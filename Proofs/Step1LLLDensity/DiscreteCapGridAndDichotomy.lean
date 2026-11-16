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

import Proofs.Step1LLLDensity.LocalBoxCoveringAndEvalLLL

/-!
# Discrete Spherical-Cap Parameter Grid and Stage-2 Dominant Normal Dichotomy

Defines the finite spherical-cap parameter grid (`lllGridN`, `lllGridParam`) and proves pairwise coordinate separation (`capMinor_rsin_lllGridParam_sep`) and close-neighbor unit-ball packing bounds (`card_filter_ball3D_one_le_of_bounded_close_neighbors`). Establishes the Stage-2 dominant normal dichotomy (`stage2_dominant_type_dichotomy`), conditional rational-slab occupancy bounds (`card_filter_lllGridParam_cond_slab_le_one`), and double local-box vertex counts (`InLocalBoxDouble`, `card_pos_in_local_box_double_le`).

## References

* Part I, Section 2.2 (`subsec:step1-lll`), Proposition 2.4 (`prop:step1-lll`), Equation (2) (`eq:archimedes-slab-bound`)
-/

noncomputable section
open scoped Classical BigOperators
namespace WeldedHierarchy

/-! ## 1. LLL Grid Spacing and Close-Neighbor Multiplicity Bounds -/

/-- **LLL Grid Size (`lllGridN = 8.2 × 10^{21}`)** and **Grid Parameter (`lllGridParam`)**: -/
def lllGridN : ℕ := 8200000000000000000000

/-- Uniformly spaced grid parameter `lllGridParam i = i / (1000 * (lllGridN + 1)) ∈ [0, 1/1000]`. -/
def lllGridParam (i : Fin (lllGridN + 1)) : ℝ :=
  (i.val : ℝ) / (1000 * ((lllGridN : ℝ) + 1))

/-- For every grid index `i`, `0 ≤ lllGridParam i ≤ 1 / 1000`. -/
lemma lllGridParam_bounds (i : Fin (lllGridN + 1)) :
    0 ≤ lllGridParam i ∧ lllGridParam i ≤ 1 / 1000 := by
  dsimp [lllGridParam, lllGridN]
  have hi : (i.val : ℝ) ≤ 8200000000000000000000 := by exact_mod_cast Nat.le_of_lt_succ i.isLt
  have hi0 : (0 : ℝ) ≤ i.val := Nat.cast_nonneg i.val
  constructor <;> linarith

/-- Adjacent grid parameters are separated by at least `1 / (1000 * (lllGridN + 1))`. -/
lemma lllGridParam_step (i j : Fin (lllGridN + 1)) (h : j.val < i.val) :
    lllGridParam j + 1 / (1000 * ((lllGridN : ℝ) + 1)) ≤ lllGridParam i := by
  dsimp [lllGridParam, lllGridN]
  have h_nat : (j.val : ℝ) + 1 ≤ (i.val : ℝ) := by exact_mod_cast h
  linarith

/-- Distinct grid indices satisfy `(capMinor / 10)^2 < (rsin (lllGridParam i) - rsin (lllGridParam j))^2`. -/
lemma capMinor_rsin_lllGridParam_sep (i j : Fin (lllGridN + 1)) (hne : i ≠ j) :
    4 < |capMinor * rsin (lllGridParam i) - capMinor * rsin (lllGridParam j)| := by
  wlog hij : j.val < i.val generalizing i j
  · have h_lt : i.val < j.val := Nat.lt_of_le_of_ne (not_lt.mp hij) (fun h => hne (Fin.ext h))
    rw [abs_sub_comm]
    exact this j i hne.symm h_lt
  · have h_step : (1 : ℝ) / (1000 * ((lllGridN : ℝ) + 1)) ≤ lllGridParam i - lllGridParam j := by
      linarith [lllGridParam_step i j hij]
    have hb_i := lllGridParam_bounds i
    have hb_j := lllGridParam_bounds j
    have h_pos_step : (0 : ℝ) ≤ 1 / (1000 * ((lllGridN : ℝ) + 1)) := by positivity
    have h_le : lllGridParam j ≤ lllGridParam i := by linarith
    have h_rsin := rsin_sub_ge_sub_of_bounds (lllGridParam i) (lllGridParam j) hb_i.1 hb_i.2 hb_j.1 h_le
    have h_cm_pos : (0 : ℝ) < capMinor := by dsimp [capMinor, bdlLambda]; norm_num
    have h_diff_pos : 4 < capMinor * (rsin (lllGridParam i) - rsin (lllGridParam j)) := by
      have h_ge : capMinor * ((1 : ℝ) / (1000 * ((lllGridN : ℝ) + 1))) ≤
          capMinor * (rsin (lllGridParam i) - rsin (lllGridParam j)) :=
        mul_le_mul_of_nonneg_left (le_trans h_step h_rsin) (le_of_lt h_cm_pos)
      have h_num : (4 : ℝ) < capMinor * ((1 : ℝ) / (1000 * ((lllGridN : ℝ) + 1))) := by
        dsimp [capMinor, bdlLambda, lllGridN]; norm_num
      linarith
    rw [← mul_sub, abs_of_pos (by linarith)]
    exact h_diff_pos

/-- At most one grid index `c` places a perturbed vertex within squared distance `4` of a fixed target point. -/
lemma card_filter_lllGridParam_distSq_le_four_le_one
    (p_fixed p0 : Point3D) (cap : ℝ → Point3D) (a1 : Fin 3)
    (h_a1 : ∀ t : ℝ, cap t a1 = capMinor * rsin t) :
    (Finset.univ.filter (fun c : Fin (lllGridN + 1) =>
      distSq3D p_fixed (fun a => (bdlLambda : ℝ) * p0 a + cap (lllGridParam c) a) ≤ 4)).card ≤ 1 := by
  rw [Finset.card_le_one]
  intro i hi j hj
  rw [Finset.mem_filter] at hi hj
  by_contra hne
  have h_sep := capMinor_rsin_lllGridParam_sep i j hne
  have hi_sq : (p_fixed a1 - ((bdlLambda : ℝ) * p0 a1 + cap (lllGridParam i) a1)) ^ 2 ≤ 4 :=
    le_trans (distSq3D_ge_coord_sq p_fixed (fun a => (bdlLambda : ℝ) * p0 a + cap (lllGridParam i) a) a1) hi.2
  have hj_sq : (p_fixed a1 - ((bdlLambda : ℝ) * p0 a1 + cap (lllGridParam j) a1)) ^ 2 ≤ 4 :=
    le_trans (distSq3D_ge_coord_sq p_fixed (fun a => (bdlLambda : ℝ) * p0 a + cap (lllGridParam j) a) a1) hj.2
  rw [h_a1, ← sq_abs] at hi_sq hj_sq
  have hi_abs : |p_fixed a1 - ((bdlLambda : ℝ) * p0 a1 + capMinor * rsin (lllGridParam i))| ≤ 2 := by
    nlinarith [abs_nonneg (p_fixed a1 - ((bdlLambda : ℝ) * p0 a1 + capMinor * rsin (lllGridParam i)))]
  have hj_abs : |p_fixed a1 - ((bdlLambda : ℝ) * p0 a1 + capMinor * rsin (lllGridParam j))| ≤ 2 := by
    nlinarith [abs_nonneg (p_fixed a1 - ((bdlLambda : ℝ) * p0 a1 + capMinor * rsin (lllGridParam j)))]
  have h_tri := abs_sub_le
    (p_fixed a1 - ((bdlLambda : ℝ) * p0 a1 + capMinor * rsin (lllGridParam j))) 0
    (p_fixed a1 - ((bdlLambda : ℝ) * p0 a1 + capMinor * rsin (lllGridParam i)))
  rw [sub_zero, zero_sub, abs_neg] at h_tri
  have h_eq : (p_fixed a1 - ((bdlLambda : ℝ) * p0 a1 + capMinor * rsin (lllGridParam j))) -
      (p_fixed a1 - ((bdlLambda : ℝ) * p0 a1 + capMinor * rsin (lllGridParam i))) =
      capMinor * rsin (lllGridParam i) - capMinor * rsin (lllGridParam j) := by ring
  rw [h_eq] at h_tri
  linarith

/-- Unit-ball multiplicity bound `≤ 17` from pairwise vertex separation `distSq3D > 4`. -/
lemma card_filter_ball3D_one_le_of_bounded_close_neighbors {V : Type*} [Fintype V] [DecidableEq V]
    (pos : V → Point3D) (M : ℕ) (hM : M + 1 ≤ 5595)
    (h_sep : ∀ v0 : V, (Finset.univ.filter (fun v : V => v ≠ v0 ∧ distSq3D (pos v0) (pos v) ≤ 4)).card ≤ M)
    (x0 : Point3D) :
    ((Finset.univ.filter (fun v : V => pos v ∈ ball3D x0 1)).card : ℝ) ≤ bdlDensityTPrime := by
  let S := Finset.univ.filter (fun v : V => pos v ∈ ball3D x0 1)
  have h_card : S.card ≤ M + 1 := by
    by_cases hne : S.Nonempty
    · obtain ⟨v0, hv0⟩ := hne
      have h_sub : S.erase v0 ⊆ Finset.univ.filter (fun v : V => v ≠ v0 ∧ distSq3D (pos v0) (pos v) ≤ 4) := by
        intro v hv
        rw [Finset.mem_erase] at hv
        have hv0_ball := (Finset.mem_filter.mp hv0).2
        have hv_ball := (Finset.mem_filter.mp hv.2).2
        dsimp [ball3D, distSq3D] at hv0_ball hv_ball
        refine Finset.mem_filter.mpr ⟨Finset.mem_univ v, hv.1, ?_⟩
        dsimp [distSq3D]
        have h_id : (pos v0 0 - pos v 0) ^ 2 + (pos v0 1 - pos v 1) ^ 2 + (pos v0 2 - pos v 2) ^ 2 +
            ((pos v0 0 + pos v 0 - 2 * x0 0) ^ 2 + (pos v0 1 + pos v 1 - 2 * x0 1) ^ 2 + (pos v0 2 + pos v 2 - 2 * x0 2) ^ 2) =
            2 * ((pos v0 0 - x0 0) ^ 2 + (pos v0 1 - x0 1) ^ 2 + (pos v0 2 - x0 2) ^ 2) +
            2 * ((pos v 0 - x0 0) ^ 2 + (pos v 1 - x0 1) ^ 2 + (pos v 2 - x0 2) ^ 2) := by ring
        nlinarith [sq_nonneg (pos v0 0 + pos v 0 - 2 * x0 0),
                   sq_nonneg (pos v0 1 + pos v 1 - 2 * x0 1),
                   sq_nonneg (pos v0 2 + pos v 2 - 2 * x0 2)]
      have h_er := le_trans (Finset.card_le_card h_sub) (h_sep v0)
      have h_eq := Finset.card_erase_add_one hv0
      omega
    · rw [Finset.not_nonempty_iff_eq_empty.mp hne]
      simp
  have h_le : (S.card : ℝ) ≤ 5595 := by exact_mod_cast le_trans h_card hM
  dsimp [bdlDensityTPrime]; linarith

/-! ## 2. Stage-2 Dominant Vertex-Type Dichotomy and Conditional Slab Bound -/

/-- **Stage 2 Dominant Vertex Type Dichotomy (`stage2_dominant_type_dichotomy`)**:
    Whenever `(bdlLambda : ℝ) ^ 3 < |(cross3D N1 N2) 2|` and `|- det3D N1 N2 Nu| ≤ (bdlLambda : ℝ) ^ 2`,
    either `(273000 * (bdlLambda : ℝ) ^ 3 ≤ |W3_A 1| ∧ |W3_A 0| ≤ 5 * |W3_A 1|)` (Type 2A, `u.val.1 ∈ B.M_X`),
    or `(273000 * (bdlLambda : ℝ) ^ 3 ≤ |W3_B 2| ∧ |W3_B 1| ≤ 5 * |W3_B 2|)` (Type 2B, `u.val.2.1 ∈ B.Q`). -/
lemma stage2_dominant_type_dichotomy (B : BundledCSSCode3D) (h8 : HasInteractionRange8 B)
    (tQ : B.Q → ℝ) (tZ : B.M_Z → ℝ) (tX : B.M_X → ℝ)
    (htQ : ∀ q, 0 ≤ tQ q ∧ tQ q ≤ 1 / 1000)
    (htZ : ∀ z, 0 ≤ tZ z ∧ tZ z ≤ 1 / 1000)
    (htX : ∀ x, 0 ≤ tX x ∧ tX x ≤ 1 / 1000)
    (s1 s2 u : ActiveSimplex2 B.code)
    (h_s1 : let pcode := bdlPerturbStep B.code bdlLambda (fun q => rationalCap0 (tQ q)) (fun z => rationalCap1 (tZ z)) (fun x => rationalCap2 (tX x))
            let N1 := cross3D (sub3D (pcode.posQ s1.val.2.1) (pcode.posX s1.val.1)) (sub3D (pcode.posZ s1.val.2.2) (pcode.posX s1.val.1))
            let N2 := cross3D (sub3D (pcode.posQ s2.val.2.1) (pcode.posX s2.val.1)) (sub3D (pcode.posZ s2.val.2.2) (pcode.posX s2.val.1))
            (bdlLambda : ℝ) ^ 3 < |(cross3D N1 N2) 2|)
    (h_bad2 : let pcode := bdlPerturbStep B.code bdlLambda (fun q => rationalCap0 (tQ q)) (fun z => rationalCap1 (tZ z)) (fun x => rationalCap2 (tX x))
              let N1 := cross3D (sub3D (pcode.posQ s1.val.2.1) (pcode.posX s1.val.1)) (sub3D (pcode.posZ s1.val.2.2) (pcode.posX s1.val.1))
              let N2 := cross3D (sub3D (pcode.posQ s2.val.2.1) (pcode.posX s2.val.1)) (sub3D (pcode.posZ s2.val.2.2) (pcode.posX s2.val.1))
              let Nu := cross3D (sub3D (pcode.posQ u.val.2.1) (pcode.posX u.val.1)) (sub3D (pcode.posZ u.val.2.2) (pcode.posX u.val.1))
              ¬ ((bdlLambda : ℝ) ^ 2 < |- det3D N1 N2 Nu|)) :
    let pcode := bdlPerturbStep B.code bdlLambda
      (fun q => rationalCap0 (tQ q)) (fun z => rationalCap1 (tZ z)) (fun x => rationalCap2 (tX x))
    let N1 := cross3D (sub3D (pcode.posQ s1.val.2.1) (pcode.posX s1.val.1)) (sub3D (pcode.posZ s1.val.2.2) (pcode.posX s1.val.1))
    let N2 := cross3D (sub3D (pcode.posQ s2.val.2.1) (pcode.posX s2.val.1)) (sub3D (pcode.posZ s2.val.2.2) (pcode.posX s2.val.1))
    let Au := pcode.posX u.val.1
    let Bu := pcode.posQ u.val.2.1
    let Cu := pcode.posZ u.val.2.2
    let W3_A := cross3D (cross3D N1 N2) (sub3D Cu Bu)
    let W3_B := cross3D (cross3D N1 N2) (sub3D Au Cu)
    (273000 * (bdlLambda : ℝ) ^ 3 ≤ |W3_A 1| ∧ |W3_A 0| ≤ 5 * |W3_A 1|) ∨
    (273000 * (bdlLambda : ℝ) ^ 3 ≤ |W3_B 2| ∧ |W3_B 1| ≤ 5 * |W3_B 2|) := by
  -- Step 1: Establish initial algebraic and geometric reductions for `stage2_dominant_type_dichotomy`
  intro pcode N1 N2 Au Bu Cu W3_A W3_B
  let L := (bdlLambda : ℝ)
  let U := cross3D N1 N2
  let Nu := cross3D (sub3D Bu Au) (sub3D Cu Au)
  have h_sum := stage2_sensitivity_ge_of_U2_gt B h8 tQ tZ tX htQ htZ htX N1 N2 u (L ^ 3) (le_of_lt h_s1)
  obtain ⟨hCB2, hCB0, hCB1, hBA0, hBA1, hBA2⟩ :=
    perturbed_simplex_edge_bounds B h8 tQ tZ tX u (htQ _) (htZ _) (htX _)
  change (31 * L ≤ Cu 2 - Bu 2 ∧ Cu 2 - Bu 2 ≤ 49 * L) at hCB2
  change (-1008 * L ≤ Cu 0 - Bu 0 ∧ Cu 0 - Bu 0 ≤ -991 * L) at hCB0
  change (951 * L ≤ Cu 1 - Bu 1 ∧ Cu 1 - Bu 1 ≤ 968 * L) at hCB1
  change (951 * L ≤ Bu 0 - Au 0 ∧ Bu 0 - Au 0 ≤ 968 * L) at hBA0
  change (31 * L ≤ Bu 1 - Au 1 ∧ Bu 1 - Au 1 ≤ 49 * L) at hBA1
  change (-1008 * L ≤ Bu 2 - Au 2 ∧ Bu 2 - Au 2 ≤ -991 * L) at hBA2
  obtain ⟨hNu0_lo, hNu1_lo, hNu2_lo⟩ :=
    perturbed_simplex_normal_coord_ge_900000_lambda_sq B h8 tQ tZ tX u (htQ _) (htZ _) (htX _)
  change 900000 * L ^ 2 ≤ Nu 0 at hNu0_lo
  change 900000 * L ^ 2 ≤ Nu 1 at hNu1_lo
  change 900000 * L ^ 2 ≤ Nu 2 at hNu2_lo
  have hNu_hi : Nu 0 ≤ 987000 * L ^ 2 ∧ Nu 1 ≤ 987000 * L ^ 2 ∧ Nu 2 ≤ 987000 * L ^ 2 := by
    have h0_eq : Nu 0 = (Bu 1 - Au 1) * (Cu 2 - Bu 2) - (Bu 2 - Au 2) * (Cu 1 - Bu 1) := by dsimp [Nu, cross3D, sub3D]; ring
    have h1_eq : Nu 1 = (Bu 2 - Au 2) * (Cu 0 - Bu 0) - (Bu 0 - Au 0) * (Cu 2 - Bu 2) := by dsimp [Nu, cross3D, sub3D]; ring
    have h2_eq : Nu 2 = (Bu 0 - Au 0) * (Cu 1 - Bu 1) - (Bu 1 - Au 1) * (Cu 0 - Bu 0) := by dsimp [Nu, cross3D, sub3D]; ring
    -- Step 2: Complete the main case analysis and bound assembly for `stage2_dominant_type_dichotomy`
    have hL : 0 ≤ L := by dsimp [L, bdlLambda]; norm_num
    exact ⟨by rw [h0_eq]; nlinarith, by rw [h1_eq]; nlinarith, by rw [h2_eq]; nlinarith⟩
  have hEu2 : |sub3D Cu Bu 2| ≤ 49 * L := abs_le.mpr ⟨by dsimp [sub3D, L] at hCB2 ⊢; linarith, by dsimp [sub3D, L] at hCB2 ⊢; linarith⟩
  have hFu2 : |sub3D Au Cu 2| ≤ 977 * L := abs_le.mpr ⟨by dsimp [sub3D, L] at hCB2 hBA2 ⊢; linarith, by dsimp [sub3D, L] at hCB2 hBA2 ⊢; linarith⟩
  have h_either : 300000 * L ^ 2 * |L| ≤ |W3_A 1| ∨ 300000 * L ^ 2 * |L| ≤ |W3_B 1| := by
    have h_abs_L : |L| = L := abs_of_pos (by dsimp [L, bdlLambda]; norm_num)
    rw [h_abs_L]
    by_contra h_neither
    push_neg at h_neither
    have h1 : |sub3D Cu Bu 2| * |W3_B 1| ≤ (49 * L) * (300000 * L ^ 2 * L) :=
      mul_le_mul hEu2 (le_of_lt h_neither.2) (abs_nonneg _) (by dsimp [L, bdlLambda]; norm_num)
    have h2 : |sub3D Au Cu 2| * |W3_A 1| ≤ (977 * L) * (300000 * L ^ 2 * L) :=
      mul_le_mul hFu2 (le_of_lt h_neither.1) (abs_nonneg _) (by dsimp [L, bdlLambda]; norm_num)
    change 900000 * L ^ 2 * L ^ 3 ≤ |sub3D Cu Bu 2| * |W3_B 1| + |sub3D Au Cu 2| * |W3_A 1| at h_sum
    dsimp [L, bdlLambda] at h_sum h1 h2
    linarith
  have hK : |dot3D U Nu| ≤ 7000000 * L ^ 2 * |L| := by
    have h_le : |- det3D N1 N2 Nu| ≤ L ^ 2 := not_lt.mp h_bad2
    have h_det_eq : det3D N1 N2 Nu = dot3D U Nu := by dsimp [det3D, U, dot3D, cross3D]; ring
    have h_eq : |- det3D N1 N2 Nu| = |dot3D U Nu| := by rw [abs_neg, h_det_eq]
    rw [← h_eq]
    have h_abs_L : |L| = L := abs_of_pos (by dsimp [L, bdlLambda]; norm_num)
    rw [h_abs_L]
    have : L ^ 2 ≤ 7000000 * L ^ 2 * L := by dsimp [L, bdlLambda]; norm_num
    linarith
  have h_idA : Nu 1 * W3_A 0 - Nu 0 * W3_A 1 = (sub3D Cu Bu 2) * dot3D U Nu := by
    dsimp [Nu, W3_A, U, cross3D, sub3D, dot3D]; ring
  have h_idB : Nu 1 * W3_B 2 - Nu 2 * W3_B 1 = (- sub3D Au Cu 0) * dot3D U Nu := by
    dsimp [Nu, W3_B, U, cross3D, sub3D, dot3D]; ring
  have hE_A : |sub3D Cu Bu 2| ≤ 1008 * L :=
    le_trans hEu2 (by dsimp [L, bdlLambda]; norm_num)
  have hE_B : |- sub3D Au Cu 0| ≤ 1008 * L := by
    rw [abs_neg]; exact abs_le.mpr ⟨by dsimp [sub3D, L] at hCB0 hBA0 ⊢; linarith, by dsimp [sub3D, L] at hCB0 hBA0 ⊢; linarith⟩
  have h_abs_L : |L| = L := abs_of_pos (by dsimp [L, bdlLambda]; norm_num)
  rcases h_either with hWA | hWB
  · left
    have hWA_lo : 273000 * (bdlLambda : ℝ) ^ 2 * |L| ≤ |W3_A 1| := by
      rw [h_abs_L] at hWA ⊢; dsimp [L, bdlLambda] at hWA ⊢; linarith
    have hWA0 := (abs_dom_and_lower_of_normal_cross_eq
      ⟨hNu1_lo, hNu_hi.2.1⟩ ⟨hNu0_lo, hNu_hi.1⟩ hE_A hK h_idA).2 hWA_lo
    refine ⟨?_, hWA0⟩
    rw [h_abs_L] at hWA_lo
    dsimp [L] at hWA_lo
    linarith [show 273000 * (bdlLambda : ℝ) ^ 3 = 273000 * (bdlLambda : ℝ) ^ 2 * (bdlLambda : ℝ) by ring]
  · right
    have hWB_res := (abs_dom_and_lower_of_normal_cross_eq
      ⟨hNu1_lo, hNu_hi.2.1⟩ ⟨hNu2_lo, hNu_hi.2.2⟩ hE_B hK h_idB).1 hWB
    rw [h_abs_L] at hWB_res
    exact ⟨by dsimp [L] at hWB_res; linarith [hWB_res.1, show 273000 * (bdlLambda : ℝ) ^ 3 = 273000 * (bdlLambda : ℝ) ^ 2 * (bdlLambda : ℝ) by ring], hWB_res.2⟩

/-! ## 3. Double Local-Box (`InLocalBoxDouble`) Covering Bound -/

/-- Affine representation of the Cramer residual in `rcos t` and `rsin t` when varying vertex `B4` along `rationalCap0`. -/
lemma cramer_residual_B_at_t_eq_affine_rcos_rsin (N1 N2 N3 A4 B4_0 C4 : Point3D) (b1 b2 b3 t : ℝ) :
    let B4 (s : ℝ) : Point3D := fun a => B4_0 a + rationalCap0 s a
    let N4 (s : ℝ) : Point3D := cross3D (sub3D (B4 s) A4) (sub3D C4 A4)
    let b4 (s : ℝ) : ℝ := dot3D (N4 s) A4
    let D4 : ℝ := - det3D N1 N2 N3
    let K (s : ℝ) : ℝ := det3D N2 N3 (N4 s) * b1 + (- det3D N1 N3 (N4 s)) * b2 +
                         det3D N1 N2 (N4 s) * b3 + D4 * b4 s
    let VB : Point3D := fun a =>
      b1 * cross3D N2 N3 a - b2 * cross3D N1 N3 a + b3 * cross3D N1 N2 a + D4 * C4 a
    let WB : Point3D := cross3D VB (sub3D A4 C4)
    K t = (K 0 - capMinor * WB 1) + capMinor * (WB 1 * rcos t + WB 2 * rsin t) := by
  intro B4 N4 b4 D4 K VB WB
  have h_c0 : rcos 0 = 1 := by dsimp [rcos]; norm_num
  have h_s0 : rsin 0 = 0 := by dsimp [rsin]; norm_num
  dsimp [K, D4, b4, N4, B4, VB, WB, det3D, dot3D, cross3D, sub3D, rationalCap0]
  rw [h_c0, h_s0]
  ring

/-- Affine representation of the Cramer residual in `rcos t` and `rsin t` when varying vertex `C4` along `rationalCap1`. -/
lemma cramer_residual_C_at_t_eq_affine_rcos_rsin (N1 N2 N3 A4 B4 C4_0 : Point3D) (b1 b2 b3 t : ℝ) :
    let C4 (s : ℝ) : Point3D := fun a => C4_0 a + rationalCap1 s a
    let N4 (s : ℝ) : Point3D := cross3D (sub3D B4 A4) (sub3D (C4 s) A4)
    let b4 (s : ℝ) : ℝ := dot3D (N4 s) A4
    let D4 : ℝ := - det3D N1 N2 N3
    let K (s : ℝ) : ℝ := det3D N2 N3 (N4 s) * b1 + (- det3D N1 N3 (N4 s)) * b2 +
                         det3D N1 N2 (N4 s) * b3 + D4 * b4 s
    let VC : Point3D := fun a =>
      b1 * cross3D N2 N3 a - b2 * cross3D N1 N3 a + b3 * cross3D N1 N2 a + D4 * A4 a
    let WC : Point3D := cross3D VC (sub3D B4 A4)
    K t = (K 0 - capMinor * WC 2) + capMinor * (WC 2 * rcos t + WC 0 * rsin t) := by
  intro C4 N4 b4 D4 K VC WC
  have h_c0 : rcos 0 = 1 := by dsimp [rcos]; norm_num
  have h_s0 : rsin 0 = 0 := by dsimp [rsin]; norm_num
  dsimp [K, D4, b4, N4, C4, VC, WC, det3D, dot3D, cross3D, sub3D, rationalCap1]
  rw [h_c0, h_s0]
  ring

/-- Conditional 1-point grid slab bound under linear dominance `|w0| ≤ 5 * |w1|`. -/
lemma card_filter_lllGridParam_cond_slab_le_one
    (P : Prop) [Decidable P] (C0 w0 w1 ε : ℝ)
    (h_imp : P → |w0| ≤ 5 * |w1| ∧ (51 / 100) * ε < (1 / (1000 * ((lllGridN : ℝ) + 1))) * |w1|) :
    (Finset.univ.filter (fun c : Fin (lllGridN + 1) =>
      P ∧ |C0 + capMinor * (w0 * rcos (lllGridParam c) + w1 * rsin (lllGridParam c))| ≤ (capMinor * ε) / 2)).card ≤ 1 := by
  by_cases hP : P
  · obtain ⟨h_dom, hw⟩ := h_imp hP
    have h_sub : Finset.univ.filter (fun c : Fin (lllGridN + 1) =>
        P ∧ |C0 + capMinor * (w0 * rcos (lllGridParam c) + w1 * rsin (lllGridParam c))| ≤ (capMinor * ε) / 2) ⊆
      Finset.univ.filter (fun c : Fin (lllGridN + 1) =>
        |C0 + capMinor * (w0 * rcos (lllGridParam c) + w1 * rsin (lllGridParam c))| ≤ (capMinor * ε) / 2) :=
      fun c hc => Finset.mem_filter.mpr ⟨Finset.mem_univ c, (Finset.mem_filter.mp hc).2.2⟩
    exact le_trans (Finset.card_le_card h_sub)
      (card_filter_rcos_rsin_slab_le_one_of_linear_dom_tight lllGridParam
        (1 / (1000 * ((lllGridN : ℝ) + 1)))
        (by dsimp [lllGridN]; norm_num)
        lllGridParam_bounds
        lllGridParam_step
        C0 w0 w1 ε h_dom hw)
  · have h_empty : Finset.univ.filter (fun c : Fin (lllGridN + 1) =>
        P ∧ |C0 + capMinor * (w0 * rcos (lllGridParam c) + w1 * rsin (lllGridParam c))| ≤ (capMinor * ε) / 2) = ∅ := by
      rw [Finset.filter_eq_empty_iff]
      intro c _ hc; exact hP hc.1
    rw [h_empty, Finset.card_empty]
    exact Nat.zero_le 1

/-- **Doubled Local Coordinate-Sum Box (`InLocalBoxDouble`)**:
    Whenever `localBoxSupport B p0` and `localBoxSupport B p1` share a vertex `v`, the triangle inequality
    implies `InLocalBoxDouble p0 p1` (`±2054` in coordinates `0, 1` and `±150` in coordinate sum). -/
def InLocalBoxDouble (p0 p : Point3D) : Prop :=
  |p 0 - p0 0| ≤ 2054 ∧
  |p 1 - p0 1| ≤ 2054 ∧
  |(p 0 + p 1 + p 2) - (p0 0 + p0 1 + p0 2)| ≤ 88

/-- Classical decidability instance for `InLocalBoxDouble p0`. -/
instance instDecidablePredInLocalBoxDouble (p0 : Point3D) : DecidablePred (InLocalBoxDouble p0) :=
  fun p => by unfold InLocalBoxDouble; infer_instance

/-- Triangle inequality composition of two `InLocalBox` relations into `InLocalBoxDouble`. -/
lemma inLocalBoxDouble_of_inLocalBox_both (p0 p1 q : Point3D)
    (h0 : InLocalBox p0 q) (h1 : InLocalBox p1 q) :
    InLocalBoxDouble p0 p1 := by
  have h0_0 := abs_le.mp h0.1; have h0_1 := abs_le.mp h0.2.1; have h0_s := abs_le.mp h0.2.2
  have h1_0 := abs_le.mp h1.1; have h1_1 := abs_le.mp h1.2.1; have h1_s := abs_le.mp h1.2.2
  refine ⟨abs_le.mpr ⟨by linarith, by linarith⟩,
          abs_le.mpr ⟨by linarith, by linarith⟩,
          abs_le.mpr ⟨by linarith, by linarith⟩⟩

/-- Every `InLocalBoxDouble p0` (`±2054, ±2054, ±88`) is covered by `2 × 2 × 2 = 8` shifted copies
    of `InLocalBox` (`±1027, ±1027, ±44`), so it contains at most `8 * (259242201 * T)` vertices. -/
lemma card_pos_in_local_box_double_le {V : Type*} [Fintype V] [DecidableEq V]
    (T : ℕ) (pos0 : V → Point3D)
    (h_dens : ∀ x0 : Point3D, ((Finset.univ.filter (fun v : V => pos0 v ∈ ball3D x0 1)).card : ℝ) ≤ (T : ℝ))
    (p0 : Point3D) :
    (Finset.univ.filter (fun v : V => InLocalBoxDouble p0 (pos0 v))).card ≤ 8 * (259242201 * T) := by
  -- Step 1: Establish initial algebraic and geometric reductions for `card_pos_in_local_box_double_le`
  let shiftCenter : Fin 2 × Fin 2 × Fin 2 → Point3D := fun ⟨i0, i1, i2⟩ a =>
    let d0 : ℝ := if i0.val = 0 then -1027 else 1027
    let d1 : ℝ := if i1.val = 0 then -1027 else 1027
    let ds : ℝ := if i2.val = 0 then -44 else 44
    if a = 0 then p0 0 + d0
    else if a = 1 then p0 1 + d1
    else p0 2 - d0 - d1 + ds
  have h_sub : Finset.univ.filter (fun v : V => InLocalBoxDouble p0 (pos0 v)) ⊆
      (Finset.univ : Finset (Fin 2 × Fin 2 × Fin 2)).biUnion
        (fun idx => Finset.univ.filter (fun v : V => InLocalBox (shiftCenter idx) (pos0 v))) := by
    intro v hv
    rw [Finset.mem_filter] at hv
    have h0 := abs_le.mp hv.2.1
    have h1 := abs_le.mp hv.2.2.1
    have hs := abs_le.mp hv.2.2.2
    let i0 : Fin 2 := if pos0 v 0 - p0 0 ≤ 0 then ⟨0, by decide⟩ else ⟨1, by decide⟩
    let i1 : Fin 2 := if pos0 v 1 - p0 1 ≤ 0 then ⟨0, by decide⟩ else ⟨1, by decide⟩
    let i2 : Fin 2 := if (pos0 v 0 + pos0 v 1 + pos0 v 2) - (p0 0 + p0 1 + p0 2) ≤ 0 then ⟨0, by decide⟩ else ⟨1, by decide⟩
    rw [Finset.mem_biUnion]
    refine ⟨(i0, i1, i2), Finset.mem_univ _, Finset.mem_filter.mpr ⟨Finset.mem_univ v, ?_⟩⟩
    -- Step 2: Complete the main case analysis and bound assembly for `card_pos_in_local_box_double_le`
    have hc0 : |pos0 v 0 - shiftCenter (i0, i1, i2) 0| ≤ 1027 := by
      dsimp [shiftCenter, i0]
      split_ifs <;> { simp_all; try { rw [abs_le]; constructor <;> linarith } }
    have hc1 : |pos0 v 1 - shiftCenter (i0, i1, i2) 1| ≤ 1027 := by
      dsimp [shiftCenter, i1]
      split_ifs <;> { simp_all; try { rw [abs_le]; constructor <;> linarith } }
    have hcs : |(pos0 v 0 + pos0 v 1 + pos0 v 2) -
        (shiftCenter (i0, i1, i2) 0 + shiftCenter (i0, i1, i2) 1 + shiftCenter (i0, i1, i2) 2)| ≤ 44 := by
      have h_sum_eq : shiftCenter (i0, i1, i2) 0 + shiftCenter (i0, i1, i2) 1 + shiftCenter (i0, i1, i2) 2 =
          (p0 0 + p0 1 + p0 2) + (if i2.val = 0 then -44 else 44) := by
        dsimp [shiftCenter]; ring
      rw [h_sum_eq]
      dsimp [i2]
      split_ifs <;> { simp_all; try { rw [abs_le]; constructor <;> linarith } }
    exact ⟨hc0, hc1, hcs⟩
  calc (Finset.univ.filter (fun v : V => InLocalBoxDouble p0 (pos0 v))).card
    _ ≤ ((Finset.univ : Finset (Fin 2 × Fin 2 × Fin 2)).biUnion
          (fun idx => Finset.univ.filter (fun v : V => InLocalBox (shiftCenter idx) (pos0 v)))).card :=
      Finset.card_le_card h_sub
    _ ≤ ∑ idx ∈ (Finset.univ : Finset (Fin 2 × Fin 2 × Fin 2)),
          (Finset.univ.filter (fun v : V => InLocalBox (shiftCenter idx) (pos0 v))).card :=
      Finset.card_biUnion_le
    _ ≤ ∑ _idx ∈ (Finset.univ : Finset (Fin 2 × Fin 2 × Fin 2)), (259242201 * T) :=
      Finset.sum_le_sum (fun idx _ => card_pos_in_local_box_le T pos0 h_dens (shiftCenter idx))
    _ = 8 * (259242201 * T) := by simp [Fintype.card_prod, Fintype.card_fin]

end WeldedHierarchy
