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

import Proofs.Step1LLLDensity.DiscreteCapGridAndDichotomy

/-!
# Single-Point Discrete Spherical-Cap Slab Bounds Across All Six LLL Stages

Defines local-box 2-simplex containment `SimplexInLocalBox` and bounds the number of active 2-simplices anchored in a local box (`card_activeSimplex_posQ_filter_le`). Proves that at most one discrete parameter value `lllGridParam` falls inside each bad coplanarity or Cramer-determinant slab across Stages 1, 2A, 2B, 3A, 3B, and 3C (`card_filter_lllGridParam_stage1_le_one` through `card_filter_lllGridParam_stage3C_le_one`).

## References

* Part I, Section 2.2 (`subsec:step1-lll`), Proposition 2.4 (`prop:step1-lll`), Equation (2) (`eq:archimedes-slab-bound`)
-/

noncomputable section
open scoped Classical BigOperators
namespace WeldedHierarchy

/-! ## 1. Simplex Local-Box Relation and Degree Counting -/

/-- Local box relation between two active 2-simplices (`SimplexInLocalBox B s1 u`):
    all three vertices of `u` lie in `InLocalBox (B.code.posQ s1.val.2.1)`. -/
def SimplexInLocalBox (B : BundledCSSCode3D) (s1 u : ActiveSimplex2 B.code) : Prop :=
  InLocalBox (B.code.posQ s1.val.2.1) (B.code.posX u.val.1) ∧
  InLocalBox (B.code.posQ s1.val.2.1) (B.code.posQ u.val.2.1) ∧
  InLocalBox (B.code.posQ s1.val.2.1) (B.code.posZ u.val.2.2)

/-- Classical decidability instance for `SimplexInLocalBox B s1`. -/
instance instDecidableRelSimplexInLocalBox (B : BundledCSSCode3D) (s1 u : ActiveSimplex2 B.code) :
    Decidable (SimplexInLocalBox B s1 u) :=
  Classical.propDecidable (SimplexInLocalBox B s1 u)

/-- Reflexivity of `SimplexInLocalBox B s1 s1` under `HasInteractionRange8 B`. -/
lemma simplexInLocalBox_self (B : BundledCSSCode3D) (h8 : HasInteractionRange8 B)
    (s1 : ActiveSimplex2 B.code) :
    SimplexInLocalBox B s1 s1 := by
  have hx0 := abs_le.mp (abs_coord_sub_le_of_distSq3D_le_eight_sq _ _ (h8.2 s1.val.1 s1.val.2.1 s1.property.1) 0)
  have hx1 := abs_le.mp (abs_coord_sub_le_of_distSq3D_le_eight_sq _ _ (h8.2 s1.val.1 s1.val.2.1 s1.property.1) 1)
  have hx2 := abs_le.mp (abs_coord_sub_le_of_distSq3D_le_eight_sq _ _ (h8.2 s1.val.1 s1.val.2.1 s1.property.1) 2)
  have hz0 := abs_le.mp (abs_coord_sub_le_of_distSq3D_le_eight_sq _ _ (h8.1 s1.val.2.2 s1.val.2.1 s1.property.2) 0)
  have hz1 := abs_le.mp (abs_coord_sub_le_of_distSq3D_le_eight_sq _ _ (h8.1 s1.val.2.2 s1.val.2.1 s1.property.2) 1)
  have hz2 := abs_le.mp (abs_coord_sub_le_of_distSq3D_le_eight_sq _ _ (h8.1 s1.val.2.2 s1.val.2.1 s1.property.2) 2)
  refine ⟨⟨abs_le.mpr ⟨by linarith, by linarith⟩, abs_le.mpr ⟨by linarith, by linarith⟩, abs_le.mpr ⟨by linarith, by linarith⟩⟩,
          ⟨abs_le.mpr ⟨by linarith, by linarith⟩, abs_le.mpr ⟨by linarith, by linarith⟩, abs_le.mpr ⟨by linarith, by linarith⟩⟩,
          ⟨abs_le.mpr ⟨by linarith, by linarith⟩, abs_le.mpr ⟨by linarith, by linarith⟩, abs_le.mpr ⟨by linarith, by linarith⟩⟩⟩

/-- Cardinality bound `≤ D * M_q` on active 2-simplices whose qubit vertex satisfies `P`. -/
lemma card_activeSimplex_posQ_filter_le (B : BundledCSSCode3D) {D M_q : ℕ}
    (h_deg : HasBoundedSimplexDegreeD B D)
    (P : Point3D → Prop) [DecidablePred P]
    (h_card_q : (Finset.univ.filter (fun q : B.Q => P (B.code.posQ q))).card ≤ M_q) :
    (Finset.univ.filter (fun u : ActiveSimplex2 B.code => P (B.code.posQ u.val.2.1))).card ≤ D * M_q := by
  let Q_set := Finset.univ.filter (fun q : B.Q => P (B.code.posQ q))
  have h_sub : Finset.univ.filter (fun u : ActiveSimplex2 B.code => P (B.code.posQ u.val.2.1)) ⊆
      Q_set.biUnion (fun q => Finset.univ.filter (fun u : ActiveSimplex2 B.code => u.val.2.1 = q)) := by
    intro u hu
    rw [Finset.mem_filter] at hu
    rw [Finset.mem_biUnion]
    exact ⟨u.val.2.1, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hu.2⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, rfl⟩⟩
  calc (Finset.univ.filter (fun u : ActiveSimplex2 B.code => P (B.code.posQ u.val.2.1))).card
    _ ≤ (Q_set.biUnion (fun q => Finset.univ.filter (fun u : ActiveSimplex2 B.code => u.val.2.1 = q))).card :=
      Finset.card_le_card h_sub
    _ ≤ ∑ q ∈ Q_set, (Finset.univ.filter (fun u : ActiveSimplex2 B.code => u.val.2.1 = q)).card :=
      Finset.card_biUnion_le
    _ ≤ ∑ _q ∈ Q_set, D := Finset.sum_le_sum (fun q _ => h_deg.2.1 q)
    _ = Q_set.card * D := by simp
    _ ≤ M_q * D := Nat.mul_le_mul_right D h_card_q
    _ = D * M_q := Nat.mul_comm _ _

/-- Affine representation of the Stage-2 3x3 determinant in `rcos t` and `rsin t` when varying `B` along `rationalCap0`. -/
lemma stage2_det3D_B_at_t_eq_affine_rcos_rsin (N1 N2 A B0 C : Point3D) (t : ℝ) :
    let B (s : ℝ) : Point3D := fun a => B0 a + rationalCap0 s a
    let Nt (s : ℝ) : Point3D := cross3D (sub3D (B s) A) (sub3D C A)
    let W3_B : Point3D := cross3D (cross3D N1 N2) (sub3D A C)
    det3D N1 N2 (Nt t) =
      (det3D N1 N2 (Nt 0) - capMinor * W3_B 1) +
      capMinor * (W3_B 1 * rcos t + W3_B 2 * rsin t) := by
  intro B Nt W3_B
  have h_c0 : rcos 0 = 1 := by dsimp [rcos]; norm_num
  have h_s0 : rsin 0 = 0 := by dsimp [rsin]; norm_num
  dsimp [Nt, B, W3_B, det3D, dot3D, cross3D, sub3D, rationalCap0]
  rw [h_c0, h_s0]
  ring

/-- At most one grid index `i` falls into the Stage-1 cross-product slab for a given simplex pair. -/
lemma card_filter_lllGridParam_stage1_le_one
    (P : Prop) [Decidable P] (N1 A0 B2 C2 : Point3D)
    (h_imp : P →
      (900000 * (bdlLambda : ℝ) ^ 2 ≤ N1 0 ∧ N1 0 ≤ 987000 * (bdlLambda : ℝ) ^ 2) ∧
      (900000 * (bdlLambda : ℝ) ^ 2 ≤ N1 1 ∧ N1 1 ≤ 987000 * (bdlLambda : ℝ) ^ 2) ∧
      (31 * (bdlLambda : ℝ) ≤ C2 2 - B2 2 ∧ C2 2 - B2 2 ≤ 49 * (bdlLambda : ℝ))) :
    let A (s : ℝ) : Point3D := fun a => A0 a + rationalCap2 s a
    let Nt (s : ℝ) : Point3D := cross3D (sub3D B2 (A s)) (sub3D C2 (A s))
    (Finset.univ.filter (fun c : Fin (lllGridN + 1) =>
      P ∧ |(cross3D N1 (Nt (lllGridParam c))) 2| ≤ (bdlLambda : ℝ) ^ 3)).card ≤ 1 := by
  -- Step 1: Establish initial algebraic and geometric reductions for `card_filter_lllGridParam_stage1_le_one`
  intro A Nt
  let E : Point3D := sub3D C2 B2
  let w0 : ℝ := N1 0 * E 2
  let w1 : ℝ := N1 1 * E 2
  let C0 : ℝ := (cross3D N1 (Nt 0)) 2 - capMinor * w0
  let ε : ℝ := (2 * (bdlLambda : ℝ) ^ 3) / capMinor
  have h_eq : ∀ c : Fin (lllGridN + 1),
      (P ∧ |(cross3D N1 (Nt (lllGridParam c))) 2| ≤ (bdlLambda : ℝ) ^ 3) ↔
      (P ∧ |C0 + capMinor * (w0 * rcos (lllGridParam c) + w1 * rsin (lllGridParam c))| ≤ (capMinor * ε) / 2) := by
    intro c
    -- Step 2: Complete the main case analysis and bound assembly for `card_filter_lllGridParam_stage1_le_one`
    have h_aff := stage1_cross3D_at_t_eq_affine_rcos_rsin N1 A0 B2 C2 (lllGridParam c)
    change (cross3D N1 (Nt (lllGridParam c))) 2 =
      C0 + capMinor * (w0 * rcos (lllGridParam c) + w1 * rsin (lllGridParam c)) at h_aff
    have h_eps : (capMinor * ε) / 2 = (bdlLambda : ℝ) ^ 3 := by
      dsimp [ε, capMinor, bdlLambda]; norm_num
    rw [h_aff, h_eps]
  simp_rw [h_eq]
  refine card_filter_lllGridParam_cond_slab_le_one P C0 w0 w1 ε (fun hP => ?_)
  obtain ⟨hN0, hN1, hE2⟩ := h_imp hP
  have hE2' : 31 * (bdlLambda : ℝ) ≤ E 2 ∧ E 2 ≤ 49 * (bdlLambda : ℝ) := hE2
  have hw0_pos : 0 ≤ w0 := by
    dsimp [w0, bdlLambda] at hN0 hE2' ⊢; nlinarith
  have hw1_lo : 27900000 * (bdlLambda : ℝ) ^ 3 ≤ w1 := by
    dsimp [w1, bdlLambda] at hN1 hE2' ⊢; nlinarith
  have hw0_hi : w0 ≤ 48363000 * (bdlLambda : ℝ) ^ 3 := by
    dsimp [w0, bdlLambda] at hN0 hE2' ⊢; nlinarith
  rw [abs_of_nonneg hw0_pos, abs_of_nonneg (by dsimp [bdlLambda] at hw1_lo; linarith)]
  constructor
  · dsimp [bdlLambda] at hw1_lo hw0_hi ⊢; linarith
  · dsimp [ε, capMinor, bdlLambda, lllGridN] at hw1_lo ⊢; linarith

/-! ## 2. Stage-1 and Stage-2 Single-Point Grid Slab Bounds -/

/-- At most one grid index `i` falls into the Stage-2A determinant slab when varying `A0` along `rationalCap2`. -/
lemma card_filter_lllGridParam_stage2A_le_one
    (P : Prop) [Decidable P] (N1 N2 A0 B2 C2 : Point3D)
    (h_imp : P →
      let W3_A := cross3D (cross3D N1 N2) (sub3D C2 B2)
      273000 * (bdlLambda : ℝ) ^ 3 ≤ |W3_A 1| ∧ |W3_A 0| ≤ 5 * |W3_A 1|) :
    let A (s : ℝ) : Point3D := fun a => A0 a + rationalCap2 s a
    let Nt (s : ℝ) : Point3D := cross3D (sub3D B2 (A s)) (sub3D C2 (A s))
    (Finset.univ.filter (fun c : Fin (lllGridN + 1) =>
      P ∧ |- det3D N1 N2 (Nt (lllGridParam c))| ≤ (bdlLambda : ℝ) ^ 2)).card ≤ 1 := by
  intro A Nt
  let W3_A : Point3D := cross3D (cross3D N1 N2) (sub3D C2 B2)
  let C0 : ℝ := det3D N1 N2 (Nt 0) - capMinor * W3_A 0
  let ε : ℝ := (2 * (bdlLambda : ℝ) ^ 2) / capMinor
  have h_eq : ∀ c : Fin (lllGridN + 1),
      (P ∧ |- det3D N1 N2 (Nt (lllGridParam c))| ≤ (bdlLambda : ℝ) ^ 2) ↔
      (P ∧ |C0 + capMinor * (W3_A 0 * rcos (lllGridParam c) + W3_A 1 * rsin (lllGridParam c))| ≤ (capMinor * ε) / 2) := by
    intro c
    rw [abs_neg]
    have h_aff := stage2_det3D_at_t_eq_affine_rcos_rsin N1 N2 A0 B2 C2 (lllGridParam c)
    change det3D N1 N2 (Nt (lllGridParam c)) =
      C0 + capMinor * (W3_A 0 * rcos (lllGridParam c) + W3_A 1 * rsin (lllGridParam c)) at h_aff
    have h_eps : (capMinor * ε) / 2 = (bdlLambda : ℝ) ^ 2 := by
      dsimp [ε, capMinor, bdlLambda]; norm_num
    rw [h_aff, h_eps]
  simp_rw [h_eq]
  refine card_filter_lllGridParam_cond_slab_le_one P C0 (W3_A 0) (W3_A 1) ε (fun hP => ?_)
  obtain ⟨hw1, hdom⟩ := h_imp hP
  refine ⟨hdom, ?_⟩
  dsimp [ε, capMinor, bdlLambda, lllGridN] at hw1 ⊢
  linarith

/-- At most one grid index `i` falls into the Stage-2B determinant slab when varying `B0` along `rationalCap0`. -/
lemma card_filter_lllGridParam_stage2B_le_one
    (P : Prop) [Decidable P] (N1 N2 A2 B0 C2 : Point3D)
    (h_imp : P →
      let W3_B := cross3D (cross3D N1 N2) (sub3D A2 C2)
      273000 * (bdlLambda : ℝ) ^ 3 ≤ |W3_B 2| ∧ |W3_B 1| ≤ 5 * |W3_B 2|) :
    let B (s : ℝ) : Point3D := fun a => B0 a + rationalCap0 s a
    let Nt (s : ℝ) : Point3D := cross3D (sub3D (B s) A2) (sub3D C2 A2)
    (Finset.univ.filter (fun c : Fin (lllGridN + 1) =>
      P ∧ |- det3D N1 N2 (Nt (lllGridParam c))| ≤ (bdlLambda : ℝ) ^ 2)).card ≤ 1 := by
  intro B Nt
  let W3_B : Point3D := cross3D (cross3D N1 N2) (sub3D A2 C2)
  let C0 : ℝ := det3D N1 N2 (Nt 0) - capMinor * W3_B 1
  let ε : ℝ := (2 * (bdlLambda : ℝ) ^ 2) / capMinor
  have h_eq : ∀ c : Fin (lllGridN + 1),
      (P ∧ |- det3D N1 N2 (Nt (lllGridParam c))| ≤ (bdlLambda : ℝ) ^ 2) ↔
      (P ∧ |C0 + capMinor * (W3_B 1 * rcos (lllGridParam c) + W3_B 2 * rsin (lllGridParam c))| ≤ (capMinor * ε) / 2) := by
    intro c
    rw [abs_neg]
    have h_aff := stage2_det3D_B_at_t_eq_affine_rcos_rsin N1 N2 A2 B0 C2 (lllGridParam c)
    change det3D N1 N2 (Nt (lllGridParam c)) =
      C0 + capMinor * (W3_B 1 * rcos (lllGridParam c) + W3_B 2 * rsin (lllGridParam c)) at h_aff
    have h_eps : (capMinor * ε) / 2 = (bdlLambda : ℝ) ^ 2 := by
      dsimp [ε, capMinor, bdlLambda]; norm_num
    rw [h_aff, h_eps]
  simp_rw [h_eq]
  refine card_filter_lllGridParam_cond_slab_le_one P C0 (W3_B 1) (W3_B 2) ε (fun hP => ?_)
  obtain ⟨hw1, hdom⟩ := h_imp hP
  refine ⟨hdom, ?_⟩
  dsimp [ε, capMinor, bdlLambda, lllGridN] at hw1 ⊢
  linarith

/-- At most one grid index `i` falls into the Stage-3A Cramer slab when varying `A4_0` along `rationalCap2`. -/
lemma card_filter_lllGridParam_stage3A_le_one
    (P : Prop) [Decidable P] (N1 N2 N3 A4_0 B4 C4 : Point3D) (b1 b2 b3 : ℝ)
    (h_imp : P →
      let D4 : ℝ := - det3D N1 N2 N3
      let VA : Point3D := fun a =>
        b1 * cross3D N2 N3 a - b2 * cross3D N1 N3 a + b3 * cross3D N1 N2 a + D4 * B4 a
      let WA : Point3D := cross3D VA (sub3D C4 B4)
      (bdlLambda : ℝ) ^ 2 < |D4| ∧
      273000 * (bdlLambda : ℝ) ^ 2 * |D4| ≤ |WA 1| ∧
      |WA 0| ≤ 5 * |WA 1|) :
    let A4 (s : ℝ) : Point3D := fun a => A4_0 a + rationalCap2 s a
    let N4 (s : ℝ) : Point3D := cross3D (sub3D B4 (A4 s)) (sub3D C4 (A4 s))
    let b4 (s : ℝ) : ℝ := dot3D (N4 s) (A4 s)
    let D4 : ℝ := - det3D N1 N2 N3
    let K (s : ℝ) : ℝ := det3D N2 N3 (N4 s) * b1 + (- det3D N1 N3 (N4 s)) * b2 +
                         det3D N1 N2 (N4 s) * b3 + D4 * b4 s
    (Finset.univ.filter (fun c : Fin (lllGridN + 1) =>
      P ∧ |K (lllGridParam c)| ≤ 7000000 * (bdlLambda : ℝ) ^ 2 * |D4|)).card ≤ 1 := by
  -- Step 1: Establish initial algebraic and geometric reductions for `card_filter_lllGridParam_stage3A_le_one`
  intro A4 N4 b4 D4 K
  let VA : Point3D := fun a =>
    b1 * cross3D N2 N3 a - b2 * cross3D N1 N3 a + b3 * cross3D N1 N2 a + D4 * B4 a
  let WA : Point3D := cross3D VA (sub3D C4 B4)
  -- Step 2: Complete the main case analysis and bound assembly for `card_filter_lllGridParam_stage3A_le_one`
  let C0 : ℝ := K 0 - capMinor * WA 0
  let ε : ℝ := (14000000 * (bdlLambda : ℝ) ^ 2 * |D4|) / capMinor
  have h_eq : ∀ c : Fin (lllGridN + 1),
      (P ∧ |K (lllGridParam c)| ≤ 7000000 * (bdlLambda : ℝ) ^ 2 * |D4|) ↔
      (P ∧ |C0 + capMinor * (WA 0 * rcos (lllGridParam c) + WA 1 * rsin (lllGridParam c))| ≤ (capMinor * ε) / 2) := by
    intro c
    have h_aff := cramer_residual_at_t_eq_affine_rcos_rsin N1 N2 N3 A4_0 B4 C4 b1 b2 b3 (lllGridParam c)
    change K (lllGridParam c) =
      C0 + capMinor * (WA 0 * rcos (lllGridParam c) + WA 1 * rsin (lllGridParam c)) at h_aff
    have h_eps : (capMinor * ε) / 2 = 7000000 * (bdlLambda : ℝ) ^ 2 * |D4| := by
      dsimp [ε, capMinor, bdlLambda]; ring
    rw [h_aff, h_eps]
  simp_rw [h_eq]
  refine card_filter_lllGridParam_cond_slab_le_one P C0 (WA 0) (WA 1) ε (fun hP => ?_)
  obtain ⟨hD4_pos, hw1, hdom⟩ := h_imp hP
  refine ⟨hdom, ?_⟩
  have hD4_gt : (0 : ℝ) < |D4| := lt_of_le_of_lt (by positivity) hD4_pos
  change 273000 * (bdlLambda : ℝ) ^ 2 * |D4| ≤ |WA 1| at hw1
  have h_eps_eq : ε = 350140 * (bdlLambda : ℝ) * |D4| := by dsimp [ε, capMinor, bdlLambda]; ring
  rw [h_eps_eq]
  dsimp [bdlLambda, lllGridN] at hw1 ⊢
  linarith

/-! ## 3. Stage-3A, Stage-3B, and Stage-3C Single-Point Grid Slab Bounds -/

/-- At most one grid index `i` falls into the Stage-3B Cramer slab when varying `B4_0` along `rationalCap0`. -/
lemma card_filter_lllGridParam_stage3B_le_one
    (P : Prop) [Decidable P] (N1 N2 N3 A4 B4_0 C4 : Point3D) (b1 b2 b3 : ℝ)
    (h_imp : P →
      let D4 : ℝ := - det3D N1 N2 N3
      let VB : Point3D := fun a =>
        b1 * cross3D N2 N3 a - b2 * cross3D N1 N3 a + b3 * cross3D N1 N2 a + D4 * C4 a
      let WB : Point3D := cross3D VB (sub3D A4 C4)
      (bdlLambda : ℝ) ^ 2 < |D4| ∧
      273000 * (bdlLambda : ℝ) ^ 2 * |D4| ≤ |WB 2| ∧
      |WB 1| ≤ 5 * |WB 2|) :
    let B4 (s : ℝ) : Point3D := fun a => B4_0 a + rationalCap0 s a
    let N4 (s : ℝ) : Point3D := cross3D (sub3D (B4 s) A4) (sub3D C4 A4)
    let b4 (s : ℝ) : ℝ := dot3D (N4 s) A4
    let D4 : ℝ := - det3D N1 N2 N3
    let K (s : ℝ) : ℝ := det3D N2 N3 (N4 s) * b1 + (- det3D N1 N3 (N4 s)) * b2 +
                         det3D N1 N2 (N4 s) * b3 + D4 * b4 s
    (Finset.univ.filter (fun c : Fin (lllGridN + 1) =>
      P ∧ |K (lllGridParam c)| ≤ 7000000 * (bdlLambda : ℝ) ^ 2 * |D4|)).card ≤ 1 := by
  -- Step 1: Establish initial algebraic and geometric reductions for `card_filter_lllGridParam_stage3B_le_one`
  intro B4 N4 b4 D4 K
  let VB : Point3D := fun a =>
    b1 * cross3D N2 N3 a - b2 * cross3D N1 N3 a + b3 * cross3D N1 N2 a + D4 * C4 a
  let WB : Point3D := cross3D VB (sub3D A4 C4)
  -- Step 2: Complete the main case analysis and bound assembly for `card_filter_lllGridParam_stage3B_le_one`
  let C0 : ℝ := K 0 - capMinor * WB 1
  let ε : ℝ := (14000000 * (bdlLambda : ℝ) ^ 2 * |D4|) / capMinor
  have h_eq : ∀ c : Fin (lllGridN + 1),
      (P ∧ |K (lllGridParam c)| ≤ 7000000 * (bdlLambda : ℝ) ^ 2 * |D4|) ↔
      (P ∧ |C0 + capMinor * (WB 1 * rcos (lllGridParam c) + WB 2 * rsin (lllGridParam c))| ≤ (capMinor * ε) / 2) := by
    intro c
    have h_aff := cramer_residual_B_at_t_eq_affine_rcos_rsin N1 N2 N3 A4 B4_0 C4 b1 b2 b3 (lllGridParam c)
    change K (lllGridParam c) =
      C0 + capMinor * (WB 1 * rcos (lllGridParam c) + WB 2 * rsin (lllGridParam c)) at h_aff
    have h_eps : (capMinor * ε) / 2 = 7000000 * (bdlLambda : ℝ) ^ 2 * |D4| := by
      dsimp [ε, capMinor, bdlLambda]; ring
    rw [h_aff, h_eps]
  simp_rw [h_eq]
  refine card_filter_lllGridParam_cond_slab_le_one P C0 (WB 1) (WB 2) ε (fun hP => ?_)
  obtain ⟨hD4_pos, hw1, hdom⟩ := h_imp hP
  refine ⟨hdom, ?_⟩
  have hD4_gt : (0 : ℝ) < |D4| := lt_of_le_of_lt (by positivity) hD4_pos
  change 273000 * (bdlLambda : ℝ) ^ 2 * |D4| ≤ |WB 2| at hw1
  have h_eps_eq : ε = 350140 * (bdlLambda : ℝ) * |D4| := by dsimp [ε, capMinor, bdlLambda]; ring
  rw [h_eps_eq]
  dsimp [bdlLambda, lllGridN] at hw1 ⊢
  linarith

/-- At most one grid index `i` falls into the Stage-3C Cramer slab when varying `C4_0` along `rationalCap1`. -/
lemma card_filter_lllGridParam_stage3C_le_one
    (P : Prop) [Decidable P] (N1 N2 N3 A4 B4 C4_0 : Point3D) (b1 b2 b3 : ℝ)
    (h_imp : P →
      let D4 : ℝ := - det3D N1 N2 N3
      let VC : Point3D := fun a =>
        b1 * cross3D N2 N3 a - b2 * cross3D N1 N3 a + b3 * cross3D N1 N2 a + D4 * A4 a
      let WC : Point3D := cross3D VC (sub3D B4 A4)
      (bdlLambda : ℝ) ^ 2 < |D4| ∧
      273000 * (bdlLambda : ℝ) ^ 2 * |D4| ≤ |WC 0| ∧
      |WC 2| ≤ 5 * |WC 0|) :
    let C4 (s : ℝ) : Point3D := fun a => C4_0 a + rationalCap1 s a
    let N4 (s : ℝ) : Point3D := cross3D (sub3D B4 A4) (sub3D (C4 s) A4)
    let b4 (s : ℝ) : ℝ := dot3D (N4 s) A4
    let D4 : ℝ := - det3D N1 N2 N3
    let K (s : ℝ) : ℝ := det3D N2 N3 (N4 s) * b1 + (- det3D N1 N3 (N4 s)) * b2 +
                         det3D N1 N2 (N4 s) * b3 + D4 * b4 s
    (Finset.univ.filter (fun c : Fin (lllGridN + 1) =>
      P ∧ |K (lllGridParam c)| ≤ 7000000 * (bdlLambda : ℝ) ^ 2 * |D4|)).card ≤ 1 := by
  -- Step 1: Establish initial algebraic and geometric reductions for `card_filter_lllGridParam_stage3C_le_one`
  intro C4 N4 b4 D4 K
  let VC : Point3D := fun a =>
    b1 * cross3D N2 N3 a - b2 * cross3D N1 N3 a + b3 * cross3D N1 N2 a + D4 * A4 a
  let WC : Point3D := cross3D VC (sub3D B4 A4)
  -- Step 2: Complete the main case analysis and bound assembly for `card_filter_lllGridParam_stage3C_le_one`
  let C0 : ℝ := K 0 - capMinor * WC 2
  let ε : ℝ := (14000000 * (bdlLambda : ℝ) ^ 2 * |D4|) / capMinor
  have h_eq : ∀ c : Fin (lllGridN + 1),
      (P ∧ |K (lllGridParam c)| ≤ 7000000 * (bdlLambda : ℝ) ^ 2 * |D4|) ↔
      (P ∧ |C0 + capMinor * (WC 2 * rcos (lllGridParam c) + WC 0 * rsin (lllGridParam c))| ≤ (capMinor * ε) / 2) := by
    intro c
    have h_aff := cramer_residual_C_at_t_eq_affine_rcos_rsin N1 N2 N3 A4 B4 C4_0 b1 b2 b3 (lllGridParam c)
    change K (lllGridParam c) =
      C0 + capMinor * (WC 2 * rcos (lllGridParam c) + WC 0 * rsin (lllGridParam c)) at h_aff
    have h_eps : (capMinor * ε) / 2 = 7000000 * (bdlLambda : ℝ) ^ 2 * |D4| := by
      dsimp [ε, capMinor, bdlLambda]; ring
    rw [h_aff, h_eps]
  simp_rw [h_eq]
  refine card_filter_lllGridParam_cond_slab_le_one P C0 (WC 2) (WC 0) ε (fun hP => ?_)
  obtain ⟨hD4_pos, hw1, hdom⟩ := h_imp hP
  refine ⟨hdom, ?_⟩
  have hD4_gt : (0 : ℝ) < |D4| := lt_of_le_of_lt (by positivity) hD4_pos
  change 273000 * (bdlLambda : ℝ) ^ 2 * |D4| ≤ |WC 0| at hw1
  have h_eps_eq : ε = 350140 * (bdlLambda : ℝ) * |D4| := by dsimp [ε, capMinor, bdlLambda]; ring
  rw [h_eps_eq]
  dsimp [bdlLambda, lllGridN] at hw1 ⊢
  linarith

end WeldedHierarchy
