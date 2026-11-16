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

import Proofs.Step1LLLDensity.NormalCrossTrichotomy

/-!
# Anisotropic Local-Box Covering Bounds and Evaluation-Assignment LLL Reduction

Defines the anisotropic local bounding-box predicate `InLocalBox`, bounds vertex counts in `InLocalBox` via unit-ball packing (`card_pos_in_local_box_le`), and proves that any perturbed 2-simplex intersecting a unit ball lies inside the local box (`simplex_inter_ball3D_implies_inLocalBox`). Introduces the masked evaluation assignment `evalAssign` and proves the conditional LLL reduction `exists_good_assignment_of_evalAssign_lll`.

## References

* Part I, Section 2.2 (`subsec:step1-lll`), Proposition 2.4 (`prop:step1-lll`)
-/

noncomputable section
open scoped Classical BigOperators
namespace WeldedHierarchy

/-! ## 1. Anisotropic Coordinate-Sum Box `InLocalBox` and Unit-Ball Covering -/

/-- **Local Coordinate-Sum Box (`InLocalBox`)**:
    Any vertex (`posX`, `posQ`, or `posZ`) of an active 2-simplex intersecting `Ball3D x0 1` lies within `±1027`
    in coordinates `0, 1` and within `±75` in the coordinate sum `p 0 + p 1 + p 2` relative to `posQ s1.val.2.1`
    of any other active 2-simplex `s1` intersecting `Ball3D x0 1`. -/
def InLocalBox (p0 p : Point3D) : Prop :=
  |p 0 - p0 0| ≤ 1027 ∧
  |p 1 - p0 1| ≤ 1027 ∧
  |(p 0 + p 1 + p 2) - (p0 0 + p0 1 + p0 2)| ≤ 44

/-- Classical decidability instance for `InLocalBox p0`. -/
instance instDecidablePredInLocalBox (p0 : Point3D) : DecidablePred (InLocalBox p0) :=
  fun p => by unfold InLocalBox; infer_instance

/-- Cauchy-Schwarz bound `|(p 0 + p 1 + p 2) - (q 0 + q 1 + q 2)| ≤ 14` when `distSq3D p q ≤ 8^2`. -/
lemma abs_sum_sub_le_fourteen_of_distSq3D_le_eight_sq (p q : Point3D) (h : distSq3D p q ≤ 8 ^ 2) :
    |(p 0 - q 0) + (p 1 - q 1) + (p 2 - q 2)| ≤ 14 := by
  have h_sq : ((p 0 - q 0) + (p 1 - q 1) + (p 2 - q 2)) ^ 2 ≤ 14 ^ 2 := by
    dsimp [distSq3D] at h
    nlinarith [sq_nonneg ((p 0 - q 0) - (p 1 - q 1)),
               sq_nonneg ((p 1 - q 1) - (p 2 - q 2)),
               sq_nonneg ((p 2 - q 2) - (p 0 - q 0))]
  exact abs_le.mpr (abs_le_of_sq_le_sq' h_sq (by norm_num))

/-- Interval bounds for a 3-point convex combination `α * x + β * y + γ * z`. -/
lemma convex3_bounds {α β γ x y z lo hi : ℝ}
    (hα : 0 ≤ α) (hβ : 0 ≤ β) (hγ : 0 ≤ γ) (hsum : α + β + γ = 1)
    (hx : lo ≤ x ∧ x ≤ hi) (hy : lo ≤ y ∧ y ≤ hi) (hz : lo ≤ z ∧ z ≤ hi) :
    lo ≤ α * x + β * y + γ * z ∧ α * x + β * y + γ * z ≤ hi := by
  constructor
  · calc lo = (α + β + γ) * lo := by rw [hsum, one_mul]
      _ = α * lo + β * lo + γ * lo := by ring
      _ ≤ α * x + β * y + γ * z := by
        linarith [mul_le_mul_of_nonneg_left hx.1 hα, mul_le_mul_of_nonneg_left hy.1 hβ, mul_le_mul_of_nonneg_left hz.1 hγ]
  · calc α * x + β * y + γ * z
      _ ≤ α * hi + β * hi + γ * hi := by
        linarith [mul_le_mul_of_nonneg_left hx.2 hα, mul_le_mul_of_nonneg_left hy.2 hβ, mul_le_mul_of_nonneg_left hz.2 hγ]
      _ = (α + β + γ) * hi := by ring
      _ = hi := by rw [hsum, one_mul]

set_option maxRecDepth 40000 in
set_option maxHeartbeats 800000 in
/-- **Skewed-Grid Unit-Ball Covering of `InLocalBox` (`card_pos_in_local_box_le`)**:
    Using inscribed cubes of side length `23 / 20` (`3 * (23 / 40)^2 = 1587 / 1600 ≤ 1`),
    `InLocalBox p0` is covered by `1789 * 1789 * 81 = 259242201` unit balls, so at most `259242201 * T`
    vertices `v : V` satisfy `InLocalBox p0 (pos0 v)`. -/
lemma card_pos_in_local_box_le {V : Type*} [Fintype V] [DecidableEq V]
    (T : ℕ) (pos0 : V → Point3D)
    (h_dens : ∀ x0 : Point3D, ((Finset.univ.filter (fun v : V => pos0 v ∈ ball3D x0 1)).card : ℝ) ≤ (T : ℝ))
    (p0 : Point3D) :
    (Finset.univ.filter (fun v : V => InLocalBox p0 (pos0 v))).card ≤ 259242201 * T := by
  -- Step 1: Establish initial algebraic and geometric reductions for `card_pos_in_local_box_le`
  let cellCenter : Fin 1789 × Fin 1789 × Fin 81 → Point3D := fun ⟨i0, i1, i2⟩ a =>
    let c0 := (23 / 20 : ℝ) * ((i0.val : ℝ) - 894 + 1 / 2)
    let c1 := (23 / 20 : ℝ) * ((i1.val : ℝ) - 894 + 1 / 2)
    let c2 := (23 / 20 : ℝ) * ((i2.val : ℝ) - 40 + 1 / 2)
    if a = 0 then p0 0 + c0
    else if a = 1 then p0 1 + c1
    else p0 2 - c0 - c1 + c2
  have h_sub : Finset.univ.filter (fun v : V => InLocalBox p0 (pos0 v)) ⊆
      (Finset.univ : Finset (Fin 1789 × Fin 1789 × Fin 81)).biUnion
        (fun idx => Finset.univ.filter (fun v : V => pos0 v ∈ ball3D (cellCenter idx) 1)) := by
    intro v hv
    rw [Finset.mem_filter] at hv
    rcases hv.2 with ⟨h0, h1, hsum⟩
    have h0_le := abs_le.mp h0
    have h1_le := abs_le.mp h1
    have hsum_le := abs_le.mp hsum
    have hd0_lo : -(894 : ℝ) ≤ (pos0 v 0 - p0 0) * (20 / 23) := by linarith
    have hd0_hi : (pos0 v 0 - p0 0) * (20 / 23) ≤ (894 : ℝ) := by linarith
    have hd1_lo : -(894 : ℝ) ≤ (pos0 v 1 - p0 1) * (20 / 23) := by linarith
    have hd1_hi : (pos0 v 1 - p0 1) * (20 / 23) ≤ (894 : ℝ) := by linarith
    obtain ⟨h0_lt, h0_abs⟩ := floor_shift_in_fin 894 ((pos0 v 0 - p0 0) * (20 / 23)) hd0_lo hd0_hi
    obtain ⟨h1_lt, h1_abs⟩ := floor_shift_in_fin 894 ((pos0 v 1 - p0 1) * (20 / 23)) hd1_lo hd1_hi
    let c0 := (23 / 20 : ℝ) * (((⌊(pos0 v 0 - p0 0) * (20 / 23) + (894 : ℝ)⌋.toNat : ℕ) : ℝ) - (894 : ℝ) + 1 / 2)
    let c1 := (23 / 20 : ℝ) * (((⌊(pos0 v 1 - p0 1) * (20 / 23) + (894 : ℝ)⌋.toNat : ℕ) : ℝ) - (894 : ℝ) + 1 / 2)
    have hc0 : -(23 / 40 : ℝ) ≤ (pos0 v 0 - p0 0) - c0 ∧ (pos0 v 0 - p0 0) - c0 ≤ 23 / 40 := by
      have := abs_le.mp h0_abs
      dsimp [c0]; constructor <;> linarith
    have hc1 : -(23 / 40 : ℝ) ≤ (pos0 v 1 - p0 1) - c1 ∧ (pos0 v 1 - p0 1) - c1 ≤ 23 / 40 := by
      have := abs_le.mp h1_abs
      dsimp [c1]; constructor <;> linarith
    let d2 := (pos0 v 2 - p0 2) + c0 + c1
    have hd2_lo : -(40 : ℝ) ≤ d2 * (20 / 23) := by dsimp [d2]; linarith
    -- Step 2: Complete the main case analysis and bound assembly for `card_pos_in_local_box_le`
    have hd2_hi : d2 * (20 / 23) ≤ (40 : ℝ) := by dsimp [d2]; linarith
    obtain ⟨h2_lt, h2_abs⟩ := floor_shift_in_fin 40 (d2 * (20 / 23)) hd2_lo hd2_hi
    let c2 := (23 / 20 : ℝ) * (((⌊d2 * (20 / 23) + (40 : ℝ)⌋.toNat : ℕ) : ℝ) - (40 : ℝ) + 1 / 2)
    have hc2 : -(23 / 40 : ℝ) ≤ d2 - c2 ∧ d2 - c2 ≤ 23 / 40 := by
      have := abs_le.mp h2_abs
      dsimp [c2]; constructor <;> linarith
    let idx : Fin 1789 × Fin 1789 × Fin 81 :=
      (⟨⌊(pos0 v 0 - p0 0) * (20 / 23) + (894 : ℝ)⌋.toNat, by omega⟩,
       ⟨⌊(pos0 v 1 - p0 1) * (20 / 23) + (894 : ℝ)⌋.toNat, by omega⟩,
       ⟨⌊d2 * (20 / 23) + (40 : ℝ)⌋.toNat, by omega⟩)
    rw [Finset.mem_biUnion]
    refine ⟨idx, Finset.mem_univ idx, Finset.mem_filter.mpr ⟨Finset.mem_univ v, ?_⟩⟩
    dsimp [ball3D, distSq3D, cellCenter, idx]
    have hs0 : (pos0 v 0 - (p0 0 + c0)) ^ 2 ≤ (23 / 40 : ℝ) ^ 2 := by nlinarith [hc0.1, hc0.2]
    have hs1 : (pos0 v 1 - (p0 1 + c1)) ^ 2 ≤ (23 / 40 : ℝ) ^ 2 := by nlinarith [hc1.1, hc1.2]
    have hs2 : (pos0 v 2 - (p0 2 - c0 - c1 + c2)) ^ 2 ≤ (23 / 40 : ℝ) ^ 2 := by
      have h_eq : pos0 v 2 - (p0 2 - c0 - c1 + c2) = d2 - c2 := by dsimp [d2]; ring
      rw [h_eq]; nlinarith [hc2.1, hc2.2]
    dsimp [c0, c1, c2] at hs0 hs1 hs2
    linarith
  calc (Finset.univ.filter (fun v : V => InLocalBox p0 (pos0 v))).card
    _ ≤ ((Finset.univ : Finset (Fin 1789 × Fin 1789 × Fin 81)).biUnion
          (fun idx => Finset.univ.filter (fun v : V => pos0 v ∈ ball3D (cellCenter idx) 1))).card :=
      Finset.card_le_card h_sub
    _ ≤ ∑ idx ∈ (Finset.univ : Finset (Fin 1789 × Fin 1789 × Fin 81)),
          (Finset.univ.filter (fun v : V => pos0 v ∈ ball3D (cellCenter idx) 1)).card :=
      Finset.card_biUnion_le
    _ ≤ ∑ _idx ∈ (Finset.univ : Finset (Fin 1789 × Fin 1789 × Fin 81)), T := by
      apply Finset.sum_le_sum
      intro idx _
      exact_mod_cast h_dens (cellCenter idx)
    _ = 259242201 * T := by
      simp [Fintype.card_prod, Fintype.card_fin]

/-! ## 2. Simplex-Ball Intersection Localization into `InLocalBox` -/

set_option maxHeartbeats 800000 in
/-- **Simplex-Ball Intersection Implies `InLocalBox` (`simplex_inter_ball3D_implies_inLocalBox`)**:
    Whenever two active 2-simplices `s1, u` intersect `Ball3D x0 1` for parameters in `[0, 1/1000]`,
    all three vertices (`posX u.val.1`, `posQ u.val.2.1`, `posZ u.val.2.2`) of `u` lie in `InLocalBox (B.code.posQ s1.val.2.1)`. -/
lemma simplex_inter_ball3D_implies_inLocalBox (B : BundledCSSCode3D) (h8 : HasInteractionRange8 B)
    (tQ : B.Q → ℝ) (tZ : B.M_Z → ℝ) (tX : B.M_X → ℝ)
    (htQ : ∀ q, 0 ≤ tQ q ∧ tQ q ≤ 1 / 1000)
    (htZ : ∀ z, 0 ≤ tZ z ∧ tZ z ≤ 1 / 1000)
    (htX : ∀ x, 0 ≤ tX x ∧ tX x ≤ 1 / 1000)
    (x0 : Point3D) (s1 u : ActiveSimplex2 B.code)
    (hs1 : (simplex2D3D
      ((bdlPerturbStep B.code bdlLambda (fun q => rationalCap0 (tQ q)) (fun z => rationalCap1 (tZ z)) (fun x => rationalCap2 (tX x))).posX s1.val.1)
      ((bdlPerturbStep B.code bdlLambda (fun q => rationalCap0 (tQ q)) (fun z => rationalCap1 (tZ z)) (fun x => rationalCap2 (tX x))).posQ s1.val.2.1)
      ((bdlPerturbStep B.code bdlLambda (fun q => rationalCap0 (tQ q)) (fun z => rationalCap1 (tZ z)) (fun x => rationalCap2 (tX x))).posZ s1.val.2.2) ∩
      ball3D x0 1).Nonempty)
    (hu : (simplex2D3D
      ((bdlPerturbStep B.code bdlLambda (fun q => rationalCap0 (tQ q)) (fun z => rationalCap1 (tZ z)) (fun x => rationalCap2 (tX x))).posX u.val.1)
      ((bdlPerturbStep B.code bdlLambda (fun q => rationalCap0 (tQ q)) (fun z => rationalCap1 (tZ z)) (fun x => rationalCap2 (tX x))).posQ u.val.2.1)
      ((bdlPerturbStep B.code bdlLambda (fun q => rationalCap0 (tQ q)) (fun z => rationalCap1 (tZ z)) (fun x => rationalCap2 (tX x))).posZ u.val.2.2) ∩
      ball3D x0 1).Nonempty) :
    InLocalBox (B.code.posQ s1.val.2.1) (B.code.posX u.val.1) ∧
    InLocalBox (B.code.posQ s1.val.2.1) (B.code.posQ u.val.2.1) ∧
    InLocalBox (B.code.posQ s1.val.2.1) (B.code.posZ u.val.2.2) := by
  -- Step 1: Establish initial algebraic and geometric reductions for `simplex_inter_ball3D_implies_inLocalBox`
  have h_posQ_close : ∀ s : ActiveSimplex2 B.code,
      (simplex2D3D
        ((bdlPerturbStep B.code bdlLambda (fun q => rationalCap0 (tQ q)) (fun z => rationalCap1 (tZ z)) (fun x => rationalCap2 (tX x))).posX s.val.1)
        ((bdlPerturbStep B.code bdlLambda (fun q => rationalCap0 (tQ q)) (fun z => rationalCap1 (tZ z)) (fun x => rationalCap2 (tX x))).posQ s.val.2.1)
        ((bdlPerturbStep B.code bdlLambda (fun q => rationalCap0 (tQ q)) (fun z => rationalCap1 (tZ z)) (fun x => rationalCap2 (tX x))).posZ s.val.2.2) ∩
        ball3D x0 1).Nonempty →
      (∀ a : Fin 3, -9 * (bdlLambda : ℝ) ≤ (x0 a - (bdlLambda : ℝ) * B.code.posQ s.val.2.1 a) ∧
        (x0 a - (bdlLambda : ℝ) * B.code.posQ s.val.2.1 a) ≤ 1009 * (bdlLambda : ℝ)) ∧
      -15 * (bdlLambda : ℝ) ≤ (x0 0 + x0 1 + x0 2) - (bdlLambda : ℝ) * (B.code.posQ s.val.2.1 0 + B.code.posQ s.val.2.1 1 + B.code.posQ s.val.2.1 2) - (capMajor + capMinor) ∧
      (x0 0 + x0 1 + x0 2) - (bdlLambda : ℝ) * (B.code.posQ s.val.2.1 0 + B.code.posQ s.val.2.1 1 + B.code.posQ s.val.2.1 2) - (capMajor + capMinor) ≤ 15 * (bdlLambda : ℝ) := by
    clear hs1 hu
    intro s ⟨p, ⟨α, β, γ, hα, hβ, hγ, hsum, hp_eq⟩, hp_ball⟩
    have hp0 := abs_le.mp (abs_coord_sub_le_one_of_mem_ball3D_one p x0 hp_ball 0)
    have hp1 := abs_le.mp (abs_coord_sub_le_one_of_mem_ball3D_one p x0 hp_ball 1)
    have hp2 := abs_le.mp (abs_coord_sub_le_one_of_mem_ball3D_one p x0 hp_ball 2)
    have hx_sum := abs_le.mp (abs_sum_sub_le_fourteen_of_distSq3D_le_eight_sq _ _ (h8.2 s.val.1 s.val.2.1 s.property.1))
    have hz_sum := abs_le.mp (abs_sum_sub_le_fourteen_of_distSq3D_le_eight_sq _ _ (h8.1 s.val.2.2 s.val.2.1 s.property.2))
    have hcQ := rcos_small_bounds (tQ s.val.2.1) (htQ s.val.2.1).1 (htQ s.val.2.1).2
    have hsQ := rsin_small_bounds (tQ s.val.2.1) (htQ s.val.2.1).1 (htQ s.val.2.1).2
    have hcZ := rcos_small_bounds (tZ s.val.2.2) (htZ s.val.2.2).1 (htZ s.val.2.2).2
    have hsZ := rsin_small_bounds (tZ s.val.2.2) (htZ s.val.2.2).1 (htZ s.val.2.2).2
    have hcX := rcos_small_bounds (tX s.val.1) (htX s.val.1).1 (htX s.val.1).2
    have hsX := rsin_small_bounds (tX s.val.1) (htX s.val.1).1 (htX s.val.1).2
    have hβ_eq : β = 1 - α - γ := by linarith [hsum]
    have h_coord : ∀ a : Fin 3, -9 * (bdlLambda : ℝ) ≤ (x0 a - (bdlLambda : ℝ) * B.code.posQ s.val.2.1 a) ∧
        (x0 a - (bdlLambda : ℝ) * B.code.posQ s.val.2.1 a) ≤ 1009 * (bdlLambda : ℝ) := by
      intro a
      have hpa := hp_eq a
      have hp_a := abs_le.mp (abs_coord_sub_le_one_of_mem_ball3D_one p x0 hp_ball a)
      have hx_a := abs_le.mp (abs_coord_sub_le_of_distSq3D_le_eight_sq _ _ (h8.2 s.val.1 s.val.2.1 s.property.1) a)
      have hz_a := abs_le.mp (abs_coord_sub_le_of_distSq3D_le_eight_sq _ _ (h8.1 s.val.2.2 s.val.2.1 s.property.2) a)
      dsimp [bdlPerturbStep] at hpa
      have h_id : p a - (bdlLambda : ℝ) * B.code.posQ s.val.2.1 a =
          (α * ((bdlLambda : ℝ) * (B.code.posX s.val.1 a - B.code.posQ s.val.2.1 a)) + β * 0 + γ * ((bdlLambda : ℝ) * (B.code.posZ s.val.2.2 a - B.code.posQ s.val.2.1 a))) +
          (α * rationalCap2 (tX s.val.1) a + β * rationalCap0 (tQ s.val.2.1) a + γ * rationalCap1 (tZ s.val.2.2) a) := by
        rw [hpa, hβ_eq]; ring
      have h_pos_b := convex3_bounds hα hβ hγ hsum
        (show -8 * (bdlLambda : ℝ) ≤ (bdlLambda : ℝ) * (B.code.posX s.val.1 a - B.code.posQ s.val.2.1 a) ∧ (bdlLambda : ℝ) * (B.code.posX s.val.1 a - B.code.posQ s.val.2.1 a) ≤ 8 * (bdlLambda : ℝ) by
          dsimp [bdlLambda]; constructor <;> linarith)
        (show -8 * (bdlLambda : ℝ) ≤ (0 : ℝ) ∧ (0 : ℝ) ≤ 8 * (bdlLambda : ℝ) by
          dsimp [bdlLambda]; constructor <;> linarith)
        (show -8 * (bdlLambda : ℝ) ≤ (bdlLambda : ℝ) * (B.code.posZ s.val.2.2 a - B.code.posQ s.val.2.1 a) ∧ (bdlLambda : ℝ) * (B.code.posZ s.val.2.2 a - B.code.posQ s.val.2.1 a) ≤ 8 * (bdlLambda : ℝ) by
          dsimp [bdlLambda]; constructor <;> linarith)
      have h_cap_b : 0 ≤ α * rationalCap2 (tX s.val.1) a + β * rationalCap0 (tQ s.val.2.1) a + γ * rationalCap1 (tZ s.val.2.2) a ∧
          α * rationalCap2 (tX s.val.1) a + β * rationalCap0 (tQ s.val.2.1) a + γ * rationalCap1 (tZ s.val.2.2) a ≤ 1000 * (bdlLambda : ℝ) := by
        fin_cases a <;> {
          dsimp [rationalCap0, rationalCap1, rationalCap2, capMajor, capMinor, bdlLambda]
          -- Step 2: Complete the main case analysis and bound assembly for `simplex_inter_ball3D_implies_inLocalBox`
          exact convex3_bounds hα hβ hγ hsum ⟨by linarith, by linarith⟩ ⟨by linarith, by linarith⟩ ⟨by linarith, by linarith⟩
        }
      dsimp [bdlLambda] at h_id h_pos_b h_cap_b ⊢
      constructor <;> linarith
    have heq0 := hp_eq 0; have heq1 := hp_eq 1; have heq2 := hp_eq 2
    dsimp [bdlPerturbStep, rationalCap0, rationalCap1, rationalCap2] at heq0 heq1 heq2
    have h_sum_id : (p 0 + p 1 + p 2) - (bdlLambda : ℝ) * (B.code.posQ s.val.2.1 0 + B.code.posQ s.val.2.1 1 + B.code.posQ s.val.2.1 2) - (capMajor + capMinor) =
        (α * ((bdlLambda : ℝ) * ((B.code.posX s.val.1 0 - B.code.posQ s.val.2.1 0) + (B.code.posX s.val.1 1 - B.code.posQ s.val.2.1 1) + (B.code.posX s.val.1 2 - B.code.posQ s.val.2.1 2))) +
         β * 0 +
         γ * ((bdlLambda : ℝ) * ((B.code.posZ s.val.2.2 0 - B.code.posQ s.val.2.1 0) + (B.code.posZ s.val.2.2 1 - B.code.posQ s.val.2.1 1) + (B.code.posZ s.val.2.2 2 - B.code.posQ s.val.2.1 2)))) +
        (α * (capMinor * (rcos (tX s.val.1) + rsin (tX s.val.1) - 1)) +
         β * (capMinor * (rcos (tQ s.val.2.1) + rsin (tQ s.val.2.1) - 1)) +
         γ * (capMinor * (rcos (tZ s.val.2.2) + rsin (tZ s.val.2.2) - 1))) := by
      rw [heq0, heq1, heq2, hβ_eq]; ring
    have h_pos_sum_b := convex3_bounds hα hβ hγ hsum
      (show -14 * (bdlLambda : ℝ) ≤ (bdlLambda : ℝ) * ((B.code.posX s.val.1 0 - B.code.posQ s.val.2.1 0) + (B.code.posX s.val.1 1 - B.code.posQ s.val.2.1 1) + (B.code.posX s.val.1 2 - B.code.posQ s.val.2.1 2)) ∧
          (bdlLambda : ℝ) * ((B.code.posX s.val.1 0 - B.code.posQ s.val.2.1 0) + (B.code.posX s.val.1 1 - B.code.posQ s.val.2.1 1) + (B.code.posX s.val.1 2 - B.code.posQ s.val.2.1 2)) ≤ 14 * (bdlLambda : ℝ) by
        dsimp [bdlLambda]; constructor <;> linarith)
      (show -14 * (bdlLambda : ℝ) ≤ (0 : ℝ) ∧ (0 : ℝ) ≤ 14 * (bdlLambda : ℝ) by
        dsimp [bdlLambda]; constructor <;> linarith)
      (show -14 * (bdlLambda : ℝ) ≤ (bdlLambda : ℝ) * ((B.code.posZ s.val.2.2 0 - B.code.posQ s.val.2.1 0) + (B.code.posZ s.val.2.2 1 - B.code.posQ s.val.2.1 1) + (B.code.posZ s.val.2.2 2 - B.code.posQ s.val.2.1 2)) ∧
          (bdlLambda : ℝ) * ((B.code.posZ s.val.2.2 0 - B.code.posQ s.val.2.1 0) + (B.code.posZ s.val.2.2 1 - B.code.posQ s.val.2.1 1) + (B.code.posZ s.val.2.2 2 - B.code.posQ s.val.2.1 2)) ≤ 14 * (bdlLambda : ℝ) by
        dsimp [bdlLambda]; constructor <;> linarith)
    -- Step 3: Conclude final cardinality and norm estimates for `simplex_inter_ball3D_implies_inLocalBox`
    have h_cap_sum_b := convex3_bounds hα hβ hγ hsum
      (show -(1 / 5) * (bdlLambda : ℝ) ≤ capMinor * (rcos (tX s.val.1) + rsin (tX s.val.1) - 1) ∧ capMinor * (rcos (tX s.val.1) + rsin (tX s.val.1) - 1) ≤ (1 / 5) * (bdlLambda : ℝ) by
        dsimp [capMinor, bdlLambda]; constructor <;> linarith)
      (show -(1 / 5) * (bdlLambda : ℝ) ≤ capMinor * (rcos (tQ s.val.2.1) + rsin (tQ s.val.2.1) - 1) ∧ capMinor * (rcos (tQ s.val.2.1) + rsin (tQ s.val.2.1) - 1) ≤ (1 / 5) * (bdlLambda : ℝ) by
        dsimp [capMinor, bdlLambda]; constructor <;> linarith)
      (show -(1 / 5) * (bdlLambda : ℝ) ≤ capMinor * (rcos (tZ s.val.2.2) + rsin (tZ s.val.2.2) - 1) ∧ capMinor * (rcos (tZ s.val.2.2) + rsin (tZ s.val.2.2) - 1) ≤ (1 / 5) * (bdlLambda : ℝ) by
        dsimp [capMinor, bdlLambda]; constructor <;> linarith)
    refine ⟨h_coord, ?_, ?_⟩ <;> {
      dsimp [bdlLambda] at h_sum_id h_pos_sum_b h_cap_sum_b ⊢
      linarith
    }
  obtain ⟨hs1_c, hs1_slo, hs1_shi⟩ := h_posQ_close s1 hs1
  obtain ⟨hu_c, hu_slo, hu_shi⟩ := h_posQ_close u hu
  have hs1_0 := hs1_c 0; have hs1_1 := hs1_c 1
  have hu_0 := hu_c 0; have hu_1 := hu_c 1
  have hux0 := abs_le.mp (abs_coord_sub_le_of_distSq3D_le_eight_sq _ _ (h8.2 u.val.1 u.val.2.1 u.property.1) 0)
  have hux1 := abs_le.mp (abs_coord_sub_le_of_distSq3D_le_eight_sq _ _ (h8.2 u.val.1 u.val.2.1 u.property.1) 1)
  have hux_sum := abs_le.mp (abs_sum_sub_le_fourteen_of_distSq3D_le_eight_sq _ _ (h8.2 u.val.1 u.val.2.1 u.property.1))
  have huz0 := abs_le.mp (abs_coord_sub_le_of_distSq3D_le_eight_sq _ _ (h8.1 u.val.2.2 u.val.2.1 u.property.2) 0)
  have huz1 := abs_le.mp (abs_coord_sub_le_of_distSq3D_le_eight_sq _ _ (h8.1 u.val.2.2 u.val.2.1 u.property.2) 1)
  have huz_sum := abs_le.mp (abs_sum_sub_le_fourteen_of_distSq3D_le_eight_sq _ _ (h8.1 u.val.2.2 u.val.2.1 u.property.2))
  dsimp [bdlLambda] at hs1_0 hs1_1 hu_0 hu_1 hs1_slo hs1_shi hu_slo hu_shi
  have hq0 : |B.code.posQ u.val.2.1 0 - B.code.posQ s1.val.2.1 0| ≤ 1018 :=
    abs_le.mpr ⟨by linarith, by linarith⟩
  have hq1 : |B.code.posQ u.val.2.1 1 - B.code.posQ s1.val.2.1 1| ≤ 1018 :=
    abs_le.mpr ⟨by linarith, by linarith⟩
  have hq_sum : |(B.code.posQ u.val.2.1 0 + B.code.posQ u.val.2.1 1 + B.code.posQ u.val.2.1 2) -
      (B.code.posQ s1.val.2.1 0 + B.code.posQ s1.val.2.1 1 + B.code.posQ s1.val.2.1 2)| ≤ 30 :=
    abs_le.mpr ⟨by linarith, by linarith⟩
  have hq0' := abs_le.mp hq0
  have hq1' := abs_le.mp hq1
  have hq_sum' := abs_le.mp hq_sum
  refine ⟨⟨abs_le.mpr ⟨by linarith, by linarith⟩, abs_le.mpr ⟨by linarith, by linarith⟩, abs_le.mpr ⟨by linarith, by linarith⟩⟩,
          ⟨abs_le.mpr ⟨by linarith, by linarith⟩, abs_le.mpr ⟨by linarith, by linarith⟩, abs_le.mpr ⟨by linarith, by linarith⟩⟩,
          ⟨abs_le.mpr ⟨by linarith, by linarith⟩, abs_le.mpr ⟨by linarith, by linarith⟩, abs_le.mpr ⟨by linarith, by linarith⟩⟩⟩

/-! ## 3. Sub-Support Assignment Extension (`evalAssign`) for Conditional LLL -/

/-- **Evaluation-Clamped Assignment (`evalAssign`)**:
    Evaluates `ω` at `x` and on `supp \ cand`, and clamps all other vertices (including `cand \ {x}` and `V \ supp`)
    to `0`. This guarantees that `badSet t x ω` is automatically cylinder-local on `supp` and independent of `cand \ {x}`
    for ANY predicate `RawBad`. -/
def evalAssign {V : Type*} [DecidableEq V] {N : ℕ}
    (supp cand : Finset V) (x : V) (ω : V → Fin (N + 1)) (w : V) : Fin (N + 1) :=
  if w = x then ω x else if w ∈ supp \ cand then ω w else 0

/-- Updating `evalAssign supp cand x c` at `x ∈ cand ∩ supp` with `c'` yields `Function.update ... x c'`. -/
lemma evalAssign_update_self {V : Type*} [DecidableEq V] {N : ℕ}
    (supp cand : Finset V) (x : V) (ω : V → Fin (N + 1)) (c : Fin (N + 1)) :
    evalAssign supp cand x (Function.update ω x c) =
      Function.update (evalAssign supp cand x ω) x c := by
  ext w
  by_cases hwx : w = x
  · subst hwx; rw [Function.update_self, evalAssign, if_pos rfl, Function.update_self]
  · rw [Function.update_of_ne hwx, evalAssign, evalAssign, if_neg hwx, if_neg hwx, Function.update_of_ne hwx]

/-- Evaluating `evalAssign supp cand x c` at `x ∈ cand` returns `c`. -/
lemma evalAssign_apply_self {V : Type*} [DecidableEq V] {N : ℕ}
    (supp cand : Finset V) (x : V) (ω : V → Fin (N + 1)) :
    evalAssign supp cand x ω x = ω x := by
  dsimp [evalAssign]; rw [if_pos rfl]

/-- Evaluating `evalAssign supp cand x c` on `v ∈ supp \ cand` returns `ω_sub ⟨v, hv⟩`. -/
lemma evalAssign_apply_of_mem_sdiff {V : Type*} [DecidableEq V] {N : ℕ}
    (supp cand : Finset V) (x : V) (ω : V → Fin (N + 1)) {w : V} (hw : w ∈ supp \ cand) :
    evalAssign supp cand x ω w = ω w := by
  dsimp [evalAssign]
  split_ifs with hwx
  · subst hwx; rfl
  · rfl

/-- Wrapper around `exists_good_assignment_of_conditional_bad_vertices_lll` phrased via `evalAssign`. -/
lemma exists_good_assignment_of_evalAssign_lll
    {T V : Type*} [Fintype T] [DecidableEq T] [Fintype V] [DecidableEq V]
    {N K L M Γ : ℕ}
    (support : T → Finset V)
    (candV : T → Finset V)
    (RawBad : T → V → (V → Fin (N + 1)) → Prop)
    [∀ t x ω, Decidable (RawBad t x ω)]
    (h_sub : ∀ t : T, candV t ⊆ support t)
    (h_cand : ∀ t : T, (candV t).card ≤ L)
    (h_fiber : ∀ (t : T) (x : V) (ω0 : V → Fin (N + 1)),
      (Finset.univ.filter (fun c : Fin (N + 1) => RawBad t x (Function.update ω0 x c))).card ≤ K)
    (h_dep : ∀ t0 : T, (Finset.univ.filter (fun t : T => ¬ Disjoint (support t0) (support t))).card ≤ Γ)
    (h_num : ((K * L) ^ (M + 1)) * (4 * (Γ + 1)) ≤ (N + 1) ^ (M + 1)) :
    ∃ ω : V → Fin (N + 1), ∀ t : T,
      ((candV t).filter (fun x : V => RawBad t x (evalAssign (support t) (candV t) x ω))).card ≤ M := by
  -- Step 1: Establish initial algebraic and geometric reductions for `exists_good_assignment_of_evalAssign_lll`
  let badSet : T → V → (V → Fin (N + 1)) → Finset (Fin (N + 1)) := fun t x ω =>
    Finset.univ.filter (fun c : Fin (N + 1) =>
      RawBad t x (evalAssign (support t) (candV t) x (Function.update ω x c)))
  have h_bad_card : ∀ (t : T) (x : V) (ω : V → Fin (N + 1)), (badSet t x ω).card ≤ K := by
    intro t x ω
    dsimp [badSet]
    simp_rw [evalAssign_update_self]
    exact h_fiber t x (evalAssign (support t) (candV t) x ω)
  have h_bad_cyl : ∀ (t : T) (x : V) (ω1 ω2 : V → Fin (N + 1)),
      (∀ v ∈ support t, ω1 v = ω2 v) → badSet t x ω1 = badSet t x ω2 := by
    intro t x ω1 ω2 h_eq
    dsimp [badSet]
    congr 1; ext c
    -- Step 2: Complete the main case analysis and bound assembly for `exists_good_assignment_of_evalAssign_lll`
    have h_ev : evalAssign (support t) (candV t) x (Function.update ω1 x c) =
        evalAssign (support t) (candV t) x (Function.update ω2 x c) := by
      ext w; dsimp [evalAssign]
      split_ifs with hwx hws
      · subst hwx; simp
      · rw [Function.update_of_ne hwx, Function.update_of_ne hwx, h_eq w (Finset.mem_sdiff.mp hws).1]
      · rfl
    rw [h_ev]
  have h_bad_indep : ∀ (t : T) (x : V), x ∈ candV t → ∀ ω1 ω2 : V → Fin (N + 1),
      (∀ v ∉ candV t, ω1 v = ω2 v) → badSet t x ω1 = badSet t x ω2 := by
    intro t x _ ω1 ω2 h_eq
    dsimp [badSet]
    congr 1; ext c
    have h_ev : evalAssign (support t) (candV t) x (Function.update ω1 x c) =
        evalAssign (support t) (candV t) x (Function.update ω2 x c) := by
      ext w; dsimp [evalAssign]
      split_ifs with hwx hws
      · subst hwx; simp
      · rw [Function.update_of_ne hwx, Function.update_of_ne hwx, h_eq w (Finset.mem_sdiff.mp hws).2]
      · rfl
    rw [h_ev]
  obtain ⟨ω, hω⟩ := exists_good_assignment_of_conditional_bad_vertices_lll
    support candV badSet h_sub h_cand h_bad_card h_bad_cyl h_bad_indep h_dep h_num
  refine ⟨ω, fun t => ?_⟩
  have h_eq_filt : (candV t).filter (fun x : V => RawBad t x (evalAssign (support t) (candV t) x ω)) =
      (candV t).filter (fun x : V => ω x ∈ badSet t x ω) := by
    ext x
    simp only [Finset.mem_filter, badSet, Finset.mem_univ, true_and, Function.update_eq_self]
  rw [h_eq_filt]
  exact hω t

end WeldedHierarchy
