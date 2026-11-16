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

import Proofs.Step1LLLDensity.StageBadPointPredicates

/-!
# Stage-3 Bad-Point Multiplicity Bounds and Local-Box Candidate Vertex Supports

Proves single-vertex update bounds of at most one bad grid parameter for Stages 3A, 3B, and 3C (`card_update_stage3ABadPts_le_one`, `card_update_stage3BBadPts_le_one`, `card_update_stage3CBadPts_le_one`). Defines local-box vertex supports (`localBoxSupport`) and sector candidate sets (`candQ`, `candZ`, `candX`), bounds their cardinalities under `HasUnitBallDensityT`, and proves `evalAssign` invariance of `lllSimplexPts` outside the active vertex sector.

## References

* Part I, Section 2.2 (`subsec:step1-lll`), Proposition 2.4 (`prop:step1-lll`), Equation (2) (`eq:archimedes-slab-bound`)
-/

noncomputable section
open scoped Classical BigOperators
namespace WeldedHierarchy

/-! ## 1. Single-Coordinate Grid Update Bounds for Stage 3A, 3B, and 3C -/

/-- Updating `ω0` at the X-check vertex of `u` satisfies `Stage3ABadPts` for at most 1 grid value `c`. -/
lemma card_update_stage3ABadPts_le_one (B : BundledCSSCode3D) (ω0 : LLLVertex B → Fin (lllGridN + 1))
    (s1 s2 s3 u : ActiveSimplex2 B.code) :
    (Finset.univ.filter (fun c : Fin (lllGridN + 1) =>
      Stage3ABadPts
        (lllSimplexPts B (Function.update ω0 (Sum.inr (Sum.inr u.val.1)) c) s1)
        (lllSimplexPts B (Function.update ω0 (Sum.inr (Sum.inr u.val.1)) c) s2)
        (lllSimplexPts B (Function.update ω0 (Sum.inr (Sum.inr u.val.1)) c) s3)
        (lllSimplexPts B (Function.update ω0 (Sum.inr (Sum.inr u.val.1)) c) u)
        (VertexDisjointSimplex2 s1.val u.val ∧ VertexDisjointSimplex2 s2.val u.val ∧ VertexDisjointSimplex2 s3.val u.val))).card ≤ 1 := by
  -- Step 1: Establish initial algebraic and geometric reductions for `card_update_stage3ABadPts_le_one`
  by_cases h_disj : VertexDisjointSimplex2 s1.val u.val ∧ VertexDisjointSimplex2 s2.val u.val ∧ VertexDisjointSimplex2 s3.val u.val
  · have hs1 : ∀ c, lllSimplexPts B (Function.update ω0 (Sum.inr (Sum.inr u.val.1)) c) s1 = lllSimplexPts B ω0 s1 :=
      fun c => lllSimplexPts_update_not_mem B ω0 s1 _ c
        (fun h => h_disj.1.1 (Sum.inr.inj (Sum.inr.inj h))) (fun h => nomatch h) (fun h => nomatch h)
    have hs2 : ∀ c, lllSimplexPts B (Function.update ω0 (Sum.inr (Sum.inr u.val.1)) c) s2 = lllSimplexPts B ω0 s2 :=
      fun c => lllSimplexPts_update_not_mem B ω0 s2 _ c
        (fun h => h_disj.2.1.1 (Sum.inr.inj (Sum.inr.inj h))) (fun h => nomatch h) (fun h => nomatch h)
    have hs3 : ∀ c, lllSimplexPts B (Function.update ω0 (Sum.inr (Sum.inr u.val.1)) c) s3 = lllSimplexPts B ω0 s3 :=
      fun c => lllSimplexPts_update_not_mem B ω0 s3 _ c
        (fun h => h_disj.2.2.1 (Sum.inr.inj (Sum.inr.inj h))) (fun h => nomatch h) (fun h => nomatch h)
    have hu : ∀ c, lllSimplexPts B (Function.update ω0 (Sum.inr (Sum.inr u.val.1)) c) u =
        (fun a => (bdlLambda : ℝ) * B.code.posX u.val.1 a + rationalCap2 (lllGridParam c) a,
         (lllSimplexPts B ω0 u).2.1, (lllSimplexPts B ω0 u).2.2) :=
      fun c => lllSimplexPts_update_X B ω0 u c
    let N1 := ptsNormal (lllSimplexPts B ω0 s1); let b1 := ptsRhs (lllSimplexPts B ω0 s1)
    let N2 := ptsNormal (lllSimplexPts B ω0 s2); let b2 := ptsRhs (lllSimplexPts B ω0 s2)
    let N3 := ptsNormal (lllSimplexPts B ω0 s3); let b3 := ptsRhs (lllSimplexPts B ω0 s3)
    let A4_0 : Point3D := fun a => (bdlLambda : ℝ) * B.code.posX u.val.1 a
    let B4 := (lllSimplexPts B ω0 u).2.1
    let C4 := (lllSimplexPts B ω0 u).2.2
    let D4 : ℝ := - det3D N1 N2 N3
    -- Step 2: Complete the main case analysis and bound assembly for `card_update_stage3ABadPts_le_one`
    let VA : Point3D := fun a =>
      b1 * cross3D N2 N3 a - b2 * cross3D N1 N3 a + b3 * cross3D N1 N2 a + D4 * B4 a
    let WA : Point3D := cross3D VA (sub3D C4 B4)
    let P : Prop :=
      (bdlLambda : ℝ) ^ 2 < |D4| ∧
      273000 * (bdlLambda : ℝ) ^ 2 * |D4| ≤ |WA 1| ∧
      |WA 0| ≤ 5 * |WA 1|
    let A4 (s : ℝ) : Point3D := fun a => A4_0 a + rationalCap2 s a
    let N4 (s : ℝ) : Point3D := cross3D (sub3D B4 (A4 s)) (sub3D C4 (A4 s))
    let b4 (s : ℝ) : ℝ := dot3D (N4 s) (A4 s)
    let K (s : ℝ) : ℝ := det3D N2 N3 (N4 s) * b1 + (- det3D N1 N3 (N4 s)) * b2 +
                         det3D N1 N2 (N4 s) * b3 + D4 * b4 s
    have h_sub : Finset.univ.filter (fun c : Fin (lllGridN + 1) =>
        Stage3ABadPts
          (lllSimplexPts B (Function.update ω0 (Sum.inr (Sum.inr u.val.1)) c) s1)
          (lllSimplexPts B (Function.update ω0 (Sum.inr (Sum.inr u.val.1)) c) s2)
          (lllSimplexPts B (Function.update ω0 (Sum.inr (Sum.inr u.val.1)) c) s3)
          (lllSimplexPts B (Function.update ω0 (Sum.inr (Sum.inr u.val.1)) c) u)
          (VertexDisjointSimplex2 s1.val u.val ∧ VertexDisjointSimplex2 s2.val u.val ∧ VertexDisjointSimplex2 s3.val u.val)) ⊆
        Finset.univ.filter (fun c : Fin (lllGridN + 1) =>
          P ∧ |K (lllGridParam c)| ≤ 7000000 * (bdlLambda : ℝ) ^ 2 * |D4|) := by
      intro c hc
      rw [Finset.mem_filter] at hc ⊢
      rcases hc with ⟨hc_mem, h_bad⟩
      rw [hs1 c, hs2 c, hs3 c, hu c] at h_bad
      exact ⟨hc_mem, h_bad.2.1, h_bad.2.2⟩
    exact le_trans (Finset.card_le_card h_sub)
      (card_filter_lllGridParam_stage3A_le_one P N1 N2 N3 A4_0 B4 C4 b1 b2 b3 id)
  · rw [Finset.card_le_one]
    intro c1 hc1; exfalso; exact h_disj (Finset.mem_filter.mp hc1).2.1

/-- Updating `ω0` at the qubit vertex of `u` satisfies `Stage3BBadPts` for at most 1 grid value `c`. -/
lemma card_update_stage3BBadPts_le_one (B : BundledCSSCode3D) (ω0 : LLLVertex B → Fin (lllGridN + 1))
    (s1 s2 s3 u : ActiveSimplex2 B.code) :
    (Finset.univ.filter (fun c : Fin (lllGridN + 1) =>
      Stage3BBadPts
        (lllSimplexPts B (Function.update ω0 (Sum.inl u.val.2.1) c) s1)
        (lllSimplexPts B (Function.update ω0 (Sum.inl u.val.2.1) c) s2)
        (lllSimplexPts B (Function.update ω0 (Sum.inl u.val.2.1) c) s3)
        (lllSimplexPts B (Function.update ω0 (Sum.inl u.val.2.1) c) u)
        (VertexDisjointSimplex2 s1.val u.val ∧ VertexDisjointSimplex2 s2.val u.val ∧ VertexDisjointSimplex2 s3.val u.val))).card ≤ 1 := by
  -- Step 1: Establish initial algebraic and geometric reductions for `card_update_stage3BBadPts_le_one`
  by_cases h_disj : VertexDisjointSimplex2 s1.val u.val ∧ VertexDisjointSimplex2 s2.val u.val ∧ VertexDisjointSimplex2 s3.val u.val
  · have hs1 : ∀ c, lllSimplexPts B (Function.update ω0 (Sum.inl u.val.2.1) c) s1 = lllSimplexPts B ω0 s1 :=
      fun c => lllSimplexPts_update_not_mem B ω0 s1 _ c
        (fun h => nomatch h) (fun h => h_disj.1.2.1 (Sum.inl.inj h)) (fun h => nomatch h)
    have hs2 : ∀ c, lllSimplexPts B (Function.update ω0 (Sum.inl u.val.2.1) c) s2 = lllSimplexPts B ω0 s2 :=
      fun c => lllSimplexPts_update_not_mem B ω0 s2 _ c
        (fun h => nomatch h) (fun h => h_disj.2.1.2.1 (Sum.inl.inj h)) (fun h => nomatch h)
    have hs3 : ∀ c, lllSimplexPts B (Function.update ω0 (Sum.inl u.val.2.1) c) s3 = lllSimplexPts B ω0 s3 :=
      fun c => lllSimplexPts_update_not_mem B ω0 s3 _ c
        (fun h => nomatch h) (fun h => h_disj.2.2.2.1 (Sum.inl.inj h)) (fun h => nomatch h)
    have hu : ∀ c, lllSimplexPts B (Function.update ω0 (Sum.inl u.val.2.1) c) u =
        ((lllSimplexPts B ω0 u).1,
         fun a => (bdlLambda : ℝ) * B.code.posQ u.val.2.1 a + rationalCap0 (lllGridParam c) a,
         (lllSimplexPts B ω0 u).2.2) :=
      fun c => lllSimplexPts_update_Q B ω0 u c
    let N1 := ptsNormal (lllSimplexPts B ω0 s1); let b1 := ptsRhs (lllSimplexPts B ω0 s1)
    let N2 := ptsNormal (lllSimplexPts B ω0 s2); let b2 := ptsRhs (lllSimplexPts B ω0 s2)
    let N3 := ptsNormal (lllSimplexPts B ω0 s3); let b3 := ptsRhs (lllSimplexPts B ω0 s3)
    let A4 := (lllSimplexPts B ω0 u).1
    let B4_0 : Point3D := fun a => (bdlLambda : ℝ) * B.code.posQ u.val.2.1 a
    let C4 := (lllSimplexPts B ω0 u).2.2
    -- Step 2: Complete the main case analysis and bound assembly for `card_update_stage3BBadPts_le_one`
    let D4 : ℝ := - det3D N1 N2 N3
    let VB : Point3D := fun a =>
      b1 * cross3D N2 N3 a - b2 * cross3D N1 N3 a + b3 * cross3D N1 N2 a + D4 * C4 a
    let WB : Point3D := cross3D VB (sub3D A4 C4)
    let P : Prop :=
      (bdlLambda : ℝ) ^ 2 < |D4| ∧
      273000 * (bdlLambda : ℝ) ^ 2 * |D4| ≤ |WB 2| ∧
      |WB 1| ≤ 5 * |WB 2|
    let B4 (s : ℝ) : Point3D := fun a => B4_0 a + rationalCap0 s a
    let N4 (s : ℝ) : Point3D := cross3D (sub3D (B4 s) A4) (sub3D C4 A4)
    let b4 (s : ℝ) : ℝ := dot3D (N4 s) A4
    let K (s : ℝ) : ℝ := det3D N2 N3 (N4 s) * b1 + (- det3D N1 N3 (N4 s)) * b2 +
                         det3D N1 N2 (N4 s) * b3 + D4 * b4 s
    have h_sub : Finset.univ.filter (fun c : Fin (lllGridN + 1) =>
        Stage3BBadPts
          (lllSimplexPts B (Function.update ω0 (Sum.inl u.val.2.1) c) s1)
          (lllSimplexPts B (Function.update ω0 (Sum.inl u.val.2.1) c) s2)
          (lllSimplexPts B (Function.update ω0 (Sum.inl u.val.2.1) c) s3)
          (lllSimplexPts B (Function.update ω0 (Sum.inl u.val.2.1) c) u)
          (VertexDisjointSimplex2 s1.val u.val ∧ VertexDisjointSimplex2 s2.val u.val ∧ VertexDisjointSimplex2 s3.val u.val)) ⊆
        Finset.univ.filter (fun c : Fin (lllGridN + 1) =>
          P ∧ |K (lllGridParam c)| ≤ 7000000 * (bdlLambda : ℝ) ^ 2 * |D4|) := by
      intro c hc
      rw [Finset.mem_filter] at hc ⊢
      rcases hc with ⟨hc_mem, h_bad⟩
      rw [hs1 c, hs2 c, hs3 c, hu c] at h_bad
      exact ⟨hc_mem, h_bad.2.1, h_bad.2.2⟩
    exact le_trans (Finset.card_le_card h_sub)
      (card_filter_lllGridParam_stage3B_le_one P N1 N2 N3 A4 B4_0 C4 b1 b2 b3 id)
  · rw [Finset.card_le_one]
    intro c1 hc1; exfalso; exact h_disj (Finset.mem_filter.mp hc1).2.1

/-! ## 2. Local-Box Support and Candidate Vertex Sets `candQ`, `candZ`, `candX` -/

/-- Updating `ω0` at the Z-check vertex of `u` satisfies `Stage3CBadPts` for at most 1 grid value `c`. -/
lemma card_update_stage3CBadPts_le_one (B : BundledCSSCode3D) (ω0 : LLLVertex B → Fin (lllGridN + 1))
    (s1 s2 s3 u : ActiveSimplex2 B.code) :
    (Finset.univ.filter (fun c : Fin (lllGridN + 1) =>
      Stage3CBadPts
        (lllSimplexPts B (Function.update ω0 (Sum.inr (Sum.inl u.val.2.2)) c) s1)
        (lllSimplexPts B (Function.update ω0 (Sum.inr (Sum.inl u.val.2.2)) c) s2)
        (lllSimplexPts B (Function.update ω0 (Sum.inr (Sum.inl u.val.2.2)) c) s3)
        (lllSimplexPts B (Function.update ω0 (Sum.inr (Sum.inl u.val.2.2)) c) u)
        (VertexDisjointSimplex2 s1.val u.val ∧ VertexDisjointSimplex2 s2.val u.val ∧ VertexDisjointSimplex2 s3.val u.val))).card ≤ 1 := by
  -- Step 1: Establish initial algebraic and geometric reductions for `card_update_stage3CBadPts_le_one`
  by_cases h_disj : VertexDisjointSimplex2 s1.val u.val ∧ VertexDisjointSimplex2 s2.val u.val ∧ VertexDisjointSimplex2 s3.val u.val
  · have hs1 : ∀ c, lllSimplexPts B (Function.update ω0 (Sum.inr (Sum.inl u.val.2.2)) c) s1 = lllSimplexPts B ω0 s1 :=
      fun c => lllSimplexPts_update_not_mem B ω0 s1 _ c
        (fun h => nomatch h) (fun h => nomatch h) (fun h => h_disj.1.2.2 (Sum.inl.inj (Sum.inr.inj h)))
    have hs2 : ∀ c, lllSimplexPts B (Function.update ω0 (Sum.inr (Sum.inl u.val.2.2)) c) s2 = lllSimplexPts B ω0 s2 :=
      fun c => lllSimplexPts_update_not_mem B ω0 s2 _ c
        (fun h => nomatch h) (fun h => nomatch h) (fun h => h_disj.2.1.2.2 (Sum.inl.inj (Sum.inr.inj h)))
    have hs3 : ∀ c, lllSimplexPts B (Function.update ω0 (Sum.inr (Sum.inl u.val.2.2)) c) s3 = lllSimplexPts B ω0 s3 :=
      fun c => lllSimplexPts_update_not_mem B ω0 s3 _ c
        (fun h => nomatch h) (fun h => nomatch h) (fun h => h_disj.2.2.2.2 (Sum.inl.inj (Sum.inr.inj h)))
    have hu : ∀ c, lllSimplexPts B (Function.update ω0 (Sum.inr (Sum.inl u.val.2.2)) c) u =
        ((lllSimplexPts B ω0 u).1, (lllSimplexPts B ω0 u).2.1,
         fun a => (bdlLambda : ℝ) * B.code.posZ u.val.2.2 a + rationalCap1 (lllGridParam c) a) :=
      fun c => lllSimplexPts_update_Z B ω0 u c
    let N1 := ptsNormal (lllSimplexPts B ω0 s1); let b1 := ptsRhs (lllSimplexPts B ω0 s1)
    let N2 := ptsNormal (lllSimplexPts B ω0 s2); let b2 := ptsRhs (lllSimplexPts B ω0 s2)
    let N3 := ptsNormal (lllSimplexPts B ω0 s3); let b3 := ptsRhs (lllSimplexPts B ω0 s3)
    let A4 := (lllSimplexPts B ω0 u).1
    let B4 := (lllSimplexPts B ω0 u).2.1
    let C4_0 : Point3D := fun a => (bdlLambda : ℝ) * B.code.posZ u.val.2.2 a
    let D4 : ℝ := - det3D N1 N2 N3
    -- Step 2: Complete the main case analysis and bound assembly for `card_update_stage3CBadPts_le_one`
    let VC : Point3D := fun a =>
      b1 * cross3D N2 N3 a - b2 * cross3D N1 N3 a + b3 * cross3D N1 N2 a + D4 * A4 a
    let WC : Point3D := cross3D VC (sub3D B4 A4)
    let P : Prop :=
      (bdlLambda : ℝ) ^ 2 < |D4| ∧
      273000 * (bdlLambda : ℝ) ^ 2 * |D4| ≤ |WC 0| ∧
      |WC 2| ≤ 5 * |WC 0|
    let C4 (s : ℝ) : Point3D := fun a => C4_0 a + rationalCap1 s a
    let N4 (s : ℝ) : Point3D := cross3D (sub3D B4 A4) (sub3D (C4 s) A4)
    let b4 (s : ℝ) : ℝ := dot3D (N4 s) A4
    let K (s : ℝ) : ℝ := det3D N2 N3 (N4 s) * b1 + (- det3D N1 N3 (N4 s)) * b2 +
                         det3D N1 N2 (N4 s) * b3 + D4 * b4 s
    have h_sub : Finset.univ.filter (fun c : Fin (lllGridN + 1) =>
        Stage3CBadPts
          (lllSimplexPts B (Function.update ω0 (Sum.inr (Sum.inl u.val.2.2)) c) s1)
          (lllSimplexPts B (Function.update ω0 (Sum.inr (Sum.inl u.val.2.2)) c) s2)
          (lllSimplexPts B (Function.update ω0 (Sum.inr (Sum.inl u.val.2.2)) c) s3)
          (lllSimplexPts B (Function.update ω0 (Sum.inr (Sum.inl u.val.2.2)) c) u)
          (VertexDisjointSimplex2 s1.val u.val ∧ VertexDisjointSimplex2 s2.val u.val ∧ VertexDisjointSimplex2 s3.val u.val)) ⊆
        Finset.univ.filter (fun c : Fin (lllGridN + 1) =>
          P ∧ |K (lllGridParam c)| ≤ 7000000 * (bdlLambda : ℝ) ^ 2 * |D4|) := by
      intro c hc
      rw [Finset.mem_filter] at hc ⊢
      rcases hc with ⟨hc_mem, h_bad⟩
      rw [hs1 c, hs2 c, hs3 c, hu c] at h_bad
      exact ⟨hc_mem, h_bad.2.1, h_bad.2.2⟩
    exact le_trans (Finset.card_le_card h_sub)
      (card_filter_lllGridParam_stage3C_le_one P N1 N2 N3 A4 B4 C4_0 b1 b2 b3 id)
  · rw [Finset.card_le_one]
    intro c1 hc1; exfalso; exact h_disj (Finset.mem_filter.mp hc1).2.1

/-- Lifting a candidate-vertex count bound `≤ K` to a simplex count bound `≤ K * D` via fiber degree `≤ D`. -/
lemma card_filter_simplex_le_mul_deg_of_cand_filter_le
    {U V : Type*} [Fintype U] [DecidableEq U] [DecidableEq V]
    {D M : ℕ} (f : U → V)
    (h_deg : ∀ v : V, (Finset.univ.filter (fun u : U => f u = v)).card ≤ D)
    (GoodCand : Finset V) (h_cand : GoodCand.card ≤ M)
    (BadU : Finset U) (h_map : ∀ u ∈ BadU, f u ∈ GoodCand) :
    BadU.card ≤ M * D := by
  have h_sub : BadU ⊆ GoodCand.biUnion (fun v => Finset.univ.filter (fun u : U => f u = v)) := by
    intro u hu
    exact Finset.mem_biUnion.mpr ⟨f u, h_map u hu, Finset.mem_filter.mpr ⟨Finset.mem_univ u, rfl⟩⟩
  calc BadU.card
    _ ≤ (GoodCand.biUnion (fun v => Finset.univ.filter (fun u : U => f u = v))).card :=
      Finset.card_le_card h_sub
    _ ≤ ∑ v ∈ GoodCand, (Finset.univ.filter (fun u : U => f u = v)).card :=
      Finset.card_biUnion_le
    _ ≤ ∑ _v ∈ GoodCand, D := Finset.sum_le_sum (fun v _ => h_deg v)
    _ = GoodCand.card * D := by simp
    _ ≤ M * D := Nat.mul_le_mul_right D h_cand

/-- Any vertex whose perturbed position lies within squared distance `4` of `p0` belongs to `InLocalBox p0`. -/
lemma inLocalBox_of_perturbed_distSq_le_four
    (p0 p : Point3D) (cap : ℝ → Point3D) (t0 t : ℝ)
    (h_small : distSq3D (cap t0) (cap t) ≤ ((1 / 5 : ℝ) * bdlLambda) ^ 2)
    (h_dist : distSq3D (fun a => (bdlLambda : ℝ) * p0 a + cap t0 a)
                       (fun a => (bdlLambda : ℝ) * p a + cap t a) ≤ 4) :
    InLocalBox p0 p := by
  have h_coord : ∀ a : Fin 3, |p a - p0 a| ≤ 1 := by
    intro a
    have h_diff_sq : (((bdlLambda : ℝ) * p0 a + cap t0 a) - ((bdlLambda : ℝ) * p a + cap t a)) ^ 2 ≤ 2 ^ 2 := by
      have h1 := distSq3D_ge_coord_sq
        (fun i => (bdlLambda : ℝ) * p0 i + cap t0 i)
        (fun i => (bdlLambda : ℝ) * p i + cap t i) a
      linarith
    have h_cap_sq : (cap t0 a - cap t a) ^ 2 ≤ ((1 / 5 : ℝ) * bdlLambda) ^ 2 := by
      have h1 := distSq3D_ge_coord_sq (cap t0) (cap t) a
      linarith
    have h_diff_abs := abs_le_of_sq_le_sq' h_diff_sq (by norm_num : (0 : ℝ) ≤ 2)
    have h_cap_abs := abs_le_of_sq_le_sq' h_cap_sq (by dsimp [bdlLambda]; positivity)
    dsimp [bdlLambda] at h_diff_abs h_cap_abs ⊢
    rw [abs_le]
    constructor <;> linarith
  have h0 := abs_le.mp (h_coord 0)
  have h1 := abs_le.mp (h_coord 1)
  have h2 := abs_le.mp (h_coord 2)
  refine ⟨abs_le.mpr ⟨by linarith, by linarith⟩,
          abs_le.mpr ⟨by linarith, by linarith⟩,
          abs_le.mpr ⟨by linarith, by linarith⟩⟩

/-! ## 3. Candidate Set Cardinality Bounds and `evalAssign` Identities -/

/-- Reflexivity of `InLocalBox p0 p0`. -/
lemma inLocalBox_self (p0 : Point3D) : InLocalBox p0 p0 := by
  refine ⟨by simp [abs_zero], by simp [abs_zero], by simp [abs_zero]⟩

/-- Finset of all LLL vertices `v` whose unperturbed position lies in `InLocalBox p0`. -/
def localBoxSupport (B : BundledCSSCode3D) (p0 : Point3D) : Finset (LLLVertex B) :=
  Finset.univ.filter (fun v : LLLVertex B => InLocalBox p0 (lllVertexPos B v))

/-- Every vertex `v` belongs to `localBoxSupport B (lllVertexPos B v)`. -/
lemma mem_localBoxSupport_self (B : BundledCSSCode3D) (v : LLLVertex B) :
    v ∈ localBoxSupport B (lllVertexPos B v) :=
  Finset.mem_filter.mpr ⟨Finset.mem_univ v, inLocalBox_self (lllVertexPos B v)⟩

/-- If `a ∈ s`, then `a ∈ s \ t.erase a`. -/
lemma mem_sdiff_erase_self {α : Type*} [DecidableEq α] {s t : Finset α} {a : α} (ha : a ∈ s) :
    a ∈ s \ t.erase a :=
  Finset.mem_sdiff.mpr ⟨ha, Finset.notMem_erase a t⟩

/-- Candidate qubit vertices in `InLocalBox p0`. -/
def candQ (B : BundledCSSCode3D) (p0 : Point3D) : Finset (LLLVertex B) :=
  (Finset.univ.filter (fun q : B.Q => InLocalBox p0 (B.code.posQ q))).map
    ⟨Sum.inl, Sum.inl_injective⟩

/-- Candidate Z-check vertices in `InLocalBox p0`. -/
def candZ (B : BundledCSSCode3D) (p0 : Point3D) : Finset (LLLVertex B) :=
  (Finset.univ.filter (fun z : B.M_Z => InLocalBox p0 (B.code.posZ z))).map
    ⟨fun z => Sum.inr (Sum.inl z), fun _ _ h => Sum.inl.inj (Sum.inr.inj h)⟩

/-- Candidate X-check vertices in `InLocalBox p0`. -/
def candX (B : BundledCSSCode3D) (p0 : Point3D) : Finset (LLLVertex B) :=
  (Finset.univ.filter (fun x : B.M_X => InLocalBox p0 (B.code.posX x))).map
    ⟨fun x => Sum.inr (Sum.inr x), fun _ _ h => Sum.inr.inj (Sum.inr.inj h)⟩

/-- `candQ B p0` is a subset of `localBoxSupport B p0`. -/
lemma candQ_subset_localBoxSupport (B : BundledCSSCode3D) (p0 : Point3D) :
    candQ B p0 ⊆ localBoxSupport B p0 := by
  intro v hv
  rcases Finset.mem_map.mp hv with ⟨q, hq, rfl⟩
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hq).2⟩

/-- `candZ B p0` is a subset of `localBoxSupport B p0`. -/
lemma candZ_subset_localBoxSupport (B : BundledCSSCode3D) (p0 : Point3D) :
    candZ B p0 ⊆ localBoxSupport B p0 := by
  intro v hv
  rcases Finset.mem_map.mp hv with ⟨z, hz, rfl⟩
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hz).2⟩

/-- `candX B p0` is a subset of `localBoxSupport B p0`. -/
lemma candX_subset_localBoxSupport (B : BundledCSSCode3D) (p0 : Point3D) :
    candX B p0 ⊆ localBoxSupport B p0 := by
  intro v hv
  rcases Finset.mem_map.mp hv with ⟨x, hx, rfl⟩
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hx).2⟩

/-- Under `HasUnitBallDensityT B`, `(candQ B p0).card ≤ 259242201 * bdlDensityTNat`. -/
lemma card_candQ_le (B : BundledCSSCode3D) (h_dens : HasUnitBallDensityT B) (p0 : Point3D) :
    (candQ B p0).card ≤ 259242201 * bdlDensityTNat := by
  rw [candQ, Finset.card_map]
  exact card_pos_in_local_box_le bdlDensityTNat B.code.posQ (fun x0 => (h_dens x0).1) p0

/-- Under `HasUnitBallDensityT B`, `(candZ B p0).card ≤ 259242201 * bdlDensityTNat`. -/
lemma card_candZ_le (B : BundledCSSCode3D) (h_dens : HasUnitBallDensityT B) (p0 : Point3D) :
    (candZ B p0).card ≤ 259242201 * bdlDensityTNat := by
  rw [candZ, Finset.card_map]
  exact card_pos_in_local_box_le bdlDensityTNat B.code.posZ (fun x0 => (h_dens x0).2.1) p0

/-- Under `HasUnitBallDensityT B`, `(candX B p0).card ≤ 259242201 * bdlDensityTNat`. -/
lemma card_candX_le (B : BundledCSSCode3D) (h_dens : HasUnitBallDensityT B) (p0 : Point3D) :
    (candX B p0).card ≤ 259242201 * bdlDensityTNat := by
  rw [candX, Finset.card_map]
  exact card_pos_in_local_box_le bdlDensityTNat B.code.posX (fun x0 => (h_dens x0).2.2) p0

/-- No qubit vertex `Sum.inl q` belongs to `candX B p0`. -/
lemma not_mem_candX_inl (B : BundledCSSCode3D) (p0 : Point3D) (q : B.Q) :
    Sum.inl q ∉ candX B p0 := by
  intro h; rcases Finset.mem_map.mp h with ⟨x, _, hx⟩; nomatch hx

/-- No Z-check vertex `Sum.inr (Sum.inl z)` belongs to `candX B p0`. -/
lemma not_mem_candX_inr_inl (B : BundledCSSCode3D) (p0 : Point3D) (z : B.M_Z) :
    Sum.inr (Sum.inl z) ∉ candX B p0 := by
  intro h; rcases Finset.mem_map.mp h with ⟨x, _, hx⟩; nomatch hx

/-- No X-check vertex `Sum.inr (Sum.inr x)` belongs to `candQ B p0`. -/
lemma not_mem_candQ_inr_inr (B : BundledCSSCode3D) (p0 : Point3D) (x : B.M_X) :
    Sum.inr (Sum.inr x) ∉ candQ B p0 := by
  intro h; rcases Finset.mem_map.mp h with ⟨q, _, hq⟩; nomatch hq

/-- No Z-check vertex `Sum.inr (Sum.inl z)` belongs to `candQ B p0`. -/
lemma not_mem_candQ_inr_inl (B : BundledCSSCode3D) (p0 : Point3D) (z : B.M_Z) :
    Sum.inr (Sum.inl z) ∉ candQ B p0 := by
  intro h; rcases Finset.mem_map.mp h with ⟨q, _, hq⟩; nomatch hq

/-- No X-check vertex `Sum.inr (Sum.inr x)` belongs to `candZ B p0`. -/
lemma not_mem_candZ_inr_inr (B : BundledCSSCode3D) (p0 : Point3D) (x : B.M_X) :
    Sum.inr (Sum.inr x) ∉ candZ B p0 := by
  intro h; rcases Finset.mem_map.mp h with ⟨z, _, hz⟩; nomatch hz

/-- No qubit vertex `Sum.inl q` belongs to `candZ B p0`. -/
lemma not_mem_candZ_inl (B : BundledCSSCode3D) (p0 : Point3D) (q : B.Q) :
    Sum.inl q ∉ candZ B p0 := by
  intro h; rcases Finset.mem_map.mp h with ⟨z, _, hz⟩; nomatch hz

/-- `lllSimplexPts` under `evalAssign` vs `Function.update` for a fixed simplex whose vertices avoid `v`. -/
lemma lllSimplexPts_evalAssign_fixed (B : BundledCSSCode3D)
    {supp cand : Finset (LLLVertex B)} (v : LLLVertex B) (ω : LLLVertex B → Fin (lllGridN + 1))
    (s : ActiveSimplex2 B.code)
    (hx : Sum.inr (Sum.inr s.val.1) ∈ supp ∧ Sum.inr (Sum.inr s.val.1) ∉ cand)
    (hq : Sum.inl s.val.2.1 ∈ supp ∧ Sum.inl s.val.2.1 ∉ cand)
    (hz : Sum.inr (Sum.inl s.val.2.2) ∈ supp ∧ Sum.inr (Sum.inl s.val.2.2) ∉ cand) :
    lllSimplexPts B (evalAssign supp cand v ω) s = lllSimplexPts B ω s :=
  lllSimplexPts_eq_of_eq B _ _ s
    (evalAssign_apply_of_mem_sdiff supp cand v ω (Finset.mem_sdiff.mpr hx))
    (evalAssign_apply_of_mem_sdiff supp cand v ω (Finset.mem_sdiff.mpr hq))
    (evalAssign_apply_of_mem_sdiff supp cand v ω (Finset.mem_sdiff.mpr hz))

/-- `lllSimplexPts` identity for `u` when evaluating `evalAssign` at its X-check vertex in `candX`. -/
lemma lllSimplexPts_evalAssign_candX (B : BundledCSSCode3D) (s1 u : ActiveSimplex2 B.code)
    {cand : Finset (LLLVertex B)} (h_sub : cand ⊆ candX B (B.code.posQ s1.val.2.1))
    (hu : SimplexInLocalBox B s1 u) (ω : LLLVertex B → Fin (lllGridN + 1)) :
    lllSimplexPts B (evalAssign (localBoxSupport B (B.code.posQ s1.val.2.1)) cand (Sum.inr (Sum.inr u.val.1)) ω) u =
      lllSimplexPts B ω u :=
  lllSimplexPts_eq_of_eq B _ _ u
    (evalAssign_apply_self _ _ _ _)
    (evalAssign_apply_of_mem_sdiff _ _ _ _ (Finset.mem_sdiff.mpr
      ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, hu.2.1⟩, fun h => not_mem_candX_inl B _ _ (h_sub h)⟩))
    (evalAssign_apply_of_mem_sdiff _ _ _ _ (Finset.mem_sdiff.mpr
      ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, hu.2.2⟩, fun h => not_mem_candX_inr_inl B _ _ (h_sub h)⟩))

/-- `lllSimplexPts` identity for `u` when evaluating `evalAssign` at its qubit vertex in `candQ`. -/
lemma lllSimplexPts_evalAssign_candQ (B : BundledCSSCode3D) (s1 u : ActiveSimplex2 B.code)
    {cand : Finset (LLLVertex B)} (h_sub : cand ⊆ candQ B (B.code.posQ s1.val.2.1))
    (hu : SimplexInLocalBox B s1 u) (ω : LLLVertex B → Fin (lllGridN + 1)) :
    lllSimplexPts B (evalAssign (localBoxSupport B (B.code.posQ s1.val.2.1)) cand (Sum.inl u.val.2.1) ω) u =
      lllSimplexPts B ω u :=
  lllSimplexPts_eq_of_eq B _ _ u
    (evalAssign_apply_of_mem_sdiff _ _ _ _ (Finset.mem_sdiff.mpr
      ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, hu.1⟩, fun h => not_mem_candQ_inr_inr B _ _ (h_sub h)⟩))
    (evalAssign_apply_self _ _ _ _)
    (evalAssign_apply_of_mem_sdiff _ _ _ _ (Finset.mem_sdiff.mpr
      ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, hu.2.2⟩, fun h => not_mem_candQ_inr_inl B _ _ (h_sub h)⟩))

/-- `lllSimplexPts` identity for `u` when evaluating `evalAssign` at its Z-check vertex in `candZ`. -/
lemma lllSimplexPts_evalAssign_candZ (B : BundledCSSCode3D) (s1 u : ActiveSimplex2 B.code)
    {cand : Finset (LLLVertex B)} (h_sub : cand ⊆ candZ B (B.code.posQ s1.val.2.1))
    (hu : SimplexInLocalBox B s1 u) (ω : LLLVertex B → Fin (lllGridN + 1)) :
    lllSimplexPts B (evalAssign (localBoxSupport B (B.code.posQ s1.val.2.1)) cand (Sum.inr (Sum.inl u.val.2.2)) ω) u =
      lllSimplexPts B ω u :=
  lllSimplexPts_eq_of_eq B _ _ u
    (evalAssign_apply_of_mem_sdiff _ _ _ _ (Finset.mem_sdiff.mpr
      ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, hu.1⟩, fun h => not_mem_candZ_inr_inr B _ _ (h_sub h)⟩))
    (evalAssign_apply_of_mem_sdiff _ _ _ _ (Finset.mem_sdiff.mpr
      ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, hu.2.1⟩, fun h => not_mem_candZ_inl B _ _ (h_sub h)⟩))
    (evalAssign_apply_self _ _ _ _)

/-- `Fintype` instance for `ActiveSimplex2 B.code`. -/
instance instFintypeActiveSimplex2 (B : BundledCSSCode3D) : Fintype (ActiveSimplex2 B.code) := by
  unfold ActiveSimplex2; infer_instance

/-- `DecidableEq` instance for `ActiveSimplex2 B.code`. -/
instance instDecidableEqActiveSimplex2 (B : BundledCSSCode3D) : DecidableEq (ActiveSimplex2 B.code) := by
  unfold ActiveSimplex2; infer_instance

end WeldedHierarchy
