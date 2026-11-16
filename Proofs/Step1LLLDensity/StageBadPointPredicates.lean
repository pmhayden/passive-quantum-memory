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

import Proofs.Step1LLLDensity.DiscreteCapSlabPointBounds

/-!
# Discrete Perturbed Simplices and Stage-1/Stage-2 Bad-Point Multiplicity Bounds

Defines the combined vertex type `LLLVertex`, the discretely perturbed CSS code `lllPCode`, perturbed 2-simplex vertex triples `lllSimplexPts`, and the six bad-configuration predicates (`Stage1BadPts`, `Stage2ABadPts`, `Stage2BBadPts`, `Stage3ABadPts`, `Stage3BBadPts`, `Stage3CBadPts`). Proves that single-vertex coordinate updates hit at most one bad grid parameter in Stages 1, 2A, and 2B (`card_update_stage1BadPts_le_one`, `card_update_stage2ABadPts_le_one`, `card_update_stage2BBadPts_le_one`).

## References

* Part I, Section 2.2 (`subsec:step1-lll`), Proposition 2.4 (`prop:step1-lll`), Equation (2) (`eq:archimedes-slab-bound`)
-/

noncomputable section
open scoped Classical BigOperators
namespace WeldedHierarchy

/-! ## 1. LLL Vertex Type, Perturbed Simplex Point Triples, and Bad Point Predicates -/

/-- Disjoint sum type `B.Q ⊕ (B.M_Z ⊕ B.M_X)` indexing all random perturbation variables of `B`. -/
abbrev LLLVertex (B : BundledCSSCode3D) : Type := B.Q ⊕ (B.M_Z ⊕ B.M_X)

/-- Unperturbed 3D Euclidean position of a vertex `v : LLLVertex B`. -/
def lllVertexPos (B : BundledCSSCode3D) : LLLVertex B → Point3D
  | Sum.inl q => B.code.posQ q
  | Sum.inr (Sum.inl z) => B.code.posZ z
  | Sum.inr (Sum.inr x) => B.code.posX x

/-- Real perturbation parameter `tQ q = lllGridParam (ω (Sum.inl q))` for qubit `q`. -/
def lllTQ (B : BundledCSSCode3D) (ω : LLLVertex B → Fin (lllGridN + 1)) (q : B.Q) : ℝ :=
  lllGridParam (ω (Sum.inl q))

/-- Real perturbation parameter `tZ z = lllGridParam (ω (Sum.inr (Sum.inl z)))` for Z-check `z`. -/
def lllTZ (B : BundledCSSCode3D) (ω : LLLVertex B → Fin (lllGridN + 1)) (z : B.M_Z) : ℝ :=
  lllGridParam (ω (Sum.inr (Sum.inl z)))

/-- Real perturbation parameter `tX x = lllGridParam (ω (Sum.inr (Sum.inr x)))` for X-check `x`. -/
def lllTX (B : BundledCSSCode3D) (ω : LLLVertex B → Fin (lllGridN + 1)) (x : B.M_X) : ℝ :=
  lllGridParam (ω (Sum.inr (Sum.inr x)))

/-- Perturbed CSS code `bdlPerturbStep B.code bdlLambda (lllTQ B ω) (lllTZ B ω) (lllTX B ω)` for grid assignment `ω`. -/
def lllPCode (B : BundledCSSCode3D) (ω : LLLVertex B → Fin (lllGridN + 1)) :
    CSSCode3D B.Q B.M_Z B.M_X :=
  bdlPerturbStep B.code bdlLambda
    (fun q => rationalCap0 (lllTQ B ω q))
    (fun z => rationalCap1 (lllTZ B ω z))
    (fun x => rationalCap2 (lllTX B ω x))

/-- Perturbed vertex triple `(posX, posQ, posZ)` of an active 2-simplex `s` under grid assignment `ω`. -/
def lllSimplexPts (B : BundledCSSCode3D) (ω : LLLVertex B → Fin (lllGridN + 1))
    (s : ActiveSimplex2 B.code) : Point3D × Point3D × Point3D :=
  let pcode := lllPCode B ω
  (pcode.posX s.val.1, pcode.posQ s.val.2.1, pcode.posZ s.val.2.2)

/-- `lllSimplexPts B ω s` depends only on the values of `ω` at the three vertices of `s`. -/
lemma lllSimplexPts_eq_of_eq (B : BundledCSSCode3D) (ω1 ω2 : LLLVertex B → Fin (lllGridN + 1))
    (s : ActiveSimplex2 B.code)
    (hx : ω1 (Sum.inr (Sum.inr s.val.1)) = ω2 (Sum.inr (Sum.inr s.val.1)))
    (hq : ω1 (Sum.inl s.val.2.1) = ω2 (Sum.inl s.val.2.1))
    (hz : ω1 (Sum.inr (Sum.inl s.val.2.2)) = ω2 (Sum.inr (Sum.inl s.val.2.2))) :
    lllSimplexPts B ω1 s = lllSimplexPts B ω2 s := by
  dsimp [lllSimplexPts, lllPCode, bdlPerturbStep, lllTQ, lllTZ, lllTX]
  rw [hx, hq, hz]

/-- Normal vector `cross3D (B - A) (C - B)` of a 3D point triple `pts = (A, B, C)`. -/
def ptsNormal (pts : Point3D × Point3D × Point3D) : Point3D :=
  cross3D (sub3D pts.2.1 pts.1) (sub3D pts.2.2 pts.1)

/-- Plane right-hand side `dot3D (ptsNormal pts) A` of a 3D point triple `pts = (A, B, C)`. -/
def ptsRhs (pts : Point3D × Point3D × Point3D) : ℝ :=
  dot3D (ptsNormal pts) pts.1

/-- Stage-1 bad point-triple predicate: bounded normal and edge vectors with small cross-product coordinate 2. -/
def Stage1BadPts (pts1 ptsU : Point3D × Point3D × Point3D) (disj : Prop) : Prop :=
  let N1 := ptsNormal pts1
  let Nu := ptsNormal ptsU
  let B2 := ptsU.2.1
  let C2 := ptsU.2.2
  disj ∧
  ((900000 * (bdlLambda : ℝ) ^ 2 ≤ N1 0 ∧ N1 0 ≤ 987000 * (bdlLambda : ℝ) ^ 2) ∧
   (900000 * (bdlLambda : ℝ) ^ 2 ≤ N1 1 ∧ N1 1 ≤ 987000 * (bdlLambda : ℝ) ^ 2) ∧
   (31 * (bdlLambda : ℝ) ≤ C2 2 - B2 2 ∧ C2 2 - B2 2 ≤ 49 * (bdlLambda : ℝ))) ∧
  |(cross3D N1 Nu) 2| ≤ (bdlLambda : ℝ) ^ 3

/-- Stage-2A bad point-triple predicate: dominant cross-product coordinate 2 and small 3x3 determinant. -/
def Stage2ABadPts (pts1 pts2 ptsU : Point3D × Point3D × Point3D) (disj : Prop) : Prop :=
  let N1 := ptsNormal pts1
  let N2 := ptsNormal pts2
  let Nu := ptsNormal ptsU
  let W3_A := cross3D (cross3D N1 N2) (sub3D ptsU.2.2 ptsU.2.1)
  disj ∧
  (273000 * (bdlLambda : ℝ) ^ 3 ≤ |W3_A 1| ∧ |W3_A 0| ≤ 5 * |W3_A 1|) ∧
  |- det3D N1 N2 Nu| ≤ (bdlLambda : ℝ) ^ 2

/-- Stage-2B bad point-triple predicate: dominant cross-product coordinate 0/1 and small 3x3 determinant. -/
def Stage2BBadPts (pts1 pts2 ptsU : Point3D × Point3D × Point3D) (disj : Prop) : Prop :=
  let N1 := ptsNormal pts1
  let N2 := ptsNormal pts2
  let Nu := ptsNormal ptsU
  let W3_B := cross3D (cross3D N1 N2) (sub3D ptsU.1 ptsU.2.2)
  disj ∧
  (273000 * (bdlLambda : ℝ) ^ 3 ≤ |W3_B 2| ∧ |W3_B 1| ≤ 5 * |W3_B 2|) ∧
  |- det3D N1 N2 Nu| ≤ (bdlLambda : ℝ) ^ 2

/-! ## 2. Coordinate Update Formulas for `lllSimplexPts` -/

/-- Stage-3A bad point-quadruple predicate: Type-A dominant Cramer sensitivity and small Cramer residual. -/
def Stage3ABadPts (pts1 pts2 pts3 ptsU : Point3D × Point3D × Point3D) (disj : Prop) : Prop :=
  let N1 := ptsNormal pts1; let b1 := ptsRhs pts1
  let N2 := ptsNormal pts2; let b2 := ptsRhs pts2
  let N3 := ptsNormal pts3; let b3 := ptsRhs pts3
  let N4 := ptsNormal ptsU; let b4 := ptsRhs ptsU
  let D4 := - det3D N1 N2 N3
  let VA : Point3D := fun a =>
    b1 * cross3D N2 N3 a - b2 * cross3D N1 N3 a + b3 * cross3D N1 N2 a + D4 * ptsU.2.1 a
  let WA := cross3D VA (sub3D ptsU.2.2 ptsU.2.1)
  let K := det3D N2 N3 N4 * b1 + (- det3D N1 N3 N4) * b2 + det3D N1 N2 N4 * b3 + D4 * b4
  disj ∧
  ((bdlLambda : ℝ) ^ 2 < |D4| ∧
   273000 * (bdlLambda : ℝ) ^ 2 * |D4| ≤ |WA 1| ∧
   |WA 0| ≤ 5 * |WA 1|) ∧
  |K| ≤ 7000000 * (bdlLambda : ℝ) ^ 2 * |D4|

/-- Stage-3B bad point-quadruple predicate: Type-B dominant Cramer sensitivity and small Cramer residual. -/
def Stage3BBadPts (pts1 pts2 pts3 ptsU : Point3D × Point3D × Point3D) (disj : Prop) : Prop :=
  let N1 := ptsNormal pts1; let b1 := ptsRhs pts1
  let N2 := ptsNormal pts2; let b2 := ptsRhs pts2
  let N3 := ptsNormal pts3; let b3 := ptsRhs pts3
  let N4 := ptsNormal ptsU; let b4 := ptsRhs ptsU
  let D4 := - det3D N1 N2 N3
  let VB : Point3D := fun a =>
    b1 * cross3D N2 N3 a - b2 * cross3D N1 N3 a + b3 * cross3D N1 N2 a + D4 * ptsU.2.2 a
  let WB := cross3D VB (sub3D ptsU.1 ptsU.2.2)
  let K := det3D N2 N3 N4 * b1 + (- det3D N1 N3 N4) * b2 + det3D N1 N2 N4 * b3 + D4 * b4
  disj ∧
  ((bdlLambda : ℝ) ^ 2 < |D4| ∧
   273000 * (bdlLambda : ℝ) ^ 2 * |D4| ≤ |WB 2| ∧
   |WB 1| ≤ 5 * |WB 2|) ∧
  |K| ≤ 7000000 * (bdlLambda : ℝ) ^ 2 * |D4|

/-- Stage-3C bad point-quadruple predicate: Type-C dominant Cramer sensitivity and small Cramer residual. -/
def Stage3CBadPts (pts1 pts2 pts3 ptsU : Point3D × Point3D × Point3D) (disj : Prop) : Prop :=
  let N1 := ptsNormal pts1; let b1 := ptsRhs pts1
  let N2 := ptsNormal pts2; let b2 := ptsRhs pts2
  let N3 := ptsNormal pts3; let b3 := ptsRhs pts3
  let N4 := ptsNormal ptsU; let b4 := ptsRhs ptsU
  let D4 := - det3D N1 N2 N3
  let VC : Point3D := fun a =>
    b1 * cross3D N2 N3 a - b2 * cross3D N1 N3 a + b3 * cross3D N1 N2 a + D4 * ptsU.1 a
  let WC := cross3D VC (sub3D ptsU.2.1 ptsU.1)
  let K := det3D N2 N3 N4 * b1 + (- det3D N1 N3 N4) * b2 + det3D N1 N2 N4 * b3 + D4 * b4
  disj ∧
  ((bdlLambda : ℝ) ^ 2 < |D4| ∧
   273000 * (bdlLambda : ℝ) ^ 2 * |D4| ≤ |WC 0| ∧
   |WC 2| ≤ 5 * |WC 0|) ∧
  |K| ≤ 7000000 * (bdlLambda : ℝ) ^ 2 * |D4|

/-- Classical decidability instance for `Stage1BadPts`. -/
instance instDecidableStage1BadPts (pts1 ptsU : Point3D × Point3D × Point3D) (disj : Prop) [Decidable disj] :
    Decidable (Stage1BadPts pts1 ptsU disj) := by unfold Stage1BadPts; infer_instance
/-- Classical decidability instance for `Stage2ABadPts`. -/
instance instDecidableStage2ABadPts (pts1 pts2 ptsU : Point3D × Point3D × Point3D) (disj : Prop) [Decidable disj] :
    Decidable (Stage2ABadPts pts1 pts2 ptsU disj) := by unfold Stage2ABadPts; infer_instance
/-- Classical decidability instance for `Stage2BBadPts`. -/
instance instDecidableStage2BBadPts (pts1 pts2 ptsU : Point3D × Point3D × Point3D) (disj : Prop) [Decidable disj] :
    Decidable (Stage2BBadPts pts1 pts2 ptsU disj) := by unfold Stage2BBadPts; infer_instance
/-- Classical decidability instance for `Stage3ABadPts`. -/
instance instDecidableStage3ABadPts (pts1 pts2 pts3 ptsU : Point3D × Point3D × Point3D) (disj : Prop) [Decidable disj] :
    Decidable (Stage3ABadPts pts1 pts2 pts3 ptsU disj) := by unfold Stage3ABadPts; infer_instance
/-- Classical decidability instance for `Stage3BBadPts`. -/
instance instDecidableStage3BBadPts (pts1 pts2 pts3 ptsU : Point3D × Point3D × Point3D) (disj : Prop) [Decidable disj] :
    Decidable (Stage3BBadPts pts1 pts2 pts3 ptsU disj) := by unfold Stage3BBadPts; infer_instance
/-- Classical decidability instance for `Stage3CBadPts`. -/
instance instDecidableStage3CBadPts (pts1 pts2 pts3 ptsU : Point3D × Point3D × Point3D) (disj : Prop) [Decidable disj] :
    Decidable (Stage3CBadPts pts1 pts2 pts3 ptsU disj) := by unfold Stage3CBadPts; infer_instance

/-- Updating `ω0` at a vertex `v` disjoint from simplex `s` leaves `lllSimplexPts B ω0 s` invariant. -/
lemma lllSimplexPts_update_not_mem (B : BundledCSSCode3D) (ω0 : LLLVertex B → Fin (lllGridN + 1))
    (s : ActiveSimplex2 B.code) (v : LLLVertex B) (c : Fin (lllGridN + 1))
    (hx : Sum.inr (Sum.inr s.val.1) ≠ v)
    (hq : Sum.inl s.val.2.1 ≠ v)
    (hz : Sum.inr (Sum.inl s.val.2.2) ≠ v) :
    lllSimplexPts B (Function.update ω0 v c) s = lllSimplexPts B ω0 s :=
  lllSimplexPts_eq_of_eq B _ _ s
    (Function.update_of_ne hx _ _)
    (Function.update_of_ne hq _ _)
    (Function.update_of_ne hz _ _)

/-- Explicit formula for `lllSimplexPts` when updating `ω0` at the X-check vertex of `u`. -/
lemma lllSimplexPts_update_X (B : BundledCSSCode3D) (ω0 : LLLVertex B → Fin (lllGridN + 1))
    (u : ActiveSimplex2 B.code) (c : Fin (lllGridN + 1)) :
    lllSimplexPts B (Function.update ω0 (Sum.inr (Sum.inr u.val.1)) c) u =
      (fun a => (bdlLambda : ℝ) * B.code.posX u.val.1 a + rationalCap2 (lllGridParam c) a,
       (lllSimplexPts B ω0 u).2.1,
       (lllSimplexPts B ω0 u).2.2) := by
  dsimp [lllSimplexPts, lllPCode, bdlPerturbStep, lllTQ, lllTZ, lllTX]
  rw [Function.update_self,
      Function.update_of_ne (fun h => nomatch h : (Sum.inl u.val.2.1 : LLLVertex B) ≠ Sum.inr (Sum.inr u.val.1)),
      Function.update_of_ne (fun h => nomatch h : (Sum.inr (Sum.inl u.val.2.2) : LLLVertex B) ≠ Sum.inr (Sum.inr u.val.1))]

/-! ## 3. Single-Coordinate Grid Update Bounds for Stage 1 and Stage 2 -/

/-- Explicit formula for `lllSimplexPts` when updating `ω0` at the qubit vertex of `u`. -/
lemma lllSimplexPts_update_Q (B : BundledCSSCode3D) (ω0 : LLLVertex B → Fin (lllGridN + 1))
    (u : ActiveSimplex2 B.code) (c : Fin (lllGridN + 1)) :
    lllSimplexPts B (Function.update ω0 (Sum.inl u.val.2.1) c) u =
      ((lllSimplexPts B ω0 u).1,
       fun a => (bdlLambda : ℝ) * B.code.posQ u.val.2.1 a + rationalCap0 (lllGridParam c) a,
       (lllSimplexPts B ω0 u).2.2) := by
  dsimp [lllSimplexPts, lllPCode, bdlPerturbStep, lllTQ, lllTZ, lllTX]
  rw [Function.update_self,
      Function.update_of_ne (fun h => nomatch h : (Sum.inr (Sum.inr u.val.1) : LLLVertex B) ≠ Sum.inl u.val.2.1),
      Function.update_of_ne (fun h => nomatch h : (Sum.inr (Sum.inl u.val.2.2) : LLLVertex B) ≠ Sum.inl u.val.2.1)]

/-- Explicit formula for `lllSimplexPts` when updating `ω0` at the Z-check vertex of `u`. -/
lemma lllSimplexPts_update_Z (B : BundledCSSCode3D) (ω0 : LLLVertex B → Fin (lllGridN + 1))
    (u : ActiveSimplex2 B.code) (c : Fin (lllGridN + 1)) :
    lllSimplexPts B (Function.update ω0 (Sum.inr (Sum.inl u.val.2.2)) c) u =
      ((lllSimplexPts B ω0 u).1,
       (lllSimplexPts B ω0 u).2.1,
       fun a => (bdlLambda : ℝ) * B.code.posZ u.val.2.2 a + rationalCap1 (lllGridParam c) a) := by
  dsimp [lllSimplexPts, lllPCode, bdlPerturbStep, lllTQ, lllTZ, lllTX]
  rw [Function.update_self,
      Function.update_of_ne (fun h => nomatch h : (Sum.inr (Sum.inr u.val.1) : LLLVertex B) ≠ Sum.inr (Sum.inl u.val.2.2)),
      Function.update_of_ne (fun h => nomatch h : (Sum.inl u.val.2.1 : LLLVertex B) ≠ Sum.inr (Sum.inl u.val.2.2))]

/-- Updating `ω0` at the X-check vertex of `u` satisfies `Stage1BadPts` for at most 1 grid value `c`. -/
lemma card_update_stage1BadPts_le_one (B : BundledCSSCode3D) (ω0 : LLLVertex B → Fin (lllGridN + 1))
    (s1 u : ActiveSimplex2 B.code) :
    (Finset.univ.filter (fun c : Fin (lllGridN + 1) =>
      Stage1BadPts
        (lllSimplexPts B (Function.update ω0 (Sum.inr (Sum.inr u.val.1)) c) s1)
        (lllSimplexPts B (Function.update ω0 (Sum.inr (Sum.inr u.val.1)) c) u)
        (VertexDisjointSimplex2 s1.val u.val))).card ≤ 1 := by
  -- Step 1: Establish initial algebraic and geometric reductions for `card_update_stage1BadPts_le_one`
  by_cases h_disj : VertexDisjointSimplex2 s1.val u.val
  · have hs1 : ∀ c, lllSimplexPts B (Function.update ω0 (Sum.inr (Sum.inr u.val.1)) c) s1 = lllSimplexPts B ω0 s1 :=
      fun c => lllSimplexPts_update_not_mem B ω0 s1 _ c
        (fun h => h_disj.1 (Sum.inr.inj (Sum.inr.inj h)))
        (fun h => nomatch h) (fun h => nomatch h)
    have hu : ∀ c, lllSimplexPts B (Function.update ω0 (Sum.inr (Sum.inr u.val.1)) c) u =
        (fun a => (bdlLambda : ℝ) * B.code.posX u.val.1 a + rationalCap2 (lllGridParam c) a,
         (lllSimplexPts B ω0 u).2.1, (lllSimplexPts B ω0 u).2.2) :=
      fun c => lllSimplexPts_update_X B ω0 u c
    let N1 := ptsNormal (lllSimplexPts B ω0 s1)
    let A0 : Point3D := fun a => (bdlLambda : ℝ) * B.code.posX u.val.1 a
    let B2 := (lllSimplexPts B ω0 u).2.1
    let C2 := (lllSimplexPts B ω0 u).2.2
    -- Step 2: Complete the main case analysis and bound assembly for `card_update_stage1BadPts_le_one`
    let P : Prop :=
      (900000 * (bdlLambda : ℝ) ^ 2 ≤ N1 0 ∧ N1 0 ≤ 987000 * (bdlLambda : ℝ) ^ 2) ∧
      (900000 * (bdlLambda : ℝ) ^ 2 ≤ N1 1 ∧ N1 1 ≤ 987000 * (bdlLambda : ℝ) ^ 2) ∧
      (31 * (bdlLambda : ℝ) ≤ C2 2 - B2 2 ∧ C2 2 - B2 2 ≤ 49 * (bdlLambda : ℝ))
    let A2 (s : ℝ) : Point3D := fun a => A0 a + rationalCap2 s a
    let Nt (s : ℝ) : Point3D := cross3D (sub3D B2 (A2 s)) (sub3D C2 (A2 s))
    have h_sub : Finset.univ.filter (fun c : Fin (lllGridN + 1) =>
        Stage1BadPts
          (lllSimplexPts B (Function.update ω0 (Sum.inr (Sum.inr u.val.1)) c) s1)
          (lllSimplexPts B (Function.update ω0 (Sum.inr (Sum.inr u.val.1)) c) u)
          (VertexDisjointSimplex2 s1.val u.val)) ⊆
        Finset.univ.filter (fun c : Fin (lllGridN + 1) =>
          P ∧ |(cross3D N1 (Nt (lllGridParam c))) 2| ≤ (bdlLambda : ℝ) ^ 3) := by
      intro c hc
      rw [Finset.mem_filter] at hc ⊢
      rcases hc with ⟨hc_mem, h_bad⟩
      rw [hs1 c, hu c] at h_bad
      exact ⟨hc_mem, h_bad.2.1, h_bad.2.2⟩
    exact le_trans (Finset.card_le_card h_sub)
      (card_filter_lllGridParam_stage1_le_one P N1 A0 B2 C2 id)
  · rw [Finset.card_le_one]
    intro c1 hc1; exfalso; exact h_disj (Finset.mem_filter.mp hc1).2.1

/-- Updating `ω0` at the X-check vertex of `u` satisfies `Stage2ABadPts` for at most 1 grid value `c`. -/
lemma card_update_stage2ABadPts_le_one (B : BundledCSSCode3D) (ω0 : LLLVertex B → Fin (lllGridN + 1))
    (s1 s2 u : ActiveSimplex2 B.code) :
    (Finset.univ.filter (fun c : Fin (lllGridN + 1) =>
      Stage2ABadPts
        (lllSimplexPts B (Function.update ω0 (Sum.inr (Sum.inr u.val.1)) c) s1)
        (lllSimplexPts B (Function.update ω0 (Sum.inr (Sum.inr u.val.1)) c) s2)
        (lllSimplexPts B (Function.update ω0 (Sum.inr (Sum.inr u.val.1)) c) u)
        (VertexDisjointSimplex2 s1.val u.val ∧ VertexDisjointSimplex2 s2.val u.val))).card ≤ 1 := by
  -- Step 1: Establish initial algebraic and geometric reductions for `card_update_stage2ABadPts_le_one`
  by_cases h_disj : VertexDisjointSimplex2 s1.val u.val ∧ VertexDisjointSimplex2 s2.val u.val
  · have hs1 : ∀ c, lllSimplexPts B (Function.update ω0 (Sum.inr (Sum.inr u.val.1)) c) s1 = lllSimplexPts B ω0 s1 :=
      fun c => lllSimplexPts_update_not_mem B ω0 s1 _ c
        (fun h => h_disj.1.1 (Sum.inr.inj (Sum.inr.inj h))) (fun h => nomatch h) (fun h => nomatch h)
    have hs2 : ∀ c, lllSimplexPts B (Function.update ω0 (Sum.inr (Sum.inr u.val.1)) c) s2 = lllSimplexPts B ω0 s2 :=
      fun c => lllSimplexPts_update_not_mem B ω0 s2 _ c
        (fun h => h_disj.2.1 (Sum.inr.inj (Sum.inr.inj h))) (fun h => nomatch h) (fun h => nomatch h)
    have hu : ∀ c, lllSimplexPts B (Function.update ω0 (Sum.inr (Sum.inr u.val.1)) c) u =
        (fun a => (bdlLambda : ℝ) * B.code.posX u.val.1 a + rationalCap2 (lllGridParam c) a,
         (lllSimplexPts B ω0 u).2.1, (lllSimplexPts B ω0 u).2.2) :=
      fun c => lllSimplexPts_update_X B ω0 u c
    let N1 := ptsNormal (lllSimplexPts B ω0 s1)
    let N2 := ptsNormal (lllSimplexPts B ω0 s2)
    let A0 : Point3D := fun a => (bdlLambda : ℝ) * B.code.posX u.val.1 a
    -- Step 2: Complete the main case analysis and bound assembly for `card_update_stage2ABadPts_le_one`
    let B2 := (lllSimplexPts B ω0 u).2.1
    let C2 := (lllSimplexPts B ω0 u).2.2
    let W3_A := cross3D (cross3D N1 N2) (sub3D C2 B2)
    let P : Prop := 273000 * (bdlLambda : ℝ) ^ 3 ≤ |W3_A 1| ∧ |W3_A 0| ≤ 5 * |W3_A 1|
    let A2 (s : ℝ) : Point3D := fun a => A0 a + rationalCap2 s a
    let Nt (s : ℝ) : Point3D := cross3D (sub3D B2 (A2 s)) (sub3D C2 (A2 s))
    have h_sub : Finset.univ.filter (fun c : Fin (lllGridN + 1) =>
        Stage2ABadPts
          (lllSimplexPts B (Function.update ω0 (Sum.inr (Sum.inr u.val.1)) c) s1)
          (lllSimplexPts B (Function.update ω0 (Sum.inr (Sum.inr u.val.1)) c) s2)
          (lllSimplexPts B (Function.update ω0 (Sum.inr (Sum.inr u.val.1)) c) u)
          (VertexDisjointSimplex2 s1.val u.val ∧ VertexDisjointSimplex2 s2.val u.val)) ⊆
        Finset.univ.filter (fun c : Fin (lllGridN + 1) =>
          P ∧ |- det3D N1 N2 (Nt (lllGridParam c))| ≤ (bdlLambda : ℝ) ^ 2) := by
      intro c hc
      rw [Finset.mem_filter] at hc ⊢
      rcases hc with ⟨hc_mem, h_bad⟩
      rw [hs1 c, hs2 c, hu c] at h_bad
      exact ⟨hc_mem, h_bad.2.1, h_bad.2.2⟩
    exact le_trans (Finset.card_le_card h_sub)
      (card_filter_lllGridParam_stage2A_le_one P N1 N2 A0 B2 C2 id)
  · rw [Finset.card_le_one]
    intro c1 hc1; exfalso; exact h_disj (Finset.mem_filter.mp hc1).2.1

/-- Updating `ω0` at the qubit vertex of `u` satisfies `Stage2BBadPts` for at most 1 grid value `c`. -/
lemma card_update_stage2BBadPts_le_one (B : BundledCSSCode3D) (ω0 : LLLVertex B → Fin (lllGridN + 1))
    (s1 s2 u : ActiveSimplex2 B.code) :
    (Finset.univ.filter (fun c : Fin (lllGridN + 1) =>
      Stage2BBadPts
        (lllSimplexPts B (Function.update ω0 (Sum.inl u.val.2.1) c) s1)
        (lllSimplexPts B (Function.update ω0 (Sum.inl u.val.2.1) c) s2)
        (lllSimplexPts B (Function.update ω0 (Sum.inl u.val.2.1) c) u)
        (VertexDisjointSimplex2 s1.val u.val ∧ VertexDisjointSimplex2 s2.val u.val))).card ≤ 1 := by
  -- Step 1: Establish initial algebraic and geometric reductions for `card_update_stage2BBadPts_le_one`
  by_cases h_disj : VertexDisjointSimplex2 s1.val u.val ∧ VertexDisjointSimplex2 s2.val u.val
  · have hs1 : ∀ c, lllSimplexPts B (Function.update ω0 (Sum.inl u.val.2.1) c) s1 = lllSimplexPts B ω0 s1 :=
      fun c => lllSimplexPts_update_not_mem B ω0 s1 _ c
        (fun h => nomatch h) (fun h => h_disj.1.2.1 (Sum.inl.inj h)) (fun h => nomatch h)
    have hs2 : ∀ c, lllSimplexPts B (Function.update ω0 (Sum.inl u.val.2.1) c) s2 = lllSimplexPts B ω0 s2 :=
      fun c => lllSimplexPts_update_not_mem B ω0 s2 _ c
        (fun h => nomatch h) (fun h => h_disj.2.2.1 (Sum.inl.inj h)) (fun h => nomatch h)
    have hu : ∀ c, lllSimplexPts B (Function.update ω0 (Sum.inl u.val.2.1) c) u =
        ((lllSimplexPts B ω0 u).1,
         fun a => (bdlLambda : ℝ) * B.code.posQ u.val.2.1 a + rationalCap0 (lllGridParam c) a,
         (lllSimplexPts B ω0 u).2.2) :=
      fun c => lllSimplexPts_update_Q B ω0 u c
    let N1 := ptsNormal (lllSimplexPts B ω0 s1)
    let N2 := ptsNormal (lllSimplexPts B ω0 s2)
    let A2 := (lllSimplexPts B ω0 u).1
    -- Step 2: Complete the main case analysis and bound assembly for `card_update_stage2BBadPts_le_one`
    let B0 : Point3D := fun a => (bdlLambda : ℝ) * B.code.posQ u.val.2.1 a
    let C2 := (lllSimplexPts B ω0 u).2.2
    let W3_B := cross3D (cross3D N1 N2) (sub3D A2 C2)
    let P : Prop := 273000 * (bdlLambda : ℝ) ^ 3 ≤ |W3_B 2| ∧ |W3_B 1| ≤ 5 * |W3_B 2|
    let B_pt (s : ℝ) : Point3D := fun a => B0 a + rationalCap0 s a
    let Nt (s : ℝ) : Point3D := cross3D (sub3D (B_pt s) A2) (sub3D C2 A2)
    have h_sub : Finset.univ.filter (fun c : Fin (lllGridN + 1) =>
        Stage2BBadPts
          (lllSimplexPts B (Function.update ω0 (Sum.inl u.val.2.1) c) s1)
          (lllSimplexPts B (Function.update ω0 (Sum.inl u.val.2.1) c) s2)
          (lllSimplexPts B (Function.update ω0 (Sum.inl u.val.2.1) c) u)
          (VertexDisjointSimplex2 s1.val u.val ∧ VertexDisjointSimplex2 s2.val u.val)) ⊆
        Finset.univ.filter (fun c : Fin (lllGridN + 1) =>
          P ∧ |- det3D N1 N2 (Nt (lllGridParam c))| ≤ (bdlLambda : ℝ) ^ 2) := by
      intro c hc
      rw [Finset.mem_filter] at hc ⊢
      rcases hc with ⟨hc_mem, h_bad⟩
      rw [hs1 c, hs2 c, hu c] at h_bad
      exact ⟨hc_mem, h_bad.2.1, h_bad.2.2⟩
    exact le_trans (Finset.card_le_card h_sub)
      (card_filter_lllGridParam_stage2B_le_one P N1 N2 A2 B0 C2 id)
  · rw [Finset.card_le_one]
    intro c1 hc1; exfalso; exact h_disj (Finset.mem_filter.mp hc1).2.1

end WeldedHierarchy
