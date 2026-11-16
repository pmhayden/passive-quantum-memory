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

import Proofs.Step1LLLDensity.RationalSphericalCapGeometry

/-!
# Simplex Vertex Degree and Four-Simplex Cramer Compatibility

Defines bounded 2-simplex vertex degree `HasBoundedSimplexDegreeD`, vertex-disjoint 2-simplices `VertexDisjointSimplex2`, and the four-simplex Cramer compatibility predicates `FourSimplicesCramerCompatible` and `FourSimplicesDominantCramerCompatible`. Proves that any four 2-simplices intersecting a common unit ball satisfy `four_simplices_inter_ball3D_implies_cramer_compatible`, verifies duality invariance `dualBundled_preserves_bounded_simplex_degreeD`, and provides Cramer determinant and cylinder-counting identities.

## References

* Part I, Section 2.1 (`subsec:css-complexes`), Definition 2.1 (`def:3d-css-complex`), Definition 2.2 (`def:well-separated-base`)
* Part I, Section 2.2 (`subsec:step1-lll`), Proposition 2.4 (`prop:step1-lll`)
-/

noncomputable section
open scoped Classical BigOperators
namespace WeldedHierarchy

/-! ## 1. Bounded Simplex Degree and Vertex Stars -/

/-- Parameterized vertex-to-2-simplex incidence degree bound `deg_simplex ≤ D` (`9 * D ≤ 5595`). -/
def HasBoundedSimplexDegreeD (B : BundledCSSCode3D) (D : ℕ) : Prop :=
  (∀ x : B.M_X, (Finset.univ.filter (fun s : ActiveSimplex2 B.code => s.val.1 = x)).card ≤ D) ∧
  (∀ q : B.Q, (Finset.univ.filter (fun s : ActiveSimplex2 B.code => s.val.2.1 = q)).card ≤ D) ∧
  (∀ z : B.M_Z, (Finset.univ.filter (fun s : ActiveSimplex2 B.code => s.val.2.2 = z)).card ≤ D)

/-- Two 2-simplices `(x1, q1, z1)` and `(x2, q2, z2)` are vertex-disjoint iff all three vertex coordinates differ. -/
def VertexDisjointSimplex2 {Q M_Z M_X : Type} (s1 s2 : M_X × Q × M_Z) : Prop :=
  s1.1 ≠ s2.1 ∧ s1.2.1 ≠ s2.2.1 ∧ s1.2.2 ≠ s2.2.2

/-- The star of active 2-simplices sharing at least one vertex (`x`, `q`, or `z`) with `s0`. -/
def simplexVertexStar {Q M_Z M_X : Type}
    [Fintype Q] [DecidableEq Q] [Fintype M_Z] [DecidableEq M_Z] [Fintype M_X] [DecidableEq M_X]
    (code : CSSCode3D Q M_Z M_X) (s0 : ActiveSimplex2 code) : Finset (ActiveSimplex2 code) :=
  (Finset.univ.filter (fun s : ActiveSimplex2 code => s.val.1 = s0.val.1) ∪
   Finset.univ.filter (fun s : ActiveSimplex2 code => s.val.2.1 = s0.val.2.1)) ∪
  Finset.univ.filter (fun s : ActiveSimplex2 code => s.val.2.2 = s0.val.2.2)

/-- A 2-simplex `u` lies outside `simplexVertexStar B S` iff it is vertex-disjoint from every `s ∈ S`. -/
lemma not_mem_simplexVertexStar_iff {Q M_Z M_X : Type}
    [Fintype Q] [DecidableEq Q] [Fintype M_Z] [DecidableEq M_Z] [Fintype M_X] [DecidableEq M_X]
    (code : CSSCode3D Q M_Z M_X) (s0 s : ActiveSimplex2 code) :
    s ∉ simplexVertexStar code s0 ↔ VertexDisjointSimplex2 s0.val s.val := by
  dsimp [simplexVertexStar, VertexDisjointSimplex2]
  simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and, not_or]
  exact ⟨fun ⟨⟨h1, h2⟩, h3⟩ => ⟨Ne.symm h1, Ne.symm h2, Ne.symm h3⟩,
         fun ⟨h1, h2, h3⟩ => ⟨⟨Ne.symm h1, Ne.symm h2⟩, Ne.symm h3⟩⟩

/-- Algebraic Cramer-residual compatibility predicate for 4 perturbed active 2-simplices intersecting a common unit ball. -/
def FourSimplicesCramerCompatible {Q M_Z M_X : Type}
    [Fintype Q] [DecidableEq Q] [Fintype M_Z] [DecidableEq M_Z] [Fintype M_X] [DecidableEq M_X]
    (pcode : CSSCode3D Q M_Z M_X) (s1 s2 s3 s4 : ActiveSimplex2 pcode) : Prop :=
  let A1 := pcode.posX s1.val.1; let B1 := pcode.posQ s1.val.2.1; let C1 := pcode.posZ s1.val.2.2
  let A2 := pcode.posX s2.val.1; let B2 := pcode.posQ s2.val.2.1; let C2 := pcode.posZ s2.val.2.2
  let A3 := pcode.posX s3.val.1; let B3 := pcode.posQ s3.val.2.1; let C3 := pcode.posZ s3.val.2.2
  let A4 := pcode.posX s4.val.1; let B4 := pcode.posQ s4.val.2.1; let C4 := pcode.posZ s4.val.2.2
  let N1 := cross3D (sub3D B1 A1) (sub3D C1 A1); let b1 := dot3D N1 A1
  let N2 := cross3D (sub3D B2 A2) (sub3D C2 A2); let b2 := dot3D N2 A2
  let N3 := cross3D (sub3D B3 A3) (sub3D C3 A3); let b3 := dot3D N3 A3
  let N4 := cross3D (sub3D B4 A4) (sub3D C4 A4); let b4 := dot3D N4 A4
  let D1 := det3D N2 N3 N4
  let D2 := - det3D N1 N3 N4
  let D3 := det3D N1 N2 N4
  let D4 := - det3D N1 N2 N3
  (D1 * b1 + D2 * b2 + D3 * b3 + D4 * b4) ^ 2 ≤
    4 * (D1 ^ 2 * dot3D N1 N1 + D2 ^ 2 * dot3D N2 N2 + D3 ^ 2 * dot3D N3 N3 + D4 ^ 2 * dot3D N4 N4)

/-- Linearity of `dot3D` in the right difference argument `sub3D x0 A`. -/
lemma dot3D_sub3D_eq_sub (N x0 A : Point3D) :
    dot3D N (sub3D x0 A) = dot3D N x0 - dot3D N A := by
  dsimp [dot3D, sub3D]; ring

/-- Any four active 2-simplices intersecting a unit ball `Ball3D x0 1` satisfy `FourSimplicesCramerCompatible`. -/
lemma four_simplices_inter_ball3D_implies_cramer_compatible {Q M_Z M_X : Type}
    [Fintype Q] [DecidableEq Q] [Fintype M_Z] [DecidableEq M_Z] [Fintype M_X] [DecidableEq M_X]
    (pcode : CSSCode3D Q M_Z M_X) (x0 : Point3D) (s1 s2 s3 s4 : ActiveSimplex2 pcode)
    (h1 : (simplex2D3D (pcode.posX s1.val.1) (pcode.posQ s1.val.2.1) (pcode.posZ s1.val.2.2) ∩ ball3D x0 1).Nonempty)
    (h2 : (simplex2D3D (pcode.posX s2.val.1) (pcode.posQ s2.val.2.1) (pcode.posZ s2.val.2.2) ∩ ball3D x0 1).Nonempty)
    (h3 : (simplex2D3D (pcode.posX s3.val.1) (pcode.posQ s3.val.2.1) (pcode.posZ s3.val.2.2) ∩ ball3D x0 1).Nonempty)
    (h4 : (simplex2D3D (pcode.posX s4.val.1) (pcode.posQ s4.val.2.1) (pcode.posZ s4.val.2.2) ∩ ball3D x0 1).Nonempty) :
    FourSimplicesCramerCompatible pcode s1 s2 s3 s4 := by
  have hr1 := simplex2D3D_inter_ball3D_plane_residual _ _ _ x0 h1
  have hr2 := simplex2D3D_inter_ball3D_plane_residual _ _ _ x0 h2
  have hr3 := simplex2D3D_inter_ball3D_plane_residual _ _ _ x0 h3
  have hr4 := simplex2D3D_inter_ball3D_plane_residual _ _ _ x0 h4
  (try dsimp at hr1 hr2 hr3 hr4)
  rw [dot3D_sub3D_eq_sub] at hr1 hr2 hr3 hr4
  exact four_planes_cramer_residual_bound _ _ _ _ x0 _ _ _ _ hr1 hr2 hr3 hr4

/-- Under `HasBoundedSimplexDegreeD B D`, the vertex star of `S` has cardinality at most `3 * S.card * D`. -/
lemma card_simplexVertexStar_le_three_mul (B : BundledCSSCode3D) {D : ℕ}
    (h_deg : HasBoundedSimplexDegreeD B D) (s0 : ActiveSimplex2 B.code) :
    (simplexVertexStar B.code s0).card ≤ 3 * D := by
  dsimp [simplexVertexStar]
  have h1 := Finset.card_union_le
    (Finset.univ.filter (fun s : ActiveSimplex2 B.code => s.val.1 = s0.val.1) ∪
     Finset.univ.filter (fun s : ActiveSimplex2 B.code => s.val.2.1 = s0.val.2.1))
    (Finset.univ.filter (fun s : ActiveSimplex2 B.code => s.val.2.2 = s0.val.2.2))
  have h2 := Finset.card_union_le
    (Finset.univ.filter (fun s : ActiveSimplex2 B.code => s.val.1 = s0.val.1))
    (Finset.univ.filter (fun s : ActiveSimplex2 B.code => s.val.2.1 = s0.val.2.1))
  have hx := h_deg.1 s0.val.1
  have hq := h_deg.2.1 s0.val.2.1
  have hz := h_deg.2.2 s0.val.2.2
  omega

/-! ## 2. 3D Cramer Determinant Identities and Ball Coordinate Bounds -/

/-- Lower bound on the cardinality of `U \ simplexVertexStar B S` under `HasBoundedSimplexDegreeD B D`. -/
lemma card_sdiff_simplexVertexStar_ge_three_mul (B : BundledCSSCode3D) {D : ℕ}
    (h_deg : HasBoundedSimplexDegreeD B D)
    (T : Finset (ActiveSimplex2 B.code)) (s0 : ActiveSimplex2 B.code) :
    T.card - 3 * D ≤ (T \ simplexVertexStar B.code s0).card := by
  have h_sub : T ⊆ (T \ simplexVertexStar B.code s0) ∪ simplexVertexStar B.code s0 := by
    intro x hx
    rw [Finset.mem_union, Finset.mem_sdiff]
    by_cases h : x ∈ simplexVertexStar B.code s0
    · exact Or.inr h
    · exact Or.inl ⟨hx, h⟩
  have h_le := le_trans (Finset.card_le_card h_sub)
    (Finset.card_union_le (T \ simplexVertexStar B.code s0) (simplexVertexStar B.code s0))
  have h_star := card_simplexVertexStar_le_three_mul B h_deg s0
  omega

/-- Exact polynomial identity `W_A + W_B + W_C = D4 * N4`: the sum of the Cramer residual sensitivities
    with respect to `A4`, `B4`, and `C4` cancels `b1, b2, b3` identically and equals `D4 * N4`. -/
lemma cramer_W_sum_eq_det_mul_normal (N1 N2 N3 A4 B4 C4 : Point3D) (b1 b2 b3 : ℝ) (a : Fin 3) :
    let D4 := - det3D N1 N2 N3
    let N4 := cross3D (sub3D B4 A4) (sub3D C4 A4)
    let VA : Point3D := fun k => b1 * cross3D N2 N3 k - b2 * cross3D N1 N3 k + b3 * cross3D N1 N2 k + D4 * B4 k
    let VB : Point3D := fun k => b1 * cross3D N2 N3 k - b2 * cross3D N1 N3 k + b3 * cross3D N1 N2 k + D4 * C4 k
    let VC : Point3D := fun k => b1 * cross3D N2 N3 k - b2 * cross3D N1 N3 k + b3 * cross3D N1 N2 k + D4 * A4 k
    let WA := cross3D VA (sub3D C4 B4)
    let WB := cross3D VB (sub3D A4 C4)
    let WC := cross3D VC (sub3D B4 A4)
    WA a + WB a + WC a = D4 * N4 a := by
  fin_cases a <;> { dsimp [det3D, cross3D, sub3D]; ring }

/-- Exact `2 × 2` Cramer recovery of `U 2 = (N1 × N2) 2` from the sensitivities `W3_A 1` and `W3_B 1` of `det3D N1 N2 N3`. -/
lemma cramer_U2_recovery_from_WA_WB (U A3 B3 C3 : Point3D) :
    let E3 := sub3D C3 B3
    let F3 := sub3D A3 C3
    let N3 := cross3D (sub3D B3 A3) (sub3D C3 A3)
    let W3_A := cross3D U E3
    let W3_B := cross3D U F3
    N3 1 * U 2 = E3 2 * W3_B 1 - F3 2 * W3_A 1 := by
  dsimp [cross3D, sub3D]; ring

/-- Exact 2-point difference identity for `w0 * rcos t + w1 * rsin t`. -/
lemma rcos_rsin_two_point_identity (w0 w1 t1 t2 : ℝ) :
    (1 + t1 ^ 2) * (1 + t2 ^ 2) * ((w0 * rcos t2 + w1 * rsin t2) - (w0 * rcos t1 + w1 * rsin t1)) =
    2 * (t2 - t1) * (w1 * (1 - t1 * t2) - w0 * (t1 + t2)) := by
  have h1 : 1 + t1 ^ 2 ≠ 0 := by positivity
  have h2 : 1 + t2 ^ 2 ≠ 0 := by positivity
  dsimp [rcos, rsin]
  field_simp
  ring

/-- If `p ∈ Ball3D x0 1`, then each coordinate difference `|p a - x0 a|` is at most `1`. -/
lemma abs_coord_sub_le_one_of_mem_ball3D_one (p x0 : Point3D) (hp : p ∈ ball3D x0 1) (a : Fin 3) :
    |p a - x0 a| ≤ 1 := by
  have h_coord : (p a - x0 a) ^ 2 ≤ distSq3D p x0 := by
    fin_cases a <;> { dsimp [distSq3D]; nlinarith [sq_nonneg (p 0 - x0 0), sq_nonneg (p 1 - x0 1), sq_nonneg (p 2 - x0 2)] }
  dsimp [ball3D] at hp
  rw [one_pow] at hp
  have h_sq : (p a - x0 a) ^ 2 ≤ 1 := le_trans h_coord hp
  rw [abs_le]
  constructor <;> nlinarith

/-- Integer floor shift `⌊d + R⌋₊` lies in `[0, 2 * R + 1)` whenever `-R ≤ d ≤ R`. -/
lemma floor_shift_in_fin (R : ℕ) (d : ℝ) (hd_lo : -(R : ℝ) ≤ d) (hd_hi : d ≤ (R : ℝ)) :
    (⌊d + (R : ℝ)⌋.toNat) < 2 * R + 1 ∧
    |d - (((⌊d + (R : ℝ)⌋.toNat : ℕ) : ℝ) - (R : ℝ) + 1 / 2)| ≤ 1 / 2 := by
  have h_nonneg : (0 : ℝ) ≤ d + (R : ℝ) := by linarith
  have h_floor_nonneg : 0 ≤ ⌊d + (R : ℝ)⌋ := Int.floor_nonneg.mpr h_nonneg
  have h_floor_le : (⌊d + (R : ℝ)⌋ : ℝ) ≤ d + (R : ℝ) := Int.floor_le (d + (R : ℝ))
  have h_lt_floor : d + (R : ℝ) < (⌊d + (R : ℝ)⌋ : ℝ) + 1 := Int.lt_floor_add_one (d + (R : ℝ))
  have h_floor_lt_int : ⌊d + (R : ℝ)⌋ < (2 * R + 1 : ℤ) := by
    have : (⌊d + (R : ℝ)⌋ : ℝ) < ((2 * R + 1 : ℤ) : ℝ) := by push_cast; linarith
    exact_mod_cast this
  have h_toNat_eq : ((⌊d + (R : ℝ)⌋.toNat : ℕ) : ℤ) = ⌊d + (R : ℝ)⌋ := Int.toNat_of_nonneg h_floor_nonneg
  have h_toNat_real : ((⌊d + (R : ℝ)⌋.toNat : ℕ) : ℝ) = (⌊d + (R : ℝ)⌋ : ℝ) := by exact_mod_cast h_toNat_eq
  refine ⟨by omega, ?_⟩
  rw [h_toNat_real, abs_le]
  constructor <;> linarith

/-- Symmetry of `HasBoundedSimplexDegreeD` under CSS code duality (`dualBundled`). -/
lemma dualBundled_preserves_bounded_simplex_degreeD (B : BundledCSSCode3D) {D : ℕ}
    (h : HasBoundedSimplexDegreeD B D) :
    HasBoundedSimplexDegreeD (dualBundled B) D := by
  let swapSimplex : ActiveSimplex2 (dualBundled B).code → ActiveSimplex2 B.code :=
    fun s => ⟨(s.val.2.2, s.val.2.1, s.val.1), s.property.2, s.property.1⟩
  have h_inj : ∀ s1 s2 : ActiveSimplex2 (dualBundled B).code, swapSimplex s1 = swapSimplex s2 → s1 = s2 := by
    intro s1 s2 heq
    have hx : s1.val.2.2 = s2.val.2.2 := congr_arg (fun u : ActiveSimplex2 B.code => u.val.1) heq
    have hq : s1.val.2.1 = s2.val.2.1 := congr_arg (fun u : ActiveSimplex2 B.code => u.val.2.1) heq
    have hz : s1.val.1 = s2.val.1 := congr_arg (fun u : ActiveSimplex2 B.code => u.val.2.2) heq
    exact Subtype.ext (Prod.ext hz (Prod.ext hq hx))
  refine ⟨?_, ?_, ?_⟩
  · intro z
    refine le_trans (Finset.card_le_card_of_injOn swapSimplex ?_ (fun s1 _ s2 _ h12 => h_inj s1 s2 h12)) (h.2.2 z)
    intro s hs
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hs ⊢
    exact hs
  · intro q
    refine le_trans (Finset.card_le_card_of_injOn swapSimplex ?_ (fun s1 _ s2 _ h12 => h_inj s1 s2 h12)) (h.2.1 q)
    intro s hs
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hs ⊢
    exact hs
  · intro x
    refine le_trans (Finset.card_le_card_of_injOn swapSimplex ?_ (fun s1 _ s2 _ h12 => h_inj s1 s2 h12)) (h.1 x)
    intro s hs
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hs ⊢
    exact hs

/-! ## 3. Dominant Cramer Compatibility and Cylinder Fiber Counting -/

/-- Dominant 3-minor Cramer compatibility predicate (`|D1*b1 + D2*b2 + D3*b3 + D4*b4| ≤ 7000000 * bdlLambda^2 * |D4|`),
    where `D4` is the 3-minor of the first three simplices `(s1, s2, s3)`. -/
def FourSimplicesDominantCramerCompatible {Q M_Z M_X : Type}
    [Fintype Q] [DecidableEq Q] [Fintype M_Z] [DecidableEq M_Z] [Fintype M_X] [DecidableEq M_X]
    (pcode : CSSCode3D Q M_Z M_X) (s1 s2 s3 s4 : ActiveSimplex2 pcode) : Prop :=
  let A1 := pcode.posX s1.val.1; let B1 := pcode.posQ s1.val.2.1; let C1 := pcode.posZ s1.val.2.2
  let A2 := pcode.posX s2.val.1; let B2 := pcode.posQ s2.val.2.1; let C2 := pcode.posZ s2.val.2.2
  let A3 := pcode.posX s3.val.1; let B3 := pcode.posQ s3.val.2.1; let C3 := pcode.posZ s3.val.2.2
  let A4 := pcode.posX s4.val.1; let B4 := pcode.posQ s4.val.2.1; let C4 := pcode.posZ s4.val.2.2
  let N1 := cross3D (sub3D B1 A1) (sub3D C1 A1); let b1 := dot3D N1 A1
  let N2 := cross3D (sub3D B2 A2) (sub3D C2 A2); let b2 := dot3D N2 A2
  let N3 := cross3D (sub3D B3 A3) (sub3D C3 A3); let b3 := dot3D N3 A3
  let N4 := cross3D (sub3D B4 A4) (sub3D C4 A4); let b4 := dot3D N4 A4
  let D1 := det3D N2 N3 N4
  let D2 := - det3D N1 N3 N4
  let D3 := det3D N1 N2 N4
  let D4 := - det3D N1 N2 N3
  |D1 * b1 + D2 * b2 + D3 * b3 + D4 * b4| ≤ 7000000 * (bdlLambda : ℝ) ^ 2 * |D4|

/-- **Exact Cylinder Independence via Coordinate-Splice Involution (`card_filter_and_mul_card_univ_eq_of_cylinder`)**:
    If `P0 : (V → α) → Prop` depends only on coordinates in `V0 : Finset V` and `P1 : (V → α) → Prop`
    depends only on coordinates outside `V0`, then `(filter (P0 ∧ P1)).card * univ.card = (filter P0).card * (filter P1).card`. -/
lemma card_filter_and_mul_card_univ_eq_of_cylinder {V α : Type*} [Fintype V] [DecidableEq V] [Fintype α] [DecidableEq α]
    (V0 : Finset V) (P0 P1 : (V → α) → Prop) [DecidablePred P0] [DecidablePred P1]
    (hP0 : ∀ ω1 ω2 : V → α, (∀ x ∈ V0, ω1 x = ω2 x) → (P0 ω1 ↔ P0 ω2))
    (hP1 : ∀ ω1 ω2 : V → α, (∀ x ∉ V0, ω1 x = ω2 x) → (P1 ω1 ↔ P1 ω2)) :
    (Finset.univ.filter (fun ω : V → α => P0 ω ∧ P1 ω)).card * (Finset.univ : Finset (V → α)).card =
      (Finset.univ.filter P0).card * (Finset.univ.filter P1).card := by
  let S_lhs : Finset ((V → α) × (V → α)) :=
    (Finset.univ.filter (fun ω : V → α => P0 ω ∧ P1 ω)) ×ˢ (Finset.univ : Finset (V → α))
  let S_rhs : Finset ((V → α) × (V → α)) :=
    (Finset.univ.filter P0) ×ˢ (Finset.univ.filter P1)
  let splice : (V → α) × (V → α) → (V → α) × (V → α) :=
    fun p => (fun x => if x ∈ V0 then p.1 x else p.2 x,
              fun x => if x ∈ V0 then p.2 x else p.1 x)
  have h_invo : ∀ p : (V → α) × (V → α), splice (splice p) = p := by
    intro ⟨ω1, ω2⟩
    ext x <;> { dsimp [splice]; split_ifs <;> rfl }
  have h_eq_card : S_lhs.card = S_rhs.card := by
    refine Finset.card_bij (fun p _ => splice p) ?_ ?_ ?_
    · intro ⟨ω1, ω2⟩ hp
      rw [Finset.mem_product, Finset.mem_filter] at hp
      rw [Finset.mem_product, Finset.mem_filter, Finset.mem_filter]
      refine ⟨⟨Finset.mem_univ _, ?_⟩, ⟨Finset.mem_univ _, ?_⟩⟩
      · exact (hP0 _ ω1 (fun x hx => if_pos hx)).mpr hp.1.2.1
      · exact (hP1 _ ω1 (fun x hx => if_neg hx)).mpr hp.1.2.2
    · intro p1 _ p2 _ h_eq
      rw [← h_invo p1, ← h_invo p2, h_eq]
    · intro ⟨ω1, ω2⟩ hq
      rw [Finset.mem_product, Finset.mem_filter, Finset.mem_filter] at hq
      refine ⟨splice (ω1, ω2), ?_, h_invo (ω1, ω2)⟩
      rw [Finset.mem_product, Finset.mem_filter]
      refine ⟨⟨Finset.mem_univ _, ?_, ?_⟩, Finset.mem_univ _⟩
      · exact (hP0 _ ω1 (fun x hx => if_pos hx)).mpr hq.1.2
      · exact (hP1 _ ω2 (fun x hx => if_neg hx)).mpr hq.2.2
  rw [Finset.card_product, Finset.card_product] at h_eq_card
  exact h_eq_card

/-- **Telescoping Subset-Difference Lemma**: If inserting any element `t ∈ F` into `S' ∪ F_sub` drops `f`
    by at most `M` (`(f A - f (insert t A)) * K ≤ M`), then `(f S' - f (S' ∪ F)) * K ≤ F.card * M`. -/
lemma sub_mul_le_card_mul_of_insert_step {T : Type*} [DecidableEq T]
    (f : Finset T → ℕ) (S' F : Finset T) (K M : ℕ)
    (h_step : ∀ (A : Finset T) (t : T), S' ⊆ A → A ⊆ S' ∪ F → t ∈ F → t ∉ A →
      (f A - f (insert t A)) * K ≤ M) :
    (f S' - f (S' ∪ F)) * K ≤ F.card * M := by
  induction F using Finset.induction_on with
  | empty => simp
  | @insert t0 F ht0_not_mem ih =>
    have h_ih : (f S' - f (S' ∪ F)) * K ≤ F.card * M := by
      refine ih (fun A t hS'A hA_sub htF htA => h_step A t hS'A ?_ (Finset.mem_insert_of_mem htF) htA)
      exact Finset.Subset.trans hA_sub (Finset.union_subset_union_right (Finset.subset_insert t0 F))
    by_cases ht0_in : t0 ∈ S' ∪ F
    · have h_union_eq : S' ∪ insert t0 F = S' ∪ F := by
        rw [Finset.union_insert, Finset.insert_eq_of_mem ht0_in]
      rw [h_union_eq, Finset.card_insert_of_notMem ht0_not_mem]
      calc (f S' - f (S' ∪ F)) * K ≤ F.card * M := h_ih
        _ ≤ (F.card + 1) * M := Nat.mul_le_mul_right M (Nat.le_succ _)
    · have h_union_eq : S' ∪ insert t0 F = insert t0 (S' ∪ F) := Finset.union_insert t0 S' F
      have h_top := h_step (S' ∪ F) t0 Finset.subset_union_left
        (Finset.union_subset_union_right (Finset.subset_insert t0 F)) (Finset.mem_insert_self t0 F) ht0_in
      rw [h_union_eq, Finset.card_insert_of_notMem ht0_not_mem, Nat.add_mul, Nat.one_mul]
      have h_sub_add : f S' - f (insert t0 (S' ∪ F)) ≤ (f S' - f (S' ∪ F)) + (f (S' ∪ F) - f (insert t0 (S' ∪ F))) := by
        omega
      calc (f S' - f (insert t0 (S' ∪ F))) * K
        _ ≤ ((f S' - f (S' ∪ F)) + (f (S' ∪ F) - f (insert t0 (S' ∪ F)))) * K := Nat.mul_le_mul_right K h_sub_add
        _ = (f S' - f (S' ∪ F)) * K + (f (S' ∪ F) - f (insert t0 (S' ∪ F))) * K := Nat.add_mul _ _ K
        _ ≤ F.card * M + M := Nat.add_le_add h_ih h_top

end WeldedHierarchy
