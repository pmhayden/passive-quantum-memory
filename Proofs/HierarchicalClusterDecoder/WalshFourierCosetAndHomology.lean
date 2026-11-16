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

import Proofs.HierarchicalClusterDecoder.DecoderDefsAndCellGrowth

/-!
# Walsh-Fourier Coset Dominance and Unique Logical Homology Preservation

Proves the F2 Walsh-Fourier character expansion and positive-cone coset dominance inequality (`coset_syndromeWeight_sum_le`) together with subsupport weight peeling (`syndromeWeight_peel_of_subsupport`). Defines `HasUniqueLogicalHomology`, verifies it on the [[5, 1, 2]] planar seed code (`hasUniqueLogicalHomology_surfaceSeed`), and bounds primal cylinder check fibers (`card_fiber_stepXMXOwnerX_le_bdlSingleStepFactor`).

## References

* Part I, Section 2.1 (`subsec:css-complexes`), Lemma 2.3 (`lem:seed-code`)
* Part I, Section 5.3 (`subsec:walsh-fourier-peierls`), Theorem 5.5 (`thm:walsh-fourier-peierls`)
* Part II, Section 3.3 (`subsec:walsh-coset-peeling`), Proposition 3.6 (`prop:walsh-coset-dominance`)
* Part II, Section 4 (`subsec:welded-hierarchy-cleaner`), Lemma 4.1 (`lem:seed-code`)
-/

noncomputable section

open scoped Classical
open BigOperators

namespace WeldedHierarchy

/-! ## 1. Syndrome Support Peeling and Range Invariance -/

/-- Over `ZMod 2`, `x + (y + x) = y`. -/
lemma zmod2_peel_add_cancel (x y : ZMod 2) : x + (y + x) = y := by
  revert x y; decide

/-- Splits a sum of `ZMod.val` indicator weights over a filter when supports are disjoint. -/
lemma sum_zmod2_eq_of_disjoint_filter (x y : ZMod 2) (h_sub : x ≠ 0 → y ≠ 0) :
    ¬ (x ≠ 0 ∧ y + x ≠ 0) := by
  revert x y h_sub; decide

/-- Additivity of `ZMod.val` weight sums over disjoint support subsets. -/
lemma sum_zmod2_union_eq_add_of_disjoint (x y : ZMod 2) (h_sub : x ≠ 0 → y ≠ 0) :
    (y ≠ 0) ↔ (x ≠ 0 ∨ y + x ≠ 0) := by
  revert x y h_sub; decide

/-- **Exact `ZMod 2` Coboundary Peeling Weight Additivity (`syndromeWeight_peel_of_subsupport`):** -/
theorem syndromeWeight_peel_of_subsupport {M_X : Type} [Fintype M_X] [DecidableEq M_X]
    (s c : M_X → ZMod 2) (h_sub : ∀ m : M_X, c m ≠ 0 → s m ≠ 0) :
    s = c + (s + c) ∧ syndromeWeight s = syndromeWeight c + syndromeWeight (s + c) := by
  refine ⟨?_, ?_⟩
  · ext m
    exact (zmod2_peel_add_cancel (c m) (s m)).symm
  · dsimp [syndromeWeight]
    let A := Finset.univ.filter (fun m : M_X => c m ≠ 0)
    let B := Finset.univ.filter (fun m : M_X => (s + c) m ≠ 0)
    have h_disj : Disjoint A B := by
      rw [Finset.disjoint_filter]
      intro m _ hc hsc
      exact sum_zmod2_eq_of_disjoint_filter (c m) (s m) (h_sub m) ⟨hc, hsc⟩
    have h_union : Finset.univ.filter (fun m : M_X => s m ≠ 0) = A ∪ B := by
      ext m
      simp only [A, B, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and, Pi.add_apply]
      exact sum_zmod2_union_eq_add_of_disjoint (c m) (s m) (h_sub m)
    rw [h_union, Finset.card_union_of_disjoint h_disj, Nat.cast_add]
    rfl

/-- If `s` is a valid syndrome in `Set.range (syndrome code)`, adding `syndrome code e'` preserves membership. -/
lemma mem_image_syndrome_add {Q M_Z M_X : Type}
    [Fintype Q] [DecidableEq Q] [Fintype M_Z] [DecidableEq M_Z] [Fintype M_X] [DecidableEq M_X]
    (code : CSSCode3D Q M_Z M_X) {s c : M_X → ZMod 2}
    (hs : s ∈ Finset.univ.image (syndrome code))
    (hc : c ∈ Finset.univ.image (syndrome code)) :
    s + c ∈ Finset.univ.image (syndrome code) := by
  rw [Finset.mem_image] at hs hc ⊢
  rcases hs with ⟨es, _, rfl⟩
  rcases hc with ⟨ec, _, rfl⟩
  exact ⟨es + ec, Finset.mem_univ _, map_add (syndrome code) es ec⟩

/-- Any syndrome arising from an error in `decoderFailureSet` lies in `Finset.univ.image (syndrome code)`. -/
lemma mem_image_syndrome_of_mem_decoderFailureSet {Q M_Z M_X : Type}
    [Fintype Q] [DecidableEq Q] [Fintype M_Z] [DecidableEq M_Z] [Fintype M_X] [DecidableEq M_X]
    (code : CSSCode3D Q M_Z M_X) (dec : Decoder code) {s : M_X → ZMod 2}
    (hs : s ∈ decoderFailureSet code dec) :
    s ∈ Finset.univ.image (syndrome code) := by
  rw [Finset.mem_image]
  rcases hs.1 with ⟨e_err, rfl⟩
  exact ⟨e_err, Finset.mem_univ e_err, rfl⟩

/-- Every element of `ZMod 2` is either `0` or `1`. -/
lemma zmod2_eq_zero_or_one (x : ZMod 2) : x = 0 ∨ x = 1 := by
  revert x; decide

/-! ## 2. Fourier Characters on ZMod 2 and the Boltzmann Coset Inequality -/

/-- 1-bit character `(-1)^z` on `ZMod 2`. -/
def zmod2Char (z : ZMod 2) : ℝ :=
  if z = 0 then 1 else -1

/-- Multiplicativity of `zmod2Char`: `zmod2Char (x + y) = zmod2Char x * zmod2Char y`. -/
lemma zmod2Char_add (x y : ZMod 2) :
    zmod2Char (x + y) = zmod2Char x * zmod2Char y := by
  have h10 : (1 : ZMod 2) ≠ 0 := by decide
  have h11 : (1 + 1 : ZMod 2) = 0 := by decide
  rcases zmod2_eq_zero_or_one x with rfl | rfl <;>
    rcases zmod2_eq_zero_or_one y with rfl | rfl <;>
    simp [zmod2Char, h10, h11]

/-- Subset Walsh-Hadamard character `χ_T(v) = ∏_{m ∈ T} (-1)^{v(m)}`. -/
def subsetChar {M_X : Type} (T : Finset M_X) (v : M_X → ZMod 2) : ℝ :=
  ∏ m ∈ T, zmod2Char (v m)

/-- Multiplicativity of the Fourier character `subsetChar T` under syndrome addition. -/
lemma subsetChar_add {M_X : Type} (T : Finset M_X) (v1 v2 : M_X → ZMod 2) :
    subsetChar T (v1 + v2) = subsetChar T v1 * subsetChar T v2 := by
  dsimp [subsetChar]
  rw [← Finset.prod_mul_distrib]
  exact Finset.prod_congr rfl (fun m _ => zmod2Char_add (v1 m) (v2 m))

/-- Every Fourier character value satisfies `(subsetChar T s)^2 = 1`. -/
lemma subsetChar_sq_eq_one {M_X : Type} (T : Finset M_X) (v : M_X → ZMod 2) :
    subsetChar T v * subsetChar T v = 1 := by
  rw [← subsetChar_add]
  have hv : v + v = 0 := by ext m; exact zmod2_add_self (v m)
  rw [hv]
  dsimp [subsetChar, zmod2Char]
  simp

/-- Every Fourier character value satisfies `subsetChar T s ≤ 1`. -/
lemma subsetChar_le_one {M_X : Type} (T : Finset M_X) (v : M_X → ZMod 2) :
    subsetChar T v ≤ 1 := by
  have hsq := subsetChar_sq_eq_one T v
  have h_nonneg : 0 ≤ (subsetChar T v - 1) ^ 2 := sq_nonneg _
  nlinarith

/-- Nonnegativity of the Fourier character sum over the subgroup `Set.range (syndrome code)`. -/
lemma sum_subsetChar_image_syndrome_nonneg {Q M_Z M_X : Type}
    [Fintype Q] [DecidableEq Q] [Fintype M_Z] [DecidableEq M_Z] [Fintype M_X] [DecidableEq M_X]
    (code : CSSCode3D Q M_Z M_X) (T : Finset M_X) :
    0 ≤ ∑ u ∈ Finset.univ.image (syndrome code), subsetChar T u := by
  let W := Finset.univ.image (syndrome code)
  let S := ∑ u ∈ W, subsetChar T u
  have h_shift : ∀ u1 ∈ W, ∑ u ∈ W, subsetChar T (u1 + u) = S := by
    intro u1 hu1
    refine Finset.sum_bij (fun u _ => u1 + u) ?_ ?_ ?_ ?_
    · intro u hu; exact mem_image_syndrome_add code hu1 hu
    · intro a _ b _ hab
      ext m
      have hm := congr_fun hab m
      (try dsimp at hm)
      have h_cancel : ∀ z x y : ZMod 2, z + x = z + y → x = y := by decide
      exact h_cancel (u1 m) (a m) (b m) hm
    · intro b hb
      refine ⟨u1 + b, mem_image_syndrome_add code hu1 hb, ?_⟩
      ext m; simp [← add_assoc, zmod2_add_self]
    · intro u _; rfl
  have h_mul : ∀ u1 ∈ W, subsetChar T u1 * S = S := by
    intro u1 hu1
    calc subsetChar T u1 * S
      _ = ∑ u ∈ W, subsetChar T u1 * subsetChar T u := Finset.mul_sum _ _ _
      _ = ∑ u ∈ W, subsetChar T (u1 + u) :=
          Finset.sum_congr rfl (fun u _ => (subsetChar_add T u1 u).symm)
      _ = S := h_shift u1 hu1
  have h_sq : S * S = (W.card : ℝ) * S := by
    calc S * S
      _ = ∑ u1 ∈ W, subsetChar T u1 * S := Finset.sum_mul _ _ _
      _ = ∑ _u1 ∈ W, S := Finset.sum_congr rfl h_mul
      _ = (W.card : ℝ) * S := by rw [Finset.sum_const, nsmul_eq_mul]
  have h0_mem : (0 : M_X → ZMod 2) ∈ W := by
    rw [Finset.mem_image]
    exact ⟨0, Finset.mem_univ _, map_zero (syndrome code)⟩
  have hW_pos : (0 : ℝ) < W.card := by
    exact_mod_cast Finset.card_pos.mpr ⟨0, h0_mem⟩
  have hS_sq_nonneg : 0 ≤ S * S := mul_self_nonneg S
  nlinarith

/-- Fourier expansion of the Boltzmann factor `exp(-β |s|)` in terms of `subsetChar T s`. -/
lemma exp_neg_beta_syndromeWeight_eq_sum_subsetChar {M_X : Type} [Fintype M_X] [DecidableEq M_X]
    (β : ℝ) (v : M_X → ZMod 2) :
    let a := (1 + Real.exp (-β)) / 2
    let b := (1 - Real.exp (-β)) / 2
    Real.exp (-β * syndromeWeight v) =
      ∑ T ∈ (Finset.univ : Finset M_X).powerset,
        (b ^ T.card * a ^ ((Finset.univ : Finset M_X) \ T).card) * subsetChar T v := by
  intro a b
  have h_wt : -β * syndromeWeight v =
      ∑ m : M_X, (-β * if v m ≠ 0 then (1 : ℝ) else 0) := by
    dsimp [syndromeWeight]
    rw [← Finset.mul_sum, Finset.sum_boole]
  have h_factor : ∀ m : M_X,
      Real.exp (-β * if v m ≠ 0 then (1 : ℝ) else 0) = b * zmod2Char (v m) + a := by
    intro m
    dsimp [a, b, zmod2Char]
    have h10 : (1 : ZMod 2) ≠ 0 := by decide
    rcases zmod2_eq_zero_or_one (v m) with hm | hm <;> simp [hm, h10] <;> ring
  rw [h_wt, Real.exp_sum]
  have h_prod : (∏ m : M_X, Real.exp (-β * if v m ≠ 0 then (1 : ℝ) else 0)) =
      ∏ m : M_X, (b * zmod2Char (v m) + a) :=
    Finset.prod_congr rfl (fun m _ => h_factor m)
  rw [h_prod, Finset.prod_add]
  apply Finset.sum_congr rfl
  intro T _
  have h_T : (∏ m ∈ T, (b * zmod2Char (v m))) = b ^ T.card * subsetChar T v := by
    rw [Finset.prod_mul_distrib, Finset.prod_const]
    rfl
  have h_comp : (∏ _m ∈ (Finset.univ : Finset M_X) \ T, a) = a ^ ((Finset.univ : Finset M_X) \ T).card :=
    Finset.prod_const a
  rw [h_T, h_comp]
  ring

/-- **Walsh-Hadamard Coset Inequality (`coset_syndromeWeight_sum_le`):** -/
lemma coset_syndromeWeight_sum_le {Q M_Z M_X : Type}
    [Fintype Q] [DecidableEq Q] [Fintype M_Z] [DecidableEq M_Z] [Fintype M_X] [DecidableEq M_X]
    (code : CSSCode3D Q M_Z M_X) (β : ℝ) (hβ : 0 ≤ β) (c : M_X → ZMod 2) :
    ∑ u ∈ Finset.univ.image (syndrome code), Real.exp (-β * syndromeWeight (c + u)) ≤
      ∑ u ∈ Finset.univ.image (syndrome code), Real.exp (-β * syndromeWeight u) := by
  let W := Finset.univ.image (syndrome code)
  let a := (1 + Real.exp (-β)) / 2
  let b := (1 - Real.exp (-β)) / 2
  have hexp_le : Real.exp (-β) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
  have hexp_pos : 0 < Real.exp (-β) := Real.exp_pos _
  have ha_nonneg : 0 ≤ a := by dsimp [a]; linarith
  have hb_nonneg : 0 ≤ b := by dsimp [b]; linarith
  have h_lhs : (∑ u ∈ W, Real.exp (-β * syndromeWeight (c + u))) =
      ∑ T ∈ (Finset.univ : Finset M_X).powerset,
        (b ^ T.card * a ^ ((Finset.univ : Finset M_X) \ T).card) *
          (subsetChar T c * ∑ u ∈ W, subsetChar T u) := by
    trans (∑ u ∈ W, ∑ T ∈ (Finset.univ : Finset M_X).powerset,
      (b ^ T.card * a ^ ((Finset.univ : Finset M_X) \ T).card) * subsetChar T (c + u))
    · exact Finset.sum_congr rfl (fun u _ => exp_neg_beta_syndromeWeight_eq_sum_subsetChar β (c + u))
    · rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro T _
      simp_rw [subsetChar_add T c, ← mul_assoc, ← Finset.mul_sum]
  have h_rhs : (∑ u ∈ W, Real.exp (-β * syndromeWeight u)) =
      ∑ T ∈ (Finset.univ : Finset M_X).powerset,
        (b ^ T.card * a ^ ((Finset.univ : Finset M_X) \ T).card) *
          (∑ u ∈ W, subsetChar T u) := by
    trans (∑ u ∈ W, ∑ T ∈ (Finset.univ : Finset M_X).powerset,
      (b ^ T.card * a ^ ((Finset.univ : Finset M_X) \ T).card) * subsetChar T u)
    · exact Finset.sum_congr rfl (fun u _ => exp_neg_beta_syndromeWeight_eq_sum_subsetChar β u)
    · rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro T _
      rw [← Finset.mul_sum]
  rw [h_lhs, h_rhs]
  apply Finset.sum_le_sum
  intro T _
  have h_coeff : 0 ≤ b ^ T.card * a ^ ((Finset.univ : Finset M_X) \ T).card :=
    mul_nonneg (pow_nonneg hb_nonneg _) (pow_nonneg ha_nonneg _)
  have h_sum_T : 0 ≤ ∑ u ∈ W, subsetChar T u := sum_subsetChar_image_syndrome_nonneg code T
  have h_c_le : subsetChar T c ≤ 1 := subsetChar_le_one T c
  have h_inner : subsetChar T c * (∑ u ∈ W, subsetChar T u) ≤ ∑ u ∈ W, subsetChar T u := by
    nlinarith
  exact mul_le_mul_of_nonneg_left h_inner h_coeff

/-! ## 3. Unique Logical Homology and Seed/Perturbation Preservation -/

/-- **Unique 1D Logical Homology Package (`HasUniqueLogicalHomology`):** -/
structure HasUniqueLogicalHomology {Q M_Z M_X : Type}
    [Fintype Q] [DecidableEq Q] [Fintype M_Z] [DecidableEq M_Z] [Fintype M_X] [DecidableEq M_X]
    (code : CSSCode3D Q M_Z M_X) (L_Z L_X : Q → ZMod 2) : Prop where
  h_syn_Z : syndrome code L_Z = 0
  h_syn_X : syndrome (dualCode code) L_X = 0
  h_pair : dualPairing L_Z L_X = 1
  h_exact_Z : ∀ g : Q → ZMod 2, syndrome code g = 0 →
    ((∃ c2 : M_Z → ZMod 2, checkGen code c2 = g) ↔ dualPairing g L_X = 0)
  h_exact_X : ∀ h : Q → ZMod 2, syndrome (dualCode code) h = 0 →
    ((∃ d2 : M_X → ZMod 2, checkGen (dualCode code) d2 = h) ↔ dualPairing L_Z h = 0)

/-- Symmetry of `dualPairing` over `ZMod 2`. -/
lemma dualPairing_comm_zmod2 {Q : Type} [Fintype Q] (f g : Q → ZMod 2) :
    dualPairing f g = dualPairing g f := by
  dsimp [dualPairing]
  apply Finset.sum_congr rfl
  intro q _
  ring

/-- Right additivity of `dualPairing` over `ZMod 2`. -/
lemma dualPairing_add_right_zmod2 {Q : Type} [Fintype Q] (f g1 g2 : Q → ZMod 2) :
    dualPairing f (g1 + g2) = dualPairing f g1 + dualPairing f g2 := by
  change (∑ q : Q, f q * (g1 q + g2 q)) = (∑ q : Q, f q * g1 q) + (∑ q : Q, f q * g2 q)
  simp_rw [mul_add]
  exact Finset.sum_add_distrib

/-- Left additivity of `dualPairing` over `ZMod 2`. -/
lemma dualPairing_add_left_zmod2 {Q : Type} [Fintype Q] (f1 f2 g : Q → ZMod 2) :
    dualPairing (f1 + f2) g = dualPairing f1 g + dualPairing f2 g := by
  rw [dualPairing_comm_zmod2, dualPairing_add_right_zmod2, dualPairing_comm_zmod2 f1 g, dualPairing_comm_zmod2 f2 g]

/-- Negation equals identity on `α → ZMod 2`. -/
lemma neg_eq_self_zmod2_pi {α : Type} (f : α → ZMod 2) : -f = f := by
  ext x
  have h : ∀ a : ZMod 2, -a = a := by decide
  exact h (f x)

/-- Left scalar multiplication linearity of `dualPairing` over `ZMod 2`. -/
lemma dualPairing_smul_left_zmod2 {Q : Type} [Fintype Q] (a : ZMod 2) (f g : Q → ZMod 2) :
    dualPairing (fun q => a * f q) g = a * dualPairing f g := by
  dsimp [dualPairing]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro q _
  ring

/-- Right scalar multiplication linearity of `dualPairing` over `ZMod 2`. -/
lemma dualPairing_smul_right_zmod2 {Q : Type} [Fintype Q] (a : ZMod 2) (f g : Q → ZMod 2) :
    dualPairing f (fun q => a * g q) = a * dualPairing f g := by
  rw [dualPairing_comm_zmod2, dualPairing_smul_left_zmod2, dualPairing_comm_zmod2]

/-- Scalar multiplication linearity of `syndrome` over `ZMod 2`. -/
lemma syndrome_smul_zmod2 {Q M_Z M_X : Type}
    [Fintype Q] [DecidableEq Q] [Fintype M_Z] [DecidableEq M_Z] [Fintype M_X] [DecidableEq M_X]
    (code : CSSCode3D Q M_Z M_X) (a : ZMod 2) (f : Q → ZMod 2) :
    syndrome code (fun q => a * f q) = fun m => a * syndrome code f m := by
  ext m
  dsimp [syndrome, f2Syndrome]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro q _
  ring

/-- Constructs `HasUniqueLogicalHomology` from dual exactness (`h_exact_X`) via `mem_of_dualPairing_ortho`. -/
lemma hasUniqueLogicalHomology_of_exact_X {Q M_Z M_X : Type}
    [Fintype Q] [DecidableEq Q] [Fintype M_Z] [DecidableEq M_Z] [Fintype M_X] [DecidableEq M_X]
    (code : CSSCode3D Q M_Z M_X) (L_Z L_X : Q → ZMod 2)
    (h_syn_Z : syndrome code L_Z = 0)
    (h_syn_X : syndrome (dualCode code) L_X = 0)
    (h_pair : dualPairing L_Z L_X = 1)
    (h_exact_X : ∀ h : Q → ZMod 2, syndrome (dualCode code) h = 0 →
      ((∃ d2 : M_X → ZMod 2, checkGen (dualCode code) d2 = h) ↔ dualPairing L_Z h = 0)) :
    HasUniqueLogicalHomology code L_Z L_X := by
  refine ⟨h_syn_Z, h_syn_X, h_pair, ?_, h_exact_X⟩
  intro g hg_syn
  constructor
  · rintro ⟨c2, rfl⟩
    rw [dualPairing_checkGen_primal, h_syn_X]
    dsimp [dualPairing]
    simp
  · intro hg_pair
    let W : Submodule (ZMod 2) (Q → ZMod 2) :=
      { carrier := {f | ∃ c2 : M_Z → ZMod 2, checkGen code c2 = f}
        add_mem' := by
          rintro _ _ ⟨c1, rfl⟩ ⟨c2, rfl⟩
          exact ⟨c1 + c2, map_add (checkGen code) c1 c2⟩
        zero_mem' := ⟨0, map_zero (checkGen code)⟩
        smul_mem' := by
          rintro a _ ⟨c, rfl⟩
          fin_cases a
          · exact ⟨0, by erw [zero_smul, map_zero]⟩
          · exact ⟨c, by erw [one_smul]⟩ }
    change g ∈ W
    apply mem_of_dualPairing_ortho W g
    intro h hh_ortho
    have hh_syn : syndrome (dualCode code) h = 0 := by
      ext mZ
      have h_mem : checkGen code (singleQubit mZ) ∈ W := ⟨singleQubit mZ, rfl⟩
      have h_p := hh_ortho (checkGen code (singleQubit mZ)) h_mem
      rw [dualPairing_checkGen_primal, Finset.sum_eq_single mZ] at h_p
      · simpa [singleQubit] using h_p
      · intro mZ' _ hne; simp [singleQubit, hne]
      · intro h_abs; exact False.elim (h_abs (Finset.mem_univ mZ))
    let a := dualPairing L_Z h
    let h' : Q → ZMod 2 := fun q => h q + a * L_X q
    have hh'_syn : syndrome (dualCode code) h' = 0 := by
      change syndrome (dualCode code) (h + fun q => a * L_X q) = 0
      rw [map_add, hh_syn, zero_add, syndrome_smul_zmod2, h_syn_X]
      ext; simp
    have hh'_pair : dualPairing L_Z h' = 0 := by
      change dualPairing L_Z (h + fun q => a * L_X q) = 0
      rw [dualPairing_add_right_zmod2, dualPairing_smul_right_zmod2, h_pair, mul_one]
      exact zmod2_add_self a
    obtain ⟨d2, hd2⟩ := (h_exact_X h' hh'_syn).mpr hh'_pair
    have hg_h' : dualPairing g h' = 0 := by
      rw [← hd2, dualPairing_checkGen_dual, hg_syn]
      dsimp [dualPairing]
      simp
    have hg_decomp : dualPairing g h' = dualPairing g h + a * dualPairing g L_X := by
      change dualPairing g (h + fun q => a * L_X q) = _
      rw [dualPairing_add_right_zmod2, dualPairing_smul_right_zmod2]
    rw [hg_pair, mul_zero, add_zero] at hg_decomp
    exact hg_decomp.symm.trans hg_h'

/-- Decomposes any Z-cycle of `bdlSurfaceSeedCode` into a Z-boundary plus a scalar multiple of `surfaceLZ`. -/
lemma eq_checkGen_add_smul_surfaceLZ_of_syndrome_zero :
    ∀ h : Fin 5 → ZMod 2,
      (∀ m : Fin 2, syndrome (dualCode bdlSurfaceSeedCode) h m = 0) →
      ((∃ d2 : Fin 2 → ZMod 2, ∀ q : Fin 5, checkGen (dualCode bdlSurfaceSeedCode) d2 q = h q) ↔
        dualPairing surfaceLZ h = 0) := by
  decide

/-- Establishes `HasUniqueLogicalHomology` for the surface seed code `bdlSurfaceSeedCode`. -/
lemma hasUniqueLogicalHomology_surfaceSeed :
    HasUniqueLogicalHomology bdlSurfaceSeedCode surfaceLZ surfaceLX := by
  have h_pair : dualPairing surfaceLZ surfaceLX = 1 := by decide
  apply hasUniqueLogicalHomology_of_exact_X bdlSurfaceSeedCode surfaceLZ surfaceLX
    surfaceLZ_syndrome surfaceLX_syndrome h_pair
  intro h hh_syn
  have hh_syn' : ∀ m : Fin 2, syndrome (dualCode bdlSurfaceSeedCode) h m = 0 :=
    fun m => congr_fun hh_syn m
  have h_iff := eq_checkGen_add_smul_surfaceLZ_of_syndrome_zero h hh_syn'
  simpa [funext_iff] using h_iff

/-- Preservation of `HasUniqueLogicalHomology` across `bdlPerturbStep`. -/
lemma hasUniqueLogicalHomology_bdlPerturbStep {Q M_Z M_X : Type}
    [Fintype Q] [DecidableEq Q] [Fintype M_Z] [DecidableEq M_Z] [Fintype M_X] [DecidableEq M_X]
    {code : CSSCode3D Q M_Z M_X} {lam : ℕ}
    {cQ : Q → Point3D} {cZ : M_Z → Point3D} {cX : M_X → Point3D}
    {L_Z L_X : Q → ZMod 2}
    (h_hom : HasUniqueLogicalHomology code L_Z L_X) :
    HasUniqueLogicalHomology (bdlPerturbStep code lam cQ cZ cX) L_Z L_X where
  h_syn_Z := h_hom.h_syn_Z
  h_syn_X := h_hom.h_syn_X
  h_pair := h_hom.h_pair
  h_exact_Z := h_hom.h_exact_Z
  h_exact_X := h_hom.h_exact_X

/-! ## 4. X-Check Fiber Owner Cardinality Bounds -/

/-- Auxiliary declaration `boundaryX0LinkFiberToSum` in the BDL cluster decoder. -/
noncomputable def boundaryX0LinkFiberToSum {Q M_Z M_X : Type}
    [Fintype Q] [DecidableEq Q] [Fintype M_Z] [DecidableEq M_Z] [Fintype M_X] [DecidableEq M_X]
    (pcode : CSSCode3D Q M_Z M_X) (M : ℕ) (x0 : M_X) :
    {xv : BoundaryX0Link pcode M // xv.val.1 = x0} →
      {q : Q // pcode.checkX x0 q ≠ 0} ⊕
      ({s : ActiveSimplex2 pcode // s.val.1 = x0} × Fin M) ⊕
      {s : ActiveSimplex2 pcode // s.val.1 = x0}
  | ⟨⟨(_, Sum.inl q), h⟩, hx⟩ => Sum.inl ⟨q, hx ▸ h⟩
  | ⟨⟨(x, Sum.inr (Sum.inl (eZ, j))), h⟩, hx⟩ =>
      Sum.inr (Sum.inl (⟨⟨(x, eZ.val.1, eZ.val.2), ⟨h, eZ.property⟩⟩, hx⟩, j))
  | ⟨⟨(x, Sum.inr (Sum.inr z)), h⟩, hx⟩ =>
      Sum.inr (Sum.inr ⟨⟨(x, Classical.choose h, z), Classical.choose_spec h⟩, hx⟩)

/-- Proves that `boundaryX0LinkFiberToSum pcode M x0` is injective on the fiber over `x0`. -/
lemma boundaryX0LinkFiberToSum_injective {Q M_Z M_X : Type}
    [Fintype Q] [DecidableEq Q] [Fintype M_Z] [DecidableEq M_Z] [Fintype M_X] [DecidableEq M_X]
    (pcode : CSSCode3D Q M_Z M_X) (M : ℕ) (x0 : M_X) :
    Function.Injective (boundaryX0LinkFiberToSum pcode M x0) := by
  rintro ⟨⟨⟨x1, q1 | ⟨⟨eZ1, j1⟩ | z1⟩⟩, h1⟩, hx1⟩ ⟨⟨⟨x2, q2 | ⟨⟨eZ2, j2⟩ | z2⟩⟩, h2⟩, hx2⟩ h <;>
    dsimp [boundaryX0LinkFiberToSum] at h hx1 hx2
  · injection h with h_eq
    have hq : q1 = q2 := congr_arg Subtype.val h_eq
    have hx : x1 = x2 := hx1.trans hx2.symm
    subst hx hq; rfl
  · nomatch h
  · nomatch h
  · nomatch h
  · injection h with h_inr
    injection h_inr with h_prod
    have hx : x1 = x2 := hx1.trans hx2.symm
    have hq : eZ1.val.1 = eZ2.val.1 :=
      congr_arg (fun u : {s : ActiveSimplex2 pcode // s.val.1 = x0} × Fin M => u.1.val.val.2.1) h_prod
    have hz : eZ1.val.2 = eZ2.val.2 :=
      congr_arg (fun u : {s : ActiveSimplex2 pcode // s.val.1 = x0} × Fin M => u.1.val.val.2.2) h_prod
    have heZ : eZ1 = eZ2 := Subtype.ext (Prod.ext hq hz)
    have hj : j1 = j2 := congr_arg Prod.snd h_prod
    subst hx heZ hj; rfl
  · nomatch h
  · nomatch h
  · nomatch h
  · injection h with h_inr
    injection h_inr with h_simp
    have hx : x1 = x2 := hx1.trans hx2.symm
    have hz : z1 = z2 :=
      congr_arg (fun u : {s : ActiveSimplex2 pcode // s.val.1 = x0} => u.val.val.2.2) h_simp
    subst hx hz; rfl

/-- Auxiliary declaration `shellVertexFiberToProd` in the BDL cluster decoder. -/
def shellVertexFiberToProd {Q M_Z M_X : Type}
    [Fintype Q] [DecidableEq Q] [Fintype M_Z] [DecidableEq M_Z] [Fintype M_X] [DecidableEq M_X]
    (pcode : CSSCode3D Q M_Z M_X) (M : ℕ) (x0 : M_X) :
    {sv : ShellVertex pcode M // sv.val.1.val.1 = x0} →
      {xv : BoundaryX0Link pcode M // xv.val.1 = x0} × Fin (M + 1)
  | ⟨⟨(xv, r), _⟩, hx⟩ => (⟨xv, hx⟩, r)

/-- Proves that `shellVertexFiberToProd pcode M x0` is injective on the shell-vertex fiber over `x0`. -/
lemma shellVertexFiberToProd_injective {Q M_Z M_X : Type}
    [Fintype Q] [DecidableEq Q] [Fintype M_Z] [DecidableEq M_Z] [Fintype M_X] [DecidableEq M_X]
    (pcode : CSSCode3D Q M_Z M_X) (M : ℕ) (x0 : M_X) :
    Function.Injective (shellVertexFiberToProd pcode M x0) := by
  rintro ⟨⟨⟨xv1, r1⟩, h1⟩, hx1⟩ ⟨⟨⟨xv2, r2⟩, h2⟩, hx2⟩ h
  dsimp [shellVertexFiberToProd] at h
  have hxv : xv1 = xv2 :=
    congr_arg (fun u : {xv : BoundaryX0Link pcode M // xv.val.1 = x0} × Fin (M + 1) => u.1.val) h
  have hr : r1 = r2 := congr_arg Prod.snd h
  subst hxv hr; rfl

/-- Auxiliary declaration `stepXMXFiberToSum` in the BDL cluster decoder. -/
def stepXMXFiberToSum {Q M_Z M_X : Type}
    [Fintype Q] [DecidableEq Q] [Fintype M_Z] [DecidableEq M_Z] [Fintype M_X] [DecidableEq M_X]
    (pcode : CSSCode3D Q M_Z M_X) (M : ℕ) (x0 : M_X) :
    {mX : BDLStepXMX pcode M // stepXMXOwnerX pcode M mX = x0} →
      Fin 3 ⊕ ({sv : ShellVertex pcode M // sv.val.1.val.1 = x0} × Fin 3)
  | ⟨Sum.inl (_, b), _⟩ => Sum.inl b
  | ⟨Sum.inr (sv, b), hx⟩ => Sum.inr (⟨sv, hx⟩, b)

/-- Proves that `stepXMXFiberToSum pcode M x0` is injective on the X-check fiber over `x0`. -/
lemma stepXMXFiberToSum_injective {Q M_Z M_X : Type}
    [Fintype Q] [DecidableEq Q] [Fintype M_Z] [DecidableEq M_Z] [Fintype M_X] [DecidableEq M_X]
    (pcode : CSSCode3D Q M_Z M_X) (M : ℕ) (x0 : M_X) :
    Function.Injective (stepXMXFiberToSum pcode M x0) := by
  rintro ⟨⟨x1, b1⟩ | ⟨sv1, b1⟩, hx1⟩ ⟨⟨x2, b2⟩ | ⟨sv2, b2⟩, hx2⟩ h <;>
    dsimp [stepXMXFiberToSum, stepXMXOwnerX] at h hx1 hx2
  · injection h with hb
    have hx : x1 = x2 := hx1.trans hx2.symm
    subst hx hb; rfl
  · nomatch h
  · nomatch h
  · injection h with h_prod
    have hsv : sv1 = sv2 :=
      congr_arg (fun u : {sv : ShellVertex pcode M // sv.val.1.val.1 = x0} × Fin 3 => u.1.val) h_prod
    have hb : b1 = b2 := congr_arg Prod.snd h_prod
    subst hsv hb; rfl

/-- Bounds the cardinality of the `stepXMXOwnerX` fiber over any `x0 : B.M_X` by `bdlSingleStepFactor`. -/
lemma card_fiber_stepXMXOwnerX_le_bdlSingleStepFactor (B : BundledCSSCode3D)
    (hdeg : HasBoundedCheckDegree B 8 8 4 4)
    (hsimp : HasBoundedSimplexDegreeD B 32)
    {lam : ℕ} {cQ : B.Q → Point3D} {cZ : B.M_Z → Point3D} {cX : B.M_X → Point3D}
    (x0 : B.M_X) :
    let pcode := bdlPerturbStep B.code lam cQ cZ cX
    (Finset.univ.filter (fun mX : BDLStepXMX pcode bdlSubdivPred =>
      stepXMXOwnerX pcode bdlSubdivPred mX = x0)).card ≤ bdlSingleStepFactor := by
  intro pcode
  let M := bdlSubdivPred
  have h_q_card : Fintype.card {q : B.Q // pcode.checkX x0 q ≠ 0} ≤ 8 := by
    rw [Fintype.card_subtype]
    exact hdeg.1 x0
  have h_simp_card : Fintype.card {s : ActiveSimplex2 pcode // s.val.1 = x0} ≤ 32 := by
    rw [Fintype.card_subtype]
    exact hsimp.1 x0
  have h_bx : Fintype.card {xv : BoundaryX0Link pcode M // xv.val.1 = x0} ≤ 8 + 32 * M + 32 := by
    have h_inj := Fintype.card_le_of_injective (boundaryX0LinkFiberToSum pcode M x0)
      (boundaryX0LinkFiberToSum_injective pcode M x0)
    simp only [Fintype.card_sum, Fintype.card_prod, Fintype.card_fin] at h_inj
    nlinarith
  have h_sv : Fintype.card {sv : ShellVertex pcode M // sv.val.1.val.1 = x0} ≤
      (8 + 32 * M + 32) * (M + 1) := by
    have h_inj := Fintype.card_le_of_injective (shellVertexFiberToProd pcode M x0)
      (shellVertexFiberToProd_injective pcode M x0)
    simp only [Fintype.card_prod, Fintype.card_fin] at h_inj
    nlinarith
  have h_mx : Fintype.card {mX : BDLStepXMX pcode M // stepXMXOwnerX pcode M mX = x0} ≤
      3 + (8 + 32 * M + 32) * (M + 1) * 3 := by
    have h_inj := Fintype.card_le_of_injective (stepXMXFiberToSum pcode M x0)
      (stepXMXFiberToSum_injective pcode M x0)
    simp only [Fintype.card_sum, Fintype.card_prod, Fintype.card_fin] at h_inj
    nlinarith
  rw [← Fintype.card_subtype]
  have hM_eq : M + 1 = bdlSubdivM := bdlSubdivM_eq_succ
  have hM_ge : 2 ≤ M + 1 := by rw [hM_eq]; exact bdlSubdivM_ge_two
  dsimp [bdlSingleStepFactor, _root_.bdlSingleStepFactor]
  rw [← hM_eq]
  nlinarith

end WeldedHierarchy
