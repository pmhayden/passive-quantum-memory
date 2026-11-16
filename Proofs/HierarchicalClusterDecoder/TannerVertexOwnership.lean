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

import Proofs.HierarchicalClusterDecoder.WalshFourierCosetAndHomology

/-!
# Tanner Vertex Ownership Partitions and Coarse Cylinder Syndrome Maps

Defines the tripartite Tanner vertex type `TannerVertex`, cell-to-Tanner ownership maps (`stepXMZOwnerTanner`), and Tanner-restricted syndrome projections (`restrictStepXMZ`). Establishes exact intertwining between fine cylinder syndromes, coarse syndrome sums (`coarseSyndromeStepXMX_syndrome_eq`), and lifted logical Z-chains (`syndrome_liftCylinderLZ_eq_embedCoarse`).

## References

* Part I, Section 2.3 (`subsec:step2-mapping-cone`), Definition 2.5 (`def:three-layer-mapping-cone`)
* Part I, Section 4.1 (`subsec:cleaner-architecture`)
* Part I, Section 5.2 (`subsec:cluster-decoder`), Proposition 5.3 (`prop:cluster-decoder-witness`)
-/

noncomputable section

open scoped Classical
open BigOperators

namespace WeldedHierarchy
namespace BDLDecoder

/-! ## 1. Tanner Vertex Ownership and Z-Check Fiber Restriction -/

/-- Natural-number Hamming weight of a `ZMod 2` vector `s`, with `syndromeWeight s = (syndromeWeightNat s : ℝ)`. -/
def syndromeWeightNat {M : Type} [Fintype M] [DecidableEq M] (s : M → ZMod 2) : ℕ :=
  (Finset.univ.filter (fun m : M => s m ≠ 0)).card

/-- Expresses real-valued `syndromeWeight s` as the natural-number cast of `syndromeWeightNat s`. -/
lemma syndromeWeight_eq_natCast {M : Type} [Fintype M] [DecidableEq M] (s : M → ZMod 2) :
    syndromeWeight s = (syndromeWeightNat s : ℝ) := rfl

/-- For a CSS code on `(Q, M_Z, M_X)`, the Tanner graph vertex set is `V = M_X ⊕ Q ⊕ M_Z`. -/
abbrev TannerVertex (Q M_Z M_X : Type) : Type := M_X ⊕ Q ⊕ M_Z

/-- Embedding `x ∈ V_X` into `TannerVertex Q M_Z M_X`. -/
def inVX {Q M_Z M_X : Type} (x : M_X) : TannerVertex Q M_Z M_X := Sum.inl x

/-- Embedding `q ∈ V_Q` into `TannerVertex Q M_Z M_X`. -/
def inVQ {Q M_Z M_X : Type} (q : Q) : TannerVertex Q M_Z M_X := Sum.inr (Sum.inl q)

/-- Embedding `z ∈ V_Z` into `TannerVertex Q M_Z M_X`. -/
def inVZ {Q M_Z M_X : Type} (z : M_Z) : TannerVertex Q M_Z M_X := Sum.inr (Sum.inr z)

/-- Local subcomplex owner in `V_X` for a 1-cell `qX ∈ BDLCX1 pcode M`. -/
def cX1OwnerX {Q M_Z M_X : Type}
    [Fintype Q] [DecidableEq Q] [Fintype M_Z] [DecidableEq M_Z] [Fintype M_X] [DecidableEq M_X]
    (pcode : CSSCode3D Q M_Z M_X) (M : ℕ) :
    BDLCX1 pcode M → M_X
  | Sum.inl (rv, _) => rv.val.val.1.val.1
  | Sum.inr (Sum.inl (seg, _)) => seg.val.1.val.1
  | Sum.inr (Sum.inr (xv, _)) => xv.val.1

/-- Local subcomplex owner in `V_Q` for a 1-cell `qQ ∈ BDLCQ1 pcode M`. -/
def cQ1OwnerQ {Q M_Z M_X : Type}
    [Fintype Q] [DecidableEq Q] [Fintype M_Z] [DecidableEq M_Z] [Fintype M_X] [DecidableEq M_X]
    (pcode : CSSCode3D Q M_Z M_X) (M : ℕ) :
    BDLCQ1 pcode M → Q
  | (v0, _) => xq0OwnerQ pcode M v0

/-- Active link face owner `lZ : ActiveZLink pcode` for a 2-cell `cX2 ∈ BDLCX2 pcode M`. -/
def cX2OwnerLink {Q M_Z M_X : Type}
    [Fintype Q] [DecidableEq Q] [Fintype M_Z] [DecidableEq M_Z] [Fintype M_X] [DecidableEq M_X]
    (pcode : CSSCode3D Q M_Z M_X) (M : ℕ) :
    BDLCX2 pcode M → ActiveZLink pcode
  | Sum.inl (seg, _) => seg.val.1
  | Sum.inr (lZ, _, _) => lZ

/-- Local subcomplex owner in `V_X` for a 2-cell `cX2 ∈ BDLCX2 pcode M`. -/
def cX2OwnerX {Q M_Z M_X : Type}
    [Fintype Q] [DecidableEq Q] [Fintype M_Z] [DecidableEq M_Z] [Fintype M_X] [DecidableEq M_X]
    (pcode : CSSCode3D Q M_Z M_X) (M : ℕ)
    (cX2 : BDLCX2 pcode M) : M_X :=
  (cX2OwnerLink pcode M cX2).val.1

/-- Active arm owner `eZ : ActiveZ pcode` for a 2-cell `cQ2 ∈ BDLCQ2 pcode M`. -/
def cQ2OwnerActiveZ {Q M_Z M_X : Type}
    [Fintype Q] [DecidableEq Q] [Fintype M_Z] [DecidableEq M_Z] [Fintype M_X] [DecidableEq M_X]
    (pcode : CSSCode3D Q M_Z M_X) (M : ℕ) :
    BDLCQ2 pcode M → ActiveZ pcode
  | Sum.inl (eZ, _, _) => eZ
  | Sum.inr (eZ, _) => eZ

/-- Local subcomplex owner in `V_Q` for a 2-cell `cQ2 ∈ BDLCQ2 pcode M`. -/
def cQ2OwnerQ {Q M_Z M_X : Type}
    [Fintype Q] [DecidableEq Q] [Fintype M_Z] [DecidableEq M_Z] [Fintype M_X] [DecidableEq M_X]
    (pcode : CSSCode3D Q M_Z M_X) (M : ℕ)
    (cQ2 : BDLCQ2 pcode M) : Q :=
  (cQ2OwnerActiveZ pcode M cQ2).val.1

/-- Local subcomplex owner in `V_Z` for a 2-cell `cZ2 ∈ BDLCZ2 M_Z`. -/
def cZ2OwnerZ {M_Z : Type} (cZ2 : BDLCZ2 M_Z) : M_Z := cZ2.1

/-- Decomposition of `C^2(X_i) = ⨁_{v ∈ V} C^2(X_v)` via the Tanner vertex owner map. -/
def stepXMZOwnerTanner {Q M_Z M_X : Type}
    [Fintype Q] [DecidableEq Q] [Fintype M_Z] [DecidableEq M_Z] [Fintype M_X] [DecidableEq M_X]
    (pcode : CSSCode3D Q M_Z M_X) (M : ℕ) :
    BDLStepXMZ pcode M → TannerVertex Q M_Z M_X
  | Sum.inl cX2 => inVX (cX2OwnerX pcode M cX2)
  | Sum.inr (Sum.inl cQ2) => inVQ (cQ2OwnerQ pcode M cQ2)
  | Sum.inr (Sum.inr cZ2) => inVZ (cZ2OwnerZ cZ2)

/-- Restriction of a fine 2-cochain `S` to the subcomplex `X_K = ⋃_{v ∈ K} X_v`. -/
def restrictStepXMZ {Q M_Z M_X : Type}
    [Fintype Q] [DecidableEq Q] [Fintype M_Z] [DecidableEq M_Z] [Fintype M_X] [DecidableEq M_X]
    (pcode : CSSCode3D Q M_Z M_X) (M : ℕ) (K : Finset (TannerVertex Q M_Z M_X))
    (S : BDLStepXMZ pcode M → ZMod 2) (mZ : BDLStepXMZ pcode M) : ZMod 2 :=
  if stepXMZOwnerTanner pcode M mZ ∈ K then S mZ else 0

/-! ## 2. Coarse X-Syndrome Map R_Z and Symplectic Adjoint Identities -/

/-- Canonical embedding `embedCoarseStepXMX` of a coarse X-syndrome `S_coarse` at apex `(x0, 0)`. -/
def embedCoarseStepXMX {Q M_Z M_X : Type}
    [Fintype Q] [DecidableEq Q] [Fintype M_Z] [DecidableEq M_Z] [Fintype M_X] [DecidableEq M_X]
    (pcode : CSSCode3D Q M_Z M_X) (M : ℕ) (S_coarse : M_X → ZMod 2) :
    BDLStepXMX pcode M → ZMod 2
  | Sum.inl (x0, 0) => S_coarse x0
  | _ => 0

/-- Coarse-grained X-syndrome `coarseSyndromeStepXMX` on `M_X` obtained by summing over `Y_{x0}`. -/
def coarseSyndromeStepXMX {Q M_Z M_X : Type}
    [Fintype Q] [DecidableEq Q] [Fintype M_Z] [DecidableEq M_Z] [Fintype M_X] [DecidableEq M_X]
    (pcode : CSSCode3D Q M_Z M_X) (M : ℕ) (S : BDLStepXMX pcode M → ZMod 2) (x0 : M_X) : ZMod 2 :=
  ∑ mX ∈ Finset.univ.filter (fun mX : BDLStepXMX pcode M => stepXMXOwnerX pcode M mX = x0), S mX

/-- Single-subcomplex active point witness in `R_Z`. -/
lemma exists_active_in_fiber_of_coarseSyndromeStepXMX_ne_zero {Q M_Z M_X : Type}
    [Fintype Q] [DecidableEq Q] [Fintype M_Z] [DecidableEq M_Z] [Fintype M_X] [DecidableEq M_X]
    (pcode : CSSCode3D Q M_Z M_X) (M : ℕ) (S : BDLStepXMX pcode M → ZMod 2) (x0 : M_X)
    (hx0 : coarseSyndromeStepXMX pcode M S x0 ≠ 0) :
    ∃ mX : BDLStepXMX pcode M, stepXMXOwnerX pcode M mX = x0 ∧ S mX ≠ 0 := by
  by_contra h_none
  push_neg at h_none
  apply hx0
  dsimp [coarseSyndromeStepXMX]
  apply Finset.sum_eq_zero
  intro mX hmX
  rw [Finset.mem_filter] at hmX
  exact h_none mX hmX.2

/-- Adjoint identity in `BDLDecoder`: `dualPairing g (checkGen (dualCode code) d2) = dualPairing (syndrome code g) d2`. -/
lemma dualPairing_checkGen_dual_eq {Q M_Z M_X : Type}
    [Fintype Q] [DecidableEq Q] [Fintype M_Z] [DecidableEq M_Z] [Fintype M_X] [DecidableEq M_X]
    (code : CSSCode3D Q M_Z M_X) (g : Q → ZMod 2) (d2 : M_X → ZMod 2) :
    dualPairing g (checkGen (dualCode code) d2) = dualPairing (syndrome code g) d2 := by
  rw [dualPairing_checkGen_dual]
  dsimp [dualPairing]
  apply Finset.sum_congr rfl
  intro mX _
  ring

/-- Expresses `coarseSyndromeStepXMX pcode M S x0` as `dualPairing S (liftStepXMX pcode M (singleQubit x0))`. -/
lemma coarseSyndromeStepXMX_eq_dualPairing {Q M_Z M_X : Type}
    [Fintype Q] [DecidableEq Q] [Fintype M_Z] [DecidableEq M_Z] [Fintype M_X] [DecidableEq M_X]
    (pcode : CSSCode3D Q M_Z M_X) (M : ℕ) (S : BDLStepXMX pcode M → ZMod 2) (x0 : M_X) :
    coarseSyndromeStepXMX pcode M S x0 =
      dualPairing S (liftStepXMX pcode M (singleQubit x0)) := by
  dsimp [coarseSyndromeStepXMX, dualPairing, liftStepXMX, singleQubit]
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro mX _
  by_cases h : stepXMXOwnerX pcode M mX = x0
  · rw [if_pos h, if_pos h, mul_one]
  · rw [if_neg h, if_neg h, mul_zero]

/-- Adjointness between `projCylinderLZ` and `liftCylinderLX`. -/
lemma dualPairing_liftCylinderLX_right {Q M_Z M_X : Type}
    [Fintype Q] [DecidableEq Q] [Fintype M_Z] [DecidableEq M_Z] [Fintype M_X] [DecidableEq M_X]
    (pcode : CSSCode3D Q M_Z M_X) (M : ℕ)
    (g : BDLStepXQ pcode M → ZMod 2) (h : Q → ZMod 2) :
    dualPairing g (liftCylinderLX pcode M h) = dualPairing (projCylinderLZ pcode M g) h := by
  conv_lhs => rw [pi_eq_sum_singleQubit h]
  have h_lin : liftCylinderLX pcode M (∑ q : Q, h q • singleQubit q) =
      ∑ q : Q, h q • liftCylinderLX pcode M (singleQubit q) := by
    ext e
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    rcases e with _ | ⟨v0, _⟩
    · dsimp [liftCylinderLX]; simp
    · dsimp [liftCylinderLX]
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  rw [h_lin]
  dsimp [dualPairing, projCylinderLZ]
  simp_rw [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro q _
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro e _
  ring

/-! ## 3. Coarse X-Syndrome Commutation and Lifted Z-Chain Syndrome Identity -/

/-- Exact coarse-graining identity on `coarseSyndromeStepXMX`. -/
theorem coarseSyndromeStepXMX_syndrome_eq {Q M_Z M_X : Type}
    [Fintype Q] [DecidableEq Q] [Fintype M_Z] [DecidableEq M_Z] [Fintype M_X] [DecidableEq M_X]
    (pcode : CSSCode3D Q M_Z M_X) (M : ℕ) (e : BDLStepXQ pcode M → ZMod 2) :
    coarseSyndromeStepXMX pcode M (syndrome (bdlCylinderStepX pcode M) e) =
      syndrome pcode (projCylinderLZ pcode M e) := by
  ext x0
  rw [coarseSyndromeStepXMX_eq_dualPairing,
      ← dualPairing_checkGen_dual_eq (bdlCylinderStepX pcode M) e (liftStepXMX pcode M (singleQubit x0)),
      checkGen_dual_liftStepXMX,
      dualPairing_liftCylinderLX_right,
      dualPairing_checkGen_dual_eq pcode (projCylinderLZ pcode M e) (singleQubit x0),
      dualPairing_singleQubit_right]

/-- For ANY coarse 1-chain `L_Z : Q → ZMod 2`, the syndrome of `liftCylinderLZ pcode M L_Z`
    on `bdlCylinderStepX pcode M` is identically `embedCoarseStepXMX pcode M (syndrome pcode L_Z)`. -/
theorem syndrome_liftCylinderLZ_eq_embedCoarse {Q M_Z M_X : Type}
    [Fintype Q] [DecidableEq Q] [Fintype M_Z] [DecidableEq M_Z] [Fintype M_X] [DecidableEq M_X]
    (pcode : CSSCode3D Q M_Z M_X) (M : ℕ) (L_Z : Q → ZMod 2) :
    syndrome (bdlCylinderStepX pcode M) (liftCylinderLZ pcode M L_Z) =
      embedCoarseStepXMX pcode M (syndrome pcode L_Z) := by
  ext mX
  simp only [syndrome, f2Syndrome, bdlCylinderStepX, AddMonoidHom.coe_mk, ZeroHom.coe_mk]
  rw [Fintype.sum_sum_type]
  have h_qX : (∑ qX : BDLCX1 pcode M, bdlStepXCheckX pcode M mX (Sum.inl qX) *
      liftCylinderLZ pcode M L_Z (Sum.inl qX)) =
      ∑ xv : BoundaryX0Link pcode M,
        (∑ r : Fin (M + 1),
          if h : InShellR pcode M xv r then
            bdlDeltaX0Shell pcode M mX ⟨(xv, r), h⟩ 0
          else 0) * boundaryX0LinkLZ pcode M L_Z xv := by
    rw [Fintype.sum_sum_type]
    have h_inr : (∑ qX23 : (ShellSegment pcode M × Fin 3) ⊕ (BoundaryX0Link pcode M × Fin 2),
        bdlStepXCheckX pcode M mX (Sum.inl (Sum.inr qX23)) *
        liftCylinderLZ pcode M L_Z (Sum.inl (Sum.inr qX23))) = 0 :=
      Finset.sum_eq_zero (fun _ _ => by dsimp [liftCylinderLZ]; simp)
    rw [h_inr, add_zero, Fintype.sum_prod_type]
    have h_b : ∀ sv : RadialVertex pcode M,
        (∑ b : Fin 3, bdlStepXCheckX pcode M mX (Sum.inl (Sum.inl (sv, b))) *
          liftCylinderLZ pcode M L_Z (Sum.inl (Sum.inl (sv, b)))) =
        bdlDeltaX0 pcode M mX (Sum.inl (sv, 0)) * boundaryX0LinkLZ pcode M L_Z sv.val.val.1 := by
      intro sv
      rw [Finset.sum_eq_single (0 : Fin 3)]
      · dsimp [bdlStepXCheckX, liftCylinderLZ]
      · intro b _ hne; dsimp [liftCylinderLZ]; rw [if_neg hne, mul_zero]
      · intro h_abs; exact False.elim (h_abs (Finset.mem_univ 0))
    simp_rw [h_b]
    rw [sum_radialVertex_bdlDeltaX0 pcode M mX (fun sv => boundaryX0LinkLZ pcode M L_Z sv.val.1)]
    rw [sum_shellVertex_eq pcode M (fun sv => bdlDeltaX0Shell pcode M mX sv 0 * boundaryX0LinkLZ pcode M L_Z sv.val.1)]
    apply Finset.sum_congr rfl
    intro xv _
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro r _
    split_ifs with h
    · rfl
    · rw [zero_mul]
  rw [h_qX]
  rcases mX with ⟨x0, b0⟩ | ⟨sv0, b0⟩
  · have h_qQ : (∑ qQ : BDLCQ1 pcode M, bdlStepXCheckX pcode M (Sum.inl (x0, b0)) (Sum.inr qQ) *
        liftCylinderLZ pcode M L_Z (Sum.inr qQ)) = 0 :=
      Finset.sum_eq_zero (fun _ _ => zero_mul _)
    rw [h_qQ, add_zero]
    by_cases hb0 : b0 = 0
    · subst hb0
      have h_inner : ∀ xv : BoundaryX0Link pcode M,
          (∑ r : Fin (M + 1),
            if h : InShellR pcode M xv r then
              bdlDeltaX0Shell pcode M (Sum.inl (x0, 0)) ⟨(xv, r), h⟩ 0
            else 0) * boundaryX0LinkLZ pcode M L_Z xv =
          if xv.val.1 = x0 then boundaryX0LinkLZ pcode M L_Z xv else 0 := by
        intro xv
        by_cases h_lz : boundaryX0LinkLZ pcode M L_Z xv = 0
        · rw [h_lz, mul_zero]; split_ifs <;> rfl
        · have h_in0 : InShellR pcode M xv 0 :=
            inShellR_of_boundaryX0LinkLZ_ne_zero pcode M L_Z xv 0 h_lz
          rw [Finset.sum_eq_single (0 : Fin (M + 1))]
          · rw [dif_pos h_in0, bdlDeltaX0Shell_eq_ite]
            (try dsimp only)
            have h_nd := not_isDiagZeroVertex_of_boundaryX0LinkLZ_ne_zero pcode M L_Z xv 0 h_in0 h_lz
            have h_eq : ((Sum.inl (x0, (0 : Fin 3)) : BDLStepXMX pcode M) = Sum.inl (xv.val.1, 0)) ↔ xv.val.1 = x0 := by
              simp [eq_comm]
            by_cases hx : xv.val.1 = x0
            · simp [h_nd, hx]
            · simp [h_nd, hx, Ne.symm hx]
          · intro r _ hne
            have hr_nz : r.val ≠ 0 := fun h => hne (Fin.ext h)
            split_ifs with h_in
            · rw [bdlDeltaX0Shell_eq_ite]; (try dsimp only); rw [if_neg hr_nz]; simp
            · rfl
          · intro h_abs; exact False.elim (h_abs (Finset.mem_univ 0))
      simp_rw [h_inner]
      rw [sum_boundaryX0LinkLZ_eq pcode M L_Z x0]
      rfl
    · have h_emb : ∀ S_c : M_X → ZMod 2, embedCoarseStepXMX pcode M S_c (Sum.inl (x0, b0)) = 0 := by
        intro S_c
        fin_cases b0 <;> first | contradiction | rfl
      rw [h_emb]
      apply Finset.sum_eq_zero
      intro xv _
      have h_sum0 : (∑ r : Fin (M + 1),
          if h : InShellR pcode M xv r then
            bdlDeltaX0Shell pcode M (Sum.inl (x0, b0)) ⟨(xv, r), h⟩ 0
          else 0) = 0 := by
        apply Finset.sum_eq_zero
        intro r _
        split_ifs with h_in
        · rw [bdlDeltaX0Shell_eq_ite]
          (try dsimp only)
          have h1 : (Sum.inl (x0, b0) : BDLStepXMX pcode M) ≠ Sum.inl (xv.val.1, 0) := by
            intro h; injection h with h; injection h with _ hb; exact hb0 hb
          by_cases hr0 : r.val = 0
          · by_cases h_diag : IsDiagZeroVertex pcode M ⟨(xv, r), h_in⟩
            · rw [if_pos hr0, if_pos h_diag]
            · rw [if_pos hr0, if_neg h_diag, if_neg h1]; simp
          · rw [if_neg hr0]; simp
        · rfl
      rw [h_sum0, zero_mul]
  · dsimp [bdlStepXCheckX, embedCoarseStepXMX]
    rw [sum_gXQ0_liftCylinderLZ pcode M L_Z sv0 b0]
    by_cases hb0 : b0 = 0
    · subst hb0
      have h_term : ∀ xv : BoundaryX0Link pcode M,
          (∑ r : Fin (M + 1),
            if h : InShellR pcode M xv r then
              bdlDeltaX0Shell pcode M (Sum.inr (sv0, 0)) ⟨(xv, r), h⟩ 0
            else 0) * boundaryX0LinkLZ pcode M L_Z xv =
          if xv = sv0.val.1 then
            (if sv0.val.2 = Fin.last M then boundaryX0LinkLZ pcode M L_Z sv0.val.1 else 0)
          else 0 := by
        intro xv
        by_cases h_lz : boundaryX0LinkLZ pcode M L_Z xv = 0
        · rw [h_lz, mul_zero]
          by_cases hxv : xv = sv0.val.1
          · subst hxv; rw [h_lz]; simp
          · simp [hxv]
        · rw [sum_radial_deltaX0_shell_eq pcode M L_Z sv0 xv h_lz]
          by_cases hxv : xv = sv0.val.1
          · subst hxv
            by_cases hr : sv0.val.2 = Fin.last M
            · simp [hr]
            · simp [hr]
          · simp [hxv]
      simp_rw [h_term]
      rw [Finset.sum_eq_single sv0.val.1]
      · rw [if_pos rfl]
        by_cases hr : sv0.val.2 = Fin.last M
        · simp [hr, zmod2_add_self]
        · simp [hr]
      · intro xv _ hne; rw [if_neg hne]
      · intro h_abs; exact False.elim (h_abs (Finset.mem_univ sv0.val.1))
    · have h_zero : (∑ xv : BoundaryX0Link pcode M,
          (∑ r : Fin (M + 1),
            if h : InShellR pcode M xv r then
              bdlDeltaX0Shell pcode M (Sum.inr (sv0, b0)) ⟨(xv, r), h⟩ 0
            else 0) * boundaryX0LinkLZ pcode M L_Z xv) = 0 := by
        apply Finset.sum_eq_zero
        intro xv _
        by_cases h_lz : boundaryX0LinkLZ pcode M L_Z xv = 0
        · rw [h_lz, mul_zero]
        · have h_sum0 : (∑ r : Fin (M + 1),
              if h : InShellR pcode M xv r then
                bdlDeltaX0Shell pcode M (Sum.inr (sv0, b0)) ⟨(xv, r), h⟩ 0
              else 0) = 0 := by
            apply Finset.sum_eq_zero
            intro r _
            split_ifs with h_in
            · rw [bdlDeltaX0Shell_eq_ite]
              (try dsimp only)
              have h1 : (Sum.inr (sv0, b0) : BDLStepXMX pcode M) ≠
                  Sum.inr (radialParentVertex pcode M ⟨(xv, r), h_in⟩, 0) := by
                intro h; injection h with h; injection h with _ hb; exact hb0 hb
              have h2 : (Sum.inr (sv0, b0) : BDLStepXMX pcode M) ≠
                  Sum.inr (⟨(xv, r), h_in⟩, 0) := by
                intro h; injection h with h; injection h with _ hb; exact hb0 hb
              by_cases hr0 : r.val = 0
              · have h_nd := not_isDiagZeroVertex_of_boundaryX0LinkLZ_ne_zero pcode M L_Z xv r h_in h_lz
                rw [if_pos hr0, if_neg h_nd, if_neg h2]; simp
              · rw [if_neg hr0, if_neg h1, if_neg h2]; simp
            · rfl
          rw [h_sum0, zero_mul]
      have hc : ¬ (sv0.val.2 = Fin.last M ∧ b0 = 0) := fun h => hb0 h.2
      rw [h_zero, if_neg hc, add_zero]

end BDLDecoder
end WeldedHierarchy
