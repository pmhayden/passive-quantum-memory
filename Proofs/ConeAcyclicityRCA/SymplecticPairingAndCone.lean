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

import Proofs.Step2DegreeAndWeld.DegreeOverlapAndDensityPreservation
import Proofs.Step2DegreeAndWeld.LogicalChainLiftsAndPreservation

/-!
# Symplectic F_2 Pairing Duality, Cylinder Fiber Lifts, and Radial Shell Homotopy

Establishes orthogonal-complement duality for the F_2 bilinear pairing dualPairing on finite CSS chain complexes (mem_of_dualPairing_ortho), constructs the three-layer cylinder fiber projections and coarse lift liftStepXMX with exact coboundary intertwining (checkGen_dual_liftStepXMX), and defines the radial shell contracting homotopy hRadialShell, cumulative ray sum radialRaySum, and apex radial cochain apexRadialCocycle.

## References

* Part I, Section 2.3 (`subsec:step2-mapping-cone`), Definition 2.5 (`def:three-layer-mapping-cone`), Proposition 2.6 (`prop:mapping-cone-invariants`)
* Part I, Section 3.1 (`subsec:rca-trinity`), Proposition 3.3 (`prop:trinity-equivalence`)
* Part I, Section 3.2 (`subsec:nilpotent-hpl`), Lemma 3.6 (`lem:block-sdr`), Proposition 3.7 (`prop:classical-hpl`)
-/

noncomputable section
open scoped Classical BigOperators
namespace WeldedHierarchy

noncomputable abbrev canonicalSquareQ {Q M_Z M_X : Type}
    [Fintype Q] [DecidableEq Q] [Fintype M_Z] [DecidableEq M_Z] [Fintype M_X] [DecidableEq M_X]
    (pcode : CSSCode3D Q M_Z M_X) (x : M_X) (z : M_Z)
    (h : ∃ q : Q, pcode.checkX x q ≠ 0 ∧ pcode.checkZ z q ≠ 0) : Q :=
  _root_.canonicalSquareQ pcode (fun _ => 0) x z h

lemma canonicalSquareQ_spec {Q M_Z M_X : Type}
    [Fintype Q] [DecidableEq Q] [Fintype M_Z] [DecidableEq M_Z] [Fintype M_X] [DecidableEq M_X]
    (pcode : CSSCode3D Q M_Z M_X) (x : M_X) (z : M_Z)
    (h : ∃ q : Q, pcode.checkX x q ≠ 0 ∧ pcode.checkZ z q ≠ 0) :
    pcode.checkX x (canonicalSquareQ pcode x z h) ≠ 0 ∧
    pcode.checkZ z (canonicalSquareQ pcode x z h) ≠ 0 :=
  _root_.canonicalSquareQ_spec pcode (fun _ => 0) x z h

lemma syndrome_checkGen_zero {Q M_Z M_X : Type}
    [Fintype Q] [DecidableEq Q] [Fintype M_Z] [DecidableEq M_Z] [Fintype M_X] [DecidableEq M_X]
    (code : CSSCode3D Q M_Z M_X) (c2 : M_Z → ZMod 2) :
    syndrome code (checkGen code c2) = 0 :=
  f2Syndrome_f2CheckGen_eq_zero code.toF2ChainComplex c2

/-! ## 1. Symplectic Pairing and Orthogonal Complement over ZMod 2 -/

/-- Decomposes any 1-chain `v : Q → ZMod 2` into its sum of single-qubit basis vectors `singleQubit q`. -/
lemma pi_eq_sum_singleQubit {Q : Type} [Fintype Q] [DecidableEq Q] (v : Q → ZMod 2) :
    v = ∑ q : Q, v q • singleQubit q := by
  ext q0
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, singleQubit]
  rw [Finset.sum_eq_single q0]
  · simp
  · intro q _ hne; rw [if_neg (Ne.symm hne), mul_zero]
  · intro h_abs; exact False.elim (h_abs (Finset.mem_univ q0))

/-- Evaluates `dualPairing (singleQubit q) w` to the coordinate `w q`. -/
lemma dualPairing_singleQubit_left {Q : Type} [Fintype Q] [DecidableEq Q]
    (q : Q) (h : Q → ZMod 2) :
    dualPairing (singleQubit q) h = h q := by
  dsimp [dualPairing, singleQubit]
  rw [Finset.sum_eq_single q]
  · simp
  · intro q' _ hne; rw [if_neg hne, zero_mul]
  · intro h_abs; exact False.elim (h_abs (Finset.mem_univ q))

/-- Evaluates `dualPairing v (singleQubit q)` to the coordinate `v q`. -/
lemma dualPairing_singleQubit_right {Q : Type} [Fintype Q] [DecidableEq Q]
    (g : Q → ZMod 2) (q : Q) :
    dualPairing g (singleQubit q) = g q := by
  dsimp [dualPairing, singleQubit]
  rw [Finset.sum_eq_single q]
  · simp
  · intro q' _ hne; rw [if_neg hne, mul_zero]
  · intro h_abs; exact False.elim (h_abs (Finset.mem_univ q))

/-- Adjoint identity relating `dualPairing (checkGen code c) w` to `syndrome (dualCode code) w`. -/
lemma dualPairing_checkGen_primal {Q M_Z M_X : Type}
    [Fintype Q] [DecidableEq Q] [Fintype M_Z] [DecidableEq M_Z] [Fintype M_X] [DecidableEq M_X]
    (code : CSSCode3D Q M_Z M_X) (c2 : M_Z → ZMod 2) (h : Q → ZMod 2) :
    dualPairing (checkGen code c2) h =
      ∑ mZ : M_Z, c2 mZ * syndrome (dualCode code) h mZ := by
  dsimp [dualPairing, checkGen, syndrome, dualCode, f2CheckGen, f2Syndrome, dualF2ChainComplex]
  simp_rw [Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro mZ _
  apply Finset.sum_congr rfl
  intro q _
  ring

/-- Adjoint identity relating `dualPairing v (checkGen (dualCode code) d)` to `syndrome code v`. -/
lemma dualPairing_checkGen_dual {Q M_Z M_X : Type}
    [Fintype Q] [DecidableEq Q] [Fintype M_Z] [DecidableEq M_Z] [Fintype M_X] [DecidableEq M_X]
    (code : CSSCode3D Q M_Z M_X) (g : Q → ZMod 2) (d2 : M_X → ZMod 2) :
    dualPairing g (checkGen (dualCode code) d2) =
      ∑ mX : M_X, d2 mX * syndrome code g mX := by
  dsimp [dualPairing, checkGen, syndrome, dualCode, f2CheckGen, f2Syndrome, dualF2ChainComplex]
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro mX _
  apply Finset.sum_congr rfl
  intro q _
  ring

/-- **Finite-Dimensional Orthogonal Complement Duality Over `ZMod 2` (`mem_of_dualPairing_ortho`):**
    A 1-chain `g : Q → ZMod 2` belongs to a submodule `W ≤ (Q → ZMod 2)` whenever `dualPairing g h = 0`
    for all `h : Q → ZMod 2` orthogonal to `W` under `dualPairing`. -/
lemma mem_of_dualPairing_ortho {Q : Type} [Fintype Q] [DecidableEq Q]
    (W : Submodule (ZMod 2) (Q → ZMod 2)) (g : Q → ZMod 2)
    (h_ortho : ∀ h : Q → ZMod 2, (∀ w ∈ W, dualPairing w h = 0) → dualPairing g h = 0) :
    g ∈ W := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_contra hg
  have h_ne : W.mkQ g ≠ 0 := by
    intro h0
    exact hg ((Submodule.Quotient.mk_eq_zero W).mp h0)
  let B := Module.Basis.ofVectorSpace (ZMod 2) ((Q → ZMod 2) ⧸ W)
  have h_repr_ne : B.repr (W.mkQ g) ≠ 0 := by
    intro hr
    exact h_ne (B.repr.injective (hr.trans (map_zero B.repr).symm))
  obtain ⟨i, hi⟩ : ∃ i, B.repr (W.mkQ g) i ≠ 0 := by
    by_contra h_all
    push_neg at h_all
    exact h_repr_ne (Finsupp.ext h_all)
  let f : (Q → ZMod 2) →ₗ[ZMod 2] ZMod 2 :=
    (Finsupp.lapply i).comp (B.repr.toLinearMap.comp W.mkQ)
  let h : Q → ZMod 2 := fun q => f (singleQubit q)
  have hf_eq : ∀ v : Q → ZMod 2, f v = dualPairing v h := by
    intro v
    conv_lhs => rw [pi_eq_sum_singleQubit v]
    rw [map_sum]
    dsimp [dualPairing, h]
    apply Finset.sum_congr rfl
    intro q _
    rw [map_smul, smul_eq_mul]
  have h_w_zero : ∀ w ∈ W, dualPairing w h = 0 := by
    intro w hw
    rw [← hf_eq w]
    dsimp [f]
    rw [(Submodule.Quotient.mk_eq_zero W).mpr hw, map_zero]
    rfl
  have hg_zero : dualPairing g h = 0 := h_ortho h h_w_zero
  rw [← hf_eq g] at hg_zero
  exact hi hg_zero

/-! ## 2. X-Check Fiber Owner Map and Cochain Lifts -/

/-- Owner coarse X-check `stepXMXOwnerX mX ∈ M_X` of a fine X-check `mX ∈ BDLStepXMX pcode M`. -/
def stepXMXOwnerX {Q M_Z M_X : Type}
    [Fintype Q] [DecidableEq Q] [Fintype M_Z] [DecidableEq M_Z] [Fintype M_X] [DecidableEq M_X]
    (pcode : CSSCode3D Q M_Z M_X) (M : ℕ) : BDLStepXMX pcode M → M_X
  | Sum.inl (x, _) => x
  | Sum.inr (sv, _) => sv.val.1.val.1

/-- Coarse primal 1-chain projection `projCylinderLZ` ($\pi_*$, transpose of `liftCylinderLX`) on `bdlCylinderStepX pcode M`. -/
def projCylinderLZ {Q M_Z M_X : Type}
    [Fintype Q] [DecidableEq Q] [Fintype M_Z] [DecidableEq M_Z] [Fintype M_X] [DecidableEq M_X]
    (pcode : CSSCode3D Q M_Z M_X) (M : ℕ) (g : BDLStepXQ pcode M → ZMod 2) (q : Q) : ZMod 2 :=
  dualPairing g (liftCylinderLX pcode M (singleQubit q))

/-- Coarse dual 1-cochain projection `projCylinderLX` ($\pi^*$, transpose of `liftCylinderLZ`) on `bdlCylinderStepX pcode M`. -/
def projCylinderLX {Q M_Z M_X : Type}
    [Fintype Q] [DecidableEq Q] [Fintype M_Z] [DecidableEq M_Z] [Fintype M_X] [DecidableEq M_X]
    (pcode : CSSCode3D Q M_Z M_X) (M : ℕ) (h : BDLStepXQ pcode M → ZMod 2) (q : Q) : ZMod 2 :=
  dualPairing (liftCylinderLZ pcode M (singleQubit q)) h

/-- Constant-on-cylinder lift `liftStepXMX` of a coarse X-check 0-cochain `c : M_X → ZMod 2` to `BDLStepXMX pcode M`. -/
def liftStepXMX {Q M_Z M_X : Type}
    [Fintype Q] [DecidableEq Q] [Fintype M_Z] [DecidableEq M_Z] [Fintype M_X] [DecidableEq M_X]
    (pcode : CSSCode3D Q M_Z M_X) (M : ℕ) (c : M_X → ZMod 2) (mX : BDLStepXMX pcode M) : ZMod 2 :=
  c (stepXMXOwnerX pcode M mX)

/-- Proves that `projXq0ToBoundaryX0 pcode M v0` lies in the link of `x` whenever `pcode.checkX x (xq0OwnerQ pcode M v0) ≠ 0`. -/
lemma inLinkOfX_projXq0_of_checkX_ne_zero {Q M_Z M_X : Type}
    [Fintype Q] [DecidableEq Q] [Fintype M_Z] [DecidableEq M_Z] [Fintype M_X] [DecidableEq M_X]
    (pcode : CSSCode3D Q M_Z M_X) (M : ℕ) (x : M_X) (v0 : Xq0 pcode M)
    (hx : pcode.checkX x (xq0OwnerQ pcode M v0) ≠ 0) :
    InLinkOfX pcode M x (projXq0ToBoundaryX0 pcode M v0) := by
  rcases v0 with q_in | ⟨⟨eZ, j⟩ | eZ⟩
  · exact hx
  · exact hx
  · exact ⟨eZ.val.1, hx, eZ.property⟩

/-- Proves that `checkGen (dualCode (bdlCylinderStepX pcode M)) (liftStepXMX pcode M c)` vanishes on all interior 1-cells `Sum.inl qX`. -/
lemma checkGen_dual_liftStepXMX_inl {Q M_Z M_X : Type}
    [Fintype Q] [DecidableEq Q] [Fintype M_Z] [DecidableEq M_Z] [Fintype M_X] [DecidableEq M_X]
    (pcode : CSSCode3D Q M_Z M_X) (M : ℕ) (c : M_X → ZMod 2) (qX : BDLCX1 pcode M) :
    checkGen (dualCode (bdlCylinderStepX pcode M)) (liftStepXMX pcode M c) (Sum.inl qX) = 0 := by
  dsimp [checkGen, dualCode, bdlCylinderStepX, f2CheckGen, f2Syndrome, dualF2ChainComplex]
  dsimp [bdlStepXCheckX, bdlDeltaX0]
  rcases qX with ⟨rv, b⟩ | ⟨⟨seg, b⟩ | ⟨xv, b⟩⟩
  · by_cases hr0 : rv.val.val.2.val = 0
    · simp_rw [if_pos hr0, add_mul, Finset.sum_add_distrib]
      rw [Finset.sum_eq_single (Sum.inl (rv.val.val.1.val.1, b))]
      · rw [Finset.sum_eq_single (Sum.inr (rv.val, b))]
        · dsimp [liftStepXMX, stepXMXOwnerX]
          rw [if_pos rfl, if_pos rfl]
          exact zmod2_add_self _
        · intro mX _ hne; rw [if_neg hne, zero_mul]
        · intro h_abs; exact False.elim (h_abs (Finset.mem_univ _))
      · intro mX _ hne; rw [if_neg hne, zero_mul]
      · intro h_abs; exact False.elim (h_abs (Finset.mem_univ _))
    · simp_rw [if_neg hr0, add_mul, Finset.sum_add_distrib]
      rw [Finset.sum_eq_single (Sum.inr (radialParentVertex pcode M rv.val, b))]
      · rw [Finset.sum_eq_single (Sum.inr (rv.val, b))]
        · rw [if_pos rfl, if_pos rfl]
          dsimp [liftStepXMX, stepXMXOwnerX, radialParentVertex, radialParentLink]
          exact zmod2_add_self _
        · intro mX _ hne; rw [if_neg hne, zero_mul]
        · intro h_abs; exact False.elim (h_abs (Finset.mem_univ _))
      · intro mX _ hne; rw [if_neg hne, zero_mul]
      · intro h_abs; exact False.elim (h_abs (Finset.mem_univ _))
  · simp_rw [add_mul, Finset.sum_add_distrib]
    rw [Finset.sum_eq_single (Sum.inr (shellSegStartVertex pcode M seg, b))]
    · rw [Finset.sum_eq_single (Sum.inr (shellSegEndVertex pcode M seg, b))]
      · rw [if_pos rfl, if_pos rfl]
        dsimp [liftStepXMX, stepXMXOwnerX, shellSegStartVertex, shellSegEndVertex]
        exact zmod2_add_self _
      · intro mX _ hne; rw [if_neg hne, zero_mul]
      · intro h_abs; exact False.elim (h_abs (Finset.mem_univ _))
    · intro mX _ hne; rw [if_neg hne, zero_mul]
    · intro h_abs; exact False.elim (h_abs (Finset.mem_univ _))
  · simp_rw [add_mul, Finset.sum_add_distrib]
    rw [Finset.sum_eq_single (Sum.inr (mkOuterShellVertex pcode M xv, 0))]
    · rw [Finset.sum_eq_single (Sum.inr (mkOuterShellVertex pcode M xv, b.succ))]
      · rw [if_pos rfl, if_pos rfl]
        dsimp [liftStepXMX, stepXMXOwnerX, mkOuterShellVertex]
        exact zmod2_add_self _
      · intro mX _ hne; rw [if_neg hne, zero_mul]
      · intro h_abs; exact False.elim (h_abs (Finset.mem_univ _))
    · intro mX _ hne; rw [if_neg hne, zero_mul]
    · intro h_abs; exact False.elim (h_abs (Finset.mem_univ _))

/-- **Cochain Commutation `δ^0 ∘ liftStepXMX = liftCylinderLX ∘ δ_coarse^0` (`checkGen_dual_liftStepXMX`):** -/
theorem checkGen_dual_liftStepXMX {Q M_Z M_X : Type}
    [Fintype Q] [DecidableEq Q] [Fintype M_Z] [DecidableEq M_Z] [Fintype M_X] [DecidableEq M_X]
    (pcode : CSSCode3D Q M_Z M_X) (M : ℕ) (c : M_X → ZMod 2) :
    checkGen (dualCode (bdlCylinderStepX pcode M)) (liftStepXMX pcode M c) =
      liftCylinderLX pcode M (checkGen (dualCode pcode) c) := by
  ext q
  rcases q with qX | ⟨v0, b0⟩
  · rw [checkGen_dual_liftStepXMX_inl]
    rfl
  · dsimp [checkGen, dualCode, bdlCylinderStepX, liftCylinderLX, f2CheckGen, f2Syndrome, dualF2ChainComplex]
    dsimp [bdlStepXCheckX]
    rw [Fintype.sum_sum_type]
    have h_inl : (∑ x : M_X × Fin 3, bdlGXQ0 pcode M (Sum.inl x) (v0, b0) *
        liftStepXMX pcode M c (Sum.inl x)) = 0 :=
      Finset.sum_eq_zero (fun _ _ => by dsimp [bdlGXQ0]; simp)
    rw [h_inl, zero_add, Fintype.sum_prod_type, Finset.sum_comm]
    rw [Finset.sum_eq_single b0]
    · rw [sum_shellVertex_eq pcode M (fun sv => bdlGXQ0 pcode M (Sum.inr (sv, b0)) (v0, b0) * liftStepXMX pcode M c (Sum.inr (sv, b0)))]
      have h_inner : ∀ xv : BoundaryX0Link pcode M,
          (∑ r : Fin (M + 1),
            if h : InShellR pcode M xv r then
              bdlGXQ0 pcode M (Sum.inr (⟨(xv, r), h⟩, b0)) (v0, b0) * liftStepXMX pcode M c (Sum.inr (⟨(xv, r), h⟩, b0))
            else 0) =
          if xv.val.2 = projXq0ToBoundaryX0 pcode M v0 then
            pcode.checkX xv.val.1 (xq0OwnerQ pcode M v0) * c xv.val.1
          else 0 := by
        intro xv
        rw [Finset.sum_eq_single (Fin.last M)]
        · rw [dif_pos (inShellR_last pcode M xv)]
          dsimp [bdlGXQ0, liftStepXMX, stepXMXOwnerX]
          by_cases hv : xv.val.2 = projXq0ToBoundaryX0 pcode M v0
          · rw [if_pos ⟨rfl, hv, rfl⟩, if_pos hv]
          · have hc : ¬ (Fin.last M = Fin.last M ∧ xv.val.2 = projXq0ToBoundaryX0 pcode M v0 ∧ b0 = b0) :=
              fun h => hv h.2.1
            rw [if_neg hc, if_neg hv, zero_mul]
        · intro r _ hne
          split_ifs with h_in
          · dsimp [bdlGXQ0]
            have hc : ¬ (r = Fin.last M ∧ xv.val.2 = projXq0ToBoundaryX0 pcode M v0 ∧ b0 = b0) :=
              fun h => hne h.1
            rw [if_neg hc, zero_mul]
          · rfl
        · intro h_abs; exact False.elim (h_abs (Finset.mem_univ _))
      simp_rw [h_inner]
      let f : M_X × BoundaryX0 pcode M → ZMod 2 := fun p =>
        if p.2 = projXq0ToBoundaryX0 pcode M v0 then pcode.checkX p.1 (xq0OwnerQ pcode M v0) * c p.1 else 0
      have h1 : (∑ xv : BoundaryX0Link pcode M, if xv.val.2 = projXq0ToBoundaryX0 pcode M v0 then
          pcode.checkX xv.val.1 (xq0OwnerQ pcode M v0) * c xv.val.1 else 0) =
          ∑ p ∈ Finset.univ.filter (fun p : M_X × BoundaryX0 pcode M => InLinkOfX pcode M p.1 p.2), f p :=
        (Finset.sum_subtype (Finset.univ.filter (fun p : M_X × BoundaryX0 pcode M => InLinkOfX pcode M p.1 p.2))
          (p := fun p : M_X × BoundaryX0 pcode M => InLinkOfX pcode M p.1 p.2)
          (fun _ => Finset.mem_filter.trans (and_iff_right (Finset.mem_univ _))) f).symm
      have h2 : (∑ p ∈ Finset.univ.filter (fun p : M_X × BoundaryX0 pcode M => InLinkOfX pcode M p.1 p.2), f p) =
          ∑ p : M_X × BoundaryX0 pcode M, if InLinkOfX pcode M p.1 p.2 then f p else 0 :=
        Finset.sum_filter (fun p : M_X × BoundaryX0 pcode M => InLinkOfX pcode M p.1 p.2) f
      rw [h1, h2, Fintype.sum_prod_type]
      apply Finset.sum_congr rfl
      intro x _
      rw [Finset.sum_eq_single (projXq0ToBoundaryX0 pcode M v0)]
      · dsimp [f]
        rw [if_pos rfl]
        by_cases hx : pcode.checkX x (xq0OwnerQ pcode M v0) = 0
        · simp [hx]
        · rw [if_pos (inLinkOfX_projXq0_of_checkX_ne_zero pcode M x v0 hx)]
      · intro v _ hne
        dsimp [f]
        simp [hne]
      · intro h_abs; exact False.elim (h_abs (Finset.mem_univ _))
    · intro b _ hne
      apply Finset.sum_eq_zero
      intro sv _
      dsimp [bdlGXQ0]
      have hc : ¬ (sv.val.2 = Fin.last M ∧ sv.val.1.val.2 = projXq0ToBoundaryX0 pcode M v0 ∧ b = b0) :=
        fun h => hne h.2.2
      rw [if_neg hc, zero_mul]
    · intro h_abs; exact False.elim (h_abs (Finset.mem_univ _))

/-! ## 3. Radial Ray Integration and Apex Radial Gauge Cochain -/

/-- Evaluation of `h` on the radial 1-cell at `sv : ShellVertex pcode M`:
    - If `sv` is a `RadialVertex` (`¬ isDiagZeroVertex pcode M sv`), equals `h (Sum.inl (Sum.inl (⟨sv, h_nd⟩, b)))`.
    - If `isDiagZeroVertex pcode M sv` (the corner vertex `((x, z), 0)`), equals the canonical corner
      square combination `h (cornerSpokeRadial x q_can, b) + h (cornerSeg x q_can z, b)` if `(x, z)`
      has a common qubit `q`, and `0` otherwise. -/
def hRadialShell {Q M_Z M_X : Type}
    [Fintype Q] [DecidableEq Q] [Fintype M_Z] [DecidableEq M_Z] [Fintype M_X] [DecidableEq M_X]
    (pcode : CSSCode3D Q M_Z M_X) (M : ℕ)
    (h : BDLStepXQ pcode M → ZMod 2) (sv : ShellVertex pcode M) (b : Fin 3) : ZMod 2 :=
  if h_nd : ¬ IsDiagZeroVertex pcode M sv then
    h (Sum.inl (Sum.inl (⟨sv, h_nd⟩, b)))
  else
    match sv.val.1.val.2 with
    | Sum.inr (Sum.inr z) =>
      if h_ex : ∃ q : Q, pcode.checkX sv.val.1.val.1 q ≠ 0 ∧ pcode.checkZ z q ≠ 0 then
        let q_can := canonicalSquareQ pcode sv.val.1.val.1 z h_ex
        let h_can := canonicalSquareQ_spec pcode sv.val.1.val.1 z h_ex
        h (Sum.inl (Sum.inl (cornerSpokeRadial pcode M sv.val.1.val.1 q_can h_can.1, b))) +
        h (Sum.inl (Sum.inr (Sum.inl (cornerSeg pcode M sv.val.1.val.1 q_can z h_can.1 h_can.2, b))))
      else 0
    | _ => 0

/-- Non-recursive 1D radial ray line integral `radialRaySum` on `ShellVertex pcode M`. -/
def radialRaySum {Q M_Z M_X : Type}
    [Fintype Q] [DecidableEq Q] [Fintype M_Z] [DecidableEq M_Z] [Fintype M_X] [DecidableEq M_X]
    (pcode : CSSCode3D Q M_Z M_X) (M : ℕ)
    (h : BDLStepXQ pcode M → ZMod 2) (sv : ShellVertex pcode M) (b : Fin 3) : ZMod 2 :=
  ∑ i ∈ Finset.range (sv.val.2.val + 1),
    hRadialShell pcode M h ((radialParentVertex pcode M)^[i] sv) b

/-- Evaluates `radialRaySum pcode M h sv b` at radial coordinate `r = 0` to `0`. -/
lemma radialRaySum_zero {Q M_Z M_X : Type}
    [Fintype Q] [DecidableEq Q] [Fintype M_Z] [DecidableEq M_Z] [Fintype M_X] [DecidableEq M_X]
    (pcode : CSSCode3D Q M_Z M_X) (M : ℕ)
    (h : BDLStepXQ pcode M → ZMod 2) (sv : ShellVertex pcode M) (b : Fin 3)
    (hr0 : sv.val.2.val = 0) :
    radialRaySum pcode M h sv b = hRadialShell pcode M h sv b := by
  dsimp [radialRaySum]
  rw [hr0]
  simp

/-- Recurrence for `radialRaySum` stepping from radial coordinate `r` to `r + 1` along a radial ray. -/
lemma radialRaySum_succ {Q M_Z M_X : Type}
    [Fintype Q] [DecidableEq Q] [Fintype M_Z] [DecidableEq M_Z] [Fintype M_X] [DecidableEq M_X]
    (pcode : CSSCode3D Q M_Z M_X) (M : ℕ)
    (h : BDLStepXQ pcode M → ZMod 2) (sv : ShellVertex pcode M) (b : Fin 3)
    (hr : sv.val.2.val ≠ 0) :
    radialRaySum pcode M h sv b =
      radialRaySum pcode M h (radialParentVertex pcode M sv) b +
      hRadialShell pcode M h sv b := by
  dsimp [radialRaySum]
  have h_pred : (radialParentVertex pcode M sv).val.2.val + 1 = sv.val.2.val := by
    dsimp [radialParentVertex, finPred]
    omega
  rw [← h_pred, Finset.sum_range_succ']
  simp only [Function.iterate_zero, id_eq, Function.iterate_succ_apply]

/-- Zero-apex radial 0-cochain `apexRadialCocycle` on `BDLStepXMX pcode M` integrating `h` outward along every radial tree. -/
def apexRadialCocycle {Q M_Z M_X : Type}
    [Fintype Q] [DecidableEq Q] [Fintype M_Z] [DecidableEq M_Z] [Fintype M_X] [DecidableEq M_X]
    (pcode : CSSCode3D Q M_Z M_X) (M : ℕ) (h : BDLStepXQ pcode M → ZMod 2) :
    BDLStepXMX pcode M → ZMod 2
  | Sum.inl _ => 0
  | Sum.inr (sv, b) => radialRaySum pcode M h sv b

/-- **Radial Exactness on `BDLCX1` (`checkGen_dual_apexRadialCocycle_radial`):**
    The coboundary of `apexRadialCocycle pcode M h` matches `h` identically on every radial 1-cell
    `Sum.inl (Sum.inl (rv, b))` (`rv : RadialVertex pcode M`) of every cylinder $Y_x$. -/
lemma checkGen_dual_apexRadialCocycle_radial {Q M_Z M_X : Type}
    [Fintype Q] [DecidableEq Q] [Fintype M_Z] [DecidableEq M_Z] [Fintype M_X] [DecidableEq M_X]
    (pcode : CSSCode3D Q M_Z M_X) (M : ℕ) (h : BDLStepXQ pcode M → ZMod 2)
    (rv : RadialVertex pcode M) (b : Fin 3) :
    checkGen (dualCode (bdlCylinderStepX pcode M)) (apexRadialCocycle pcode M h)
      (Sum.inl (Sum.inl (rv, b))) = h (Sum.inl (Sum.inl (rv, b))) := by
  dsimp [checkGen, dualCode, bdlCylinderStepX, f2CheckGen, f2Syndrome, dualF2ChainComplex]
  dsimp [bdlStepXCheckX, bdlDeltaX0]
  have h_shell : hRadialShell pcode M h rv.val b = h (Sum.inl (Sum.inl (rv, b))) := by
    dsimp [hRadialShell]
    rw [dif_pos rv.property]
  by_cases hr0 : rv.val.val.2.val = 0
  · simp_rw [if_pos hr0, add_mul, Finset.sum_add_distrib]
    rw [Finset.sum_eq_single (Sum.inl (rv.val.val.1.val.1, b))]
    · rw [Finset.sum_eq_single (Sum.inr (rv.val, b))]
      · dsimp [apexRadialCocycle]
        rw [if_pos rfl, if_pos rfl, radialRaySum_zero pcode M h rv.val b hr0, h_shell]
        ring
      · intro mX _ hne; rw [if_neg hne, zero_mul]
      · intro h_abs; exact False.elim (h_abs (Finset.mem_univ _))
    · intro mX _ hne; rw [if_neg hne, zero_mul]
    · intro h_abs; exact False.elim (h_abs (Finset.mem_univ _))
  · simp_rw [if_neg hr0, add_mul, Finset.sum_add_distrib]
    rw [Finset.sum_eq_single (Sum.inr (radialParentVertex pcode M rv.val, b))]
    · rw [Finset.sum_eq_single (Sum.inr (rv.val, b))]
      · dsimp [apexRadialCocycle]
        rw [if_pos rfl, if_pos rfl, radialRaySum_succ pcode M h rv.val b hr0, h_shell, one_mul, one_mul]
        have := zmod2_add_self (radialRaySum pcode M h (radialParentVertex pcode M rv.val) b)
        linear_combination this
      · intro mX _ hne; rw [if_neg hne, zero_mul]
      · intro h_abs; exact False.elim (h_abs (Finset.mem_univ _))
    · intro mX _ hne; rw [if_neg hne, zero_mul]
    · intro h_abs; exact False.elim (h_abs (Finset.mem_univ _))

/-- **Outer Collar Step Constancy (`bdlDeltaX1_collar_const_step`):**
    If `h'` vanishes on the outer azimuthal segments `(mkOuterShellSegment pcode M s k, 0)` and `(..., b.succ)`
    and has zero Z-syndrome at `Sum.inl (Sum.inr (s, k, b))`, then `h'` takes equal values on the vertical
    boundary 1-cells `(bxStartLink pcode M s k, b)` and `(bxEndLink pcode M s k, b)`. -/
lemma bdlDeltaX1_collar_const_step {Q M_Z M_X : Type}
    [Fintype Q] [DecidableEq Q] [Fintype M_Z] [DecidableEq M_Z] [Fintype M_X] [DecidableEq M_X]
    (pcode : CSSCode3D Q M_Z M_X) (M : ℕ) (h' : BDLStepXQ pcode M → ZMod 2)
    (s : ActiveZLink pcode) (k : Fin (M + 1)) (b : Fin 2)
    (h_az0 : h' (Sum.inl (Sum.inr (Sum.inl (mkOuterShellSegment pcode M s k, 0)))) = 0)
    (h_az1 : h' (Sum.inl (Sum.inr (Sum.inl (mkOuterShellSegment pcode M s k, b.succ)))) = 0)
    (h_syn : syndrome (dualCode (bdlCylinderStepX pcode M)) h' (Sum.inl (Sum.inr (s, k, b))) = 0) :
    h' (Sum.inl (Sum.inr (Sum.inr (bxStartLink pcode M s k, b)))) =
    h' (Sum.inl (Sum.inr (Sum.inr (bxEndLink pcode M s k, b)))) := by
  dsimp [syndrome, dualCode, bdlCylinderStepX, f2CheckGen, f2Syndrome, dualF2ChainComplex] at h_syn
  rw [Fintype.sum_sum_type] at h_syn
  have hQ : (∑ qQ : BDLCQ1 pcode M,
      bdlStepXCheckZ pcode M (Sum.inl (Sum.inr (s, k, b))) (Sum.inr qQ) * h' (Sum.inr qQ)) = 0 :=
    Finset.sum_eq_zero (fun _ _ => zero_mul _)
  rw [hQ, add_zero] at h_syn
  have hX : (∑ qX : BDLCX1 pcode M,
      bdlStepXCheckZ pcode M (Sum.inl (Sum.inr (s, k, b))) (Sum.inl qX) * h' (Sum.inl qX)) =
      h' (Sum.inl (Sum.inr (Sum.inl (mkOuterShellSegment pcode M s k, 0)))) +
      h' (Sum.inl (Sum.inr (Sum.inl (mkOuterShellSegment pcode M s k, b.succ)))) +
      h' (Sum.inl (Sum.inr (Sum.inr (bxStartLink pcode M s k, b)))) +
      h' (Sum.inl (Sum.inr (Sum.inr (bxEndLink pcode M s k, b)))) := by
    dsimp [bdlStepXCheckZ, bdlDeltaX1]
    simp_rw [add_mul, Finset.sum_add_distrib]
    rw [Finset.sum_eq_single (Sum.inr (Sum.inl (mkOuterShellSegment pcode M s k, 0)))]
    · rw [Finset.sum_eq_single (Sum.inr (Sum.inl (mkOuterShellSegment pcode M s k, b.succ)))]
      · rw [Finset.sum_eq_single (Sum.inr (Sum.inr (bxStartLink pcode M s k, b)))]
        · rw [Finset.sum_eq_single (Sum.inr (Sum.inr (bxEndLink pcode M s k, b)))]
          · simp
          · intro qX _ hne; rw [if_neg hne, zero_mul]
          · intro h_abs; exact False.elim (h_abs (Finset.mem_univ _))
        · intro qX _ hne; rw [if_neg hne, zero_mul]
        · intro h_abs; exact False.elim (h_abs (Finset.mem_univ _))
      · intro qX _ hne; rw [if_neg hne, zero_mul]
      · intro h_abs; exact False.elim (h_abs (Finset.mem_univ _))
    · intro qX _ hne; rw [if_neg hne, zero_mul]
    · intro h_abs; exact False.elim (h_abs (Finset.mem_univ _))
  rw [hX, h_az0, h_az1, zero_add, zero_add] at h_syn
  have h2 := zmod2_add_self (h' (Sum.inl (Sum.inr (Sum.inr (bxEndLink pcode M s k, b)))))
  linear_combination h_syn - h2

end WeldedHierarchy
