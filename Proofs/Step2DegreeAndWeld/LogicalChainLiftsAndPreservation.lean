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

import Proofs.Step1LLLDensity.SphericalCapAndLLL

/-!
# Logical Cochain/Cycle Lifts and Inductive Logical Qubit Preservation

Constructs explicit primal and dual logical chain lifts (`liftCylinderLZ`, `liftCylinderLX`) across `bdlCylinderStepX` and proves syndrome vanishing (`cylinder_syndrome_primal_lift`, `cylinder_syndrome_dual_lift`) together with symplectic pairing invariance (`cylinder_dualPairing_lift`). Verifies the nontrivial dual logical pair on the planar surface code seed (`bdlSurfaceSeedCode_hasDualLogicalPair`) and transports `HasDualLogicalPair` and `HasLogicalQubit` inductively to `bdlWeldedCode k` (`bdlWeldedCode_hasDualLogicalPair`).

## References

* Part I, Section 2.1 (`subsec:css-complexes`), Lemma 2.3 (`lem:seed-code`)
* Part I, Section 2.3 (`subsec:step2-mapping-cone`), Definition 2.5 (`def:three-layer-mapping-cone`), Proposition 2.6 (`prop:mapping-cone-invariants`)
* Part I, Section 3.2 (`subsec:nilpotent-hpl`), Proposition 3.7 (`prop:classical-hpl`), Equation (18) (`eq:degree1-lift-intertwining`)
-/

noncomputable section

open scoped Classical BigOperators

/-! ## 1. Relative Homology Exact Sequence and Logical Qubit Preservation $k_{\mathrm{log}} = 1$ -/

/-- Bilinear $\mathbb{F}_2$ pairing $\langle g_1, g_2 \rangle = \sum_q g_1(q) g_2(q)$. -/
def dualPairing {Q : Type} [Fintype Q] (g1 g2 : Q → ZMod 2) : ZMod 2 :=
  ∑ q : Q, g1 q * g2 q

lemma dualPairing_comm {Q : Type} [Fintype Q] (g1 g2 : Q → ZMod 2) :
    dualPairing g1 g2 = dualPairing g2 g1 := by
  dsimp [dualPairing]
  exact Finset.sum_congr rfl (fun _ _ => mul_comm _ _)

/-- Any 1-boundary `checkGen code c2` is orthogonal under `dualPairing` to any dual 1-cycle `L_Z`. -/
lemma dualPairing_checkGen_zero {Q M_Z M_X : Type}
    [Fintype Q] [DecidableEq Q] [Fintype M_Z] [DecidableEq M_Z] [Fintype M_X] [DecidableEq M_X]
    (code : CSSCode3D Q M_Z M_X) (c2 : M_Z → ZMod 2) (L_Z : Q → ZMod 2)
    (h_dual_cycle : syndrome (dualCode code) L_Z = 0) :
    dualPairing L_Z (checkGen code c2) = 0 := by
  dsimp [dualPairing, checkGen, f2CheckGen]
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_eq_zero
  intro mZ _
  have h_mZ : syndrome (dualCode code) L_Z mZ = 0 := by rw [h_dual_cycle]; rfl
  dsimp [syndrome, f2Syndrome, dualCode, dualF2ChainComplex] at h_mZ
  have h_factor : (∑ x : Q, L_Z x * (code.checkZ mZ x * c2 mZ)) =
      (∑ x : Q, code.checkZ mZ x * L_Z x) * c2 mZ := by
    rw [Finset.sum_mul]
    exact Finset.sum_congr rfl (fun _ _ => by ring)
  rw [h_factor, h_mZ, zero_mul]

/-- Any `HasDualLogicalPair code` certifies `HasLogicalQubit code`. -/
theorem hasLogicalQubit_of_hasDualLogicalPair {Q M_Z M_X : Type}
    [Fintype Q] [DecidableEq Q] [Fintype M_Z] [DecidableEq M_Z] [Fintype M_X] [DecidableEq M_X]
    {code : CSSCode3D Q M_Z M_X} (h : HasDualLogicalPair code) :
    HasLogicalQubit code := by
  rcases h with ⟨p⟩
  refine ⟨p.L_X, p.h_syn_X, fun c2 h_eq => ?_⟩
  have h0 := dualPairing_checkGen_zero code c2 p.L_Z p.h_syn_Z
  rw [h_eq] at h0
  dsimp [dualPairing] at h0
  rw [p.h_pair] at h0
  exact one_ne_zero h0

/-- Swapping `(L_Z, L_X)` transports `HasDualLogicalPair` from `code` to `dualCode code`. -/
theorem hasDualLogicalPair_dual {Q M_Z M_X : Type}
    [Fintype Q] [DecidableEq Q] [Fintype M_Z] [DecidableEq M_Z] [Fintype M_X] [DecidableEq M_X]
    {code : CSSCode3D Q M_Z M_X} (h : HasDualLogicalPair code) :
    HasDualLogicalPair (dualCode code) := by
  rcases h with ⟨p⟩
  refine ⟨⟨p.L_X, p.L_Z, p.h_syn_X, p.h_syn_Z, ?_⟩⟩
  have hp := p.h_pair
  simpa only [mul_comm] using hp

/-! ## 2. Cylinder Cochain Lift Maps and Radial Shell Telescoping -/

/-- Logical operator values on `BoundaryX0Link pcode M` (`boundaryX0LinkLZ`). -/
def boundaryX0LinkLZ {Q M_Z M_X : Type}
    [Fintype Q] [DecidableEq Q] [Fintype M_Z] [DecidableEq M_Z] [Fintype M_X] [DecidableEq M_X]
    (pcode : CSSCode3D Q M_Z M_X) (M : ℕ) (L : Q → ZMod 2)
    (xv : BoundaryX0Link pcode M) : ZMod 2 :=
  match xv.val.2 with
  | Sum.inl q => pcode.checkX xv.val.1 q * L q
  | Sum.inr _ => 0

/-- Logical operator values on `Xq0 pcode M` (`xq0LZ`). -/
def xq0LZ {Q M_Z M_X : Type}
    [Fintype Q] [DecidableEq Q] [Fintype M_Z] [DecidableEq M_Z] [Fintype M_X] [DecidableEq M_X]
    (pcode : CSSCode3D Q M_Z M_X) (M : ℕ) (L : Q → ZMod 2) :
    Xq0 pcode M → ZMod 2
  | Sum.inl q => L q
  | Sum.inr _ => 0

/-- Lifted primal logical representative `liftCylinderLZ` on `BDLStepXQ pcode M`. -/
def liftCylinderLZ {Q M_Z M_X : Type}
    [Fintype Q] [DecidableEq Q] [Fintype M_Z] [DecidableEq M_Z] [Fintype M_X] [DecidableEq M_X]
    (pcode : CSSCode3D Q M_Z M_X) (M : ℕ) (L : Q → ZMod 2) :
    BDLStepXQ pcode M → ZMod 2
  | Sum.inl (Sum.inl (sv, b)) => if b = 0 then boundaryX0LinkLZ pcode M L sv.val.val.1 else 0
  | Sum.inl (Sum.inr _) => 0
  | Sum.inr (v0, b) => if b = 0 then xq0LZ pcode M L v0 else 0

/-- Lifted dual logical representative `liftCylinderLX` on `BDLStepXQ pcode M`. -/
def liftCylinderLX {Q M_Z M_X : Type}
    [Fintype Q] [DecidableEq Q] [Fintype M_Z] [DecidableEq M_Z] [Fintype M_X] [DecidableEq M_X]
    (pcode : CSSCode3D Q M_Z M_X) (M : ℕ) (L : Q → ZMod 2) :
    BDLStepXQ pcode M → ZMod 2
  | Sum.inl _ => 0
  | Sum.inr (v0, _) => L (xq0OwnerQ pcode M v0)

lemma sum_boundaryX0LinkLZ_eq {Q M_Z M_X : Type}
    [Fintype Q] [DecidableEq Q] [Fintype M_Z] [DecidableEq M_Z] [Fintype M_X] [DecidableEq M_X]
    (pcode : CSSCode3D Q M_Z M_X) (M : ℕ) (L : Q → ZMod 2) (x0 : M_X) :
    (∑ xv : BoundaryX0Link pcode M, if xv.val.1 = x0 then boundaryX0LinkLZ pcode M L xv else 0) =
    ∑ q : Q, pcode.checkX x0 q * L q := by
  let f : M_X × BoundaryX0 pcode M → ZMod 2 := fun p =>
    if p.1 = x0 then
      match p.2 with
      | Sum.inl q => pcode.checkX p.1 q * L q
      | Sum.inr _ => 0
    else 0
  have h1 : (∑ xv : BoundaryX0Link pcode M, if xv.val.1 = x0 then boundaryX0LinkLZ pcode M L xv else 0) =
      ∑ p ∈ Finset.univ.filter (fun p : M_X × BoundaryX0 pcode M => InLinkOfX pcode M p.1 p.2), f p :=
    (Finset.sum_subtype (Finset.univ.filter (fun p : M_X × BoundaryX0 pcode M => InLinkOfX pcode M p.1 p.2))
      (p := fun p : M_X × BoundaryX0 pcode M => InLinkOfX pcode M p.1 p.2)
      (fun _ => Finset.mem_filter.trans (and_iff_right (Finset.mem_univ _)))
      f).symm
  have h2 : (∑ p ∈ Finset.univ.filter (fun p : M_X × BoundaryX0 pcode M => InLinkOfX pcode M p.1 p.2), f p) =
      ∑ p : M_X × BoundaryX0 pcode M, if InLinkOfX pcode M p.1 p.2 then f p else 0 :=
    Finset.sum_filter (fun p : M_X × BoundaryX0 pcode M => InLinkOfX pcode M p.1 p.2) f
  rw [h1, h2, Fintype.sum_prod_type]
  rw [Finset.sum_eq_single x0]
  · rw [Fintype.sum_sum_type]
    have h_inr : (∑ v23 : (ActiveZ pcode × Fin M) ⊕ M_Z,
        if InLinkOfX pcode M x0 (Sum.inr v23) then f (x0, Sum.inr v23) else 0) = 0 := by
      apply Finset.sum_eq_zero; intro v23 _; dsimp [f]; simp
    rw [h_inr, add_zero]
    apply Finset.sum_congr rfl; intro q _; dsimp [f, InLinkOfX]
    by_cases hx : pcode.checkX x0 q = 0 <;> simp [hx]
  · intro x _ hne; apply Finset.sum_eq_zero; intro v _; dsimp [f]; simp [hne]
  · intro h_abs; exact False.elim (h_abs (Finset.mem_univ x0))

lemma sum_gXQ0_liftCylinderLZ {Q M_Z M_X : Type}
    [Fintype Q] [DecidableEq Q] [Fintype M_Z] [DecidableEq M_Z] [Fintype M_X] [DecidableEq M_X]
    (pcode : CSSCode3D Q M_Z M_X) (M : ℕ) (L : Q → ZMod 2)
    (sv0 : ShellVertex pcode M) (b0 : Fin 3) :
    (∑ qQ : BDLCQ1 pcode M, bdlGXQ0 pcode M (Sum.inr (sv0, b0)) qQ *
      liftCylinderLZ pcode M L (Sum.inr qQ)) =
    if sv0.val.2 = Fin.last M ∧ b0 = 0 then boundaryX0LinkLZ pcode M L sv0.val.1 else 0 := by
  let xv := sv0.val.1
  let r0 := sv0.val.2
  rw [Fintype.sum_prod_type, Finset.sum_comm]
  rw [Finset.sum_eq_single (0 : Fin 3)]
  · rw [Fintype.sum_sum_type]
    have h_inr : (∑ v23 : (ActiveZ pcode × Fin M) ⊕ ActiveZ pcode,
        bdlGXQ0 pcode M (Sum.inr (sv0, b0)) (Sum.inr v23, 0) *
        liftCylinderLZ pcode M L (Sum.inr (Sum.inr v23, 0))) = 0 := by
      apply Finset.sum_eq_zero; intro v23 _; dsimp [liftCylinderLZ, xq0LZ]; simp
    rw [h_inr, add_zero]
    rcases h_xv : xv.val.2 with q0 | v_other
    · rw [Finset.sum_eq_single q0]
      · dsimp [bdlGXQ0, liftCylinderLZ, xq0LZ, boundaryX0LinkLZ, projXq0ToBoundaryX0, xq0OwnerQ]
        change (if r0 = Fin.last M ∧ xv.val.2 = Sum.inl q0 ∧ b0 = 0 then pcode.checkX xv.val.1 q0 else 0) * L q0 =
          if r0 = Fin.last M ∧ b0 = 0 then
            (match xv.val.2 with | Sum.inl q => pcode.checkX xv.val.1 q * L q | Sum.inr _ => 0)
          else 0
        rw [h_xv]
        by_cases hc : r0 = Fin.last M ∧ b0 = 0
        · rcases hc with ⟨hr0, hb0⟩; rw [if_pos ⟨hr0, rfl, hb0⟩, if_pos ⟨hr0, hb0⟩]
        · have hc' : ¬ (r0 = Fin.last M ∧ (Sum.inl q0 : BoundaryX0 pcode M) = Sum.inl q0 ∧ b0 = 0) :=
            fun h => hc ⟨h.1, h.2.2⟩
          rw [if_neg hc', if_neg hc, zero_mul]
      · intro q _ hne
        dsimp [bdlGXQ0, liftCylinderLZ, xq0LZ, projXq0ToBoundaryX0]
        change (if r0 = Fin.last M ∧ xv.val.2 = Sum.inl q ∧ b0 = 0 then pcode.checkX xv.val.1 q else 0) * L q = 0
        rw [h_xv]
        have hc' : ¬ (r0 = Fin.last M ∧ (Sum.inl q0 : BoundaryX0 pcode M) = Sum.inl q ∧ b0 = 0) :=
          fun h => hne (Sum.inl.inj h.2.1).symm
        rw [if_neg hc', zero_mul]
      · intro h_abs; exact False.elim (h_abs (Finset.mem_univ q0))
    · have h_zero : (∑ q : Q, bdlGXQ0 pcode M (Sum.inr (sv0, b0)) (Sum.inl q, 0) *
          liftCylinderLZ pcode M L (Sum.inr (Sum.inl q, 0))) = 0 := by
        apply Finset.sum_eq_zero; intro q _
        dsimp [bdlGXQ0, projXq0ToBoundaryX0]
        change (if r0 = Fin.last M ∧ xv.val.2 = Sum.inl q ∧ b0 = 0 then pcode.checkX xv.val.1 q else 0) * _ = 0
        rw [h_xv]; simp
      rw [h_zero]
      dsimp [boundaryX0LinkLZ]
      change (0 : ZMod 2) = if r0 = Fin.last M ∧ b0 = 0 then
        (match xv.val.2 with | Sum.inl q => pcode.checkX xv.val.1 q * L q | Sum.inr _ => 0) else 0
      rw [h_xv]; simp
  · intro b _ hne; apply Finset.sum_eq_zero; intro v0 _; dsimp [liftCylinderLZ]; rw [if_neg hne, mul_zero]
  · intro h_abs; exact False.elim (h_abs (Finset.mem_univ 0))

lemma sum_shellVertex_eq {Q M_Z M_X : Type}
    [Fintype Q] [DecidableEq Q] [Fintype M_Z] [DecidableEq M_Z] [Fintype M_X] [DecidableEq M_X]
    (pcode : CSSCode3D Q M_Z M_X) (M : ℕ) (f : ShellVertex pcode M → ZMod 2) :
    (∑ sv : ShellVertex pcode M, f sv) =
    ∑ xv : BoundaryX0Link pcode M, ∑ r : Fin (M + 1),
      if h : InShellR pcode M xv r then f ⟨(xv, r), h⟩ else 0 := by
  let g : BoundaryX0Link pcode M × Fin (M + 1) → ZMod 2 :=
    fun p => if h : InShellR pcode M p.1 p.2 then f ⟨p, h⟩ else 0
  have h0 : (∑ sv : ShellVertex pcode M, f sv) = ∑ sv : ShellVertex pcode M, g sv.val :=
    Finset.sum_congr rfl (fun sv _ => by dsimp [g]; rw [dif_pos sv.property])
  have h1 : (∑ sv : ShellVertex pcode M, g sv.val) =
      ∑ p ∈ Finset.univ.filter (fun p : BoundaryX0Link pcode M × Fin (M + 1) => InShellR pcode M p.1 p.2), g p :=
    (Finset.sum_subtype (Finset.univ.filter (fun p : BoundaryX0Link pcode M × Fin (M + 1) => InShellR pcode M p.1 p.2))
      (p := fun p : BoundaryX0Link pcode M × Fin (M + 1) => InShellR pcode M p.1 p.2)
      (fun _ => Finset.mem_filter.trans (and_iff_right (Finset.mem_univ _)))
      g).symm
  have h2 : (∑ p ∈ Finset.univ.filter (fun p : BoundaryX0Link pcode M × Fin (M + 1) => InShellR pcode M p.1 p.2), g p) =
      ∑ p : BoundaryX0Link pcode M × Fin (M + 1), if InShellR pcode M p.1 p.2 then g p else 0 :=
    Finset.sum_filter (fun p : BoundaryX0Link pcode M × Fin (M + 1) => InShellR pcode M p.1 p.2) g
  rw [h0, h1, h2, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl (fun xv _ => Finset.sum_congr rfl (fun r _ => ?_))
  dsimp [g]; split_ifs with h <;> rfl

lemma inShellR_of_boundaryX0LinkLZ_ne_zero {Q M_Z M_X : Type}
    [Fintype Q] [DecidableEq Q] [Fintype M_Z] [DecidableEq M_Z] [Fintype M_X] [DecidableEq M_X]
    (pcode : CSSCode3D Q M_Z M_X) (M : ℕ) (L : Q → ZMod 2)
    (xv : BoundaryX0Link pcode M) (r : Fin (M + 1)) (hne : boundaryX0LinkLZ pcode M L xv ≠ 0) :
    InShellR pcode M xv r := by
  rcases xv with ⟨⟨x, v⟩, hp⟩; rcases v with q | _ <;> [trivial; exact False.elim (hne rfl)]

lemma radialParentLink_of_boundaryX0LinkLZ_ne_zero {Q M_Z M_X : Type}
    [Fintype Q] [DecidableEq Q] [Fintype M_Z] [DecidableEq M_Z] [Fintype M_X] [DecidableEq M_X]
    (pcode : CSSCode3D Q M_Z M_X) (M : ℕ) (L : Q → ZMod 2)
    (xv : BoundaryX0Link pcode M) (r : Fin (M + 1)) (hne : boundaryX0LinkLZ pcode M L xv ≠ 0) :
    radialParentLink pcode M xv r = xv := by
  rcases xv with ⟨⟨x, v⟩, hp⟩; rcases v with q | _ <;> [rfl; exact False.elim (hne rfl)]

lemma not_isDiagZeroVertex_of_boundaryX0LinkLZ_ne_zero {Q M_Z M_X : Type}
    [Fintype Q] [DecidableEq Q] [Fintype M_Z] [DecidableEq M_Z] [Fintype M_X] [DecidableEq M_X]
    (pcode : CSSCode3D Q M_Z M_X) (M : ℕ) (L : Q → ZMod 2)
    (xv : BoundaryX0Link pcode M) (r : Fin (M + 1)) (h : InShellR pcode M xv r)
    (hne : boundaryX0LinkLZ pcode M L xv ≠ 0) :
    ¬ IsDiagZeroVertex pcode M ⟨(xv, r), h⟩ := by
  rintro ⟨_, z, hz⟩; dsimp [boundaryX0LinkLZ] at hne hz; rw [hz] at hne; exact hne rfl

def bdlDeltaX0Shell {Q M_Z M_X : Type}
    [Fintype Q] [DecidableEq Q] [Fintype M_Z] [DecidableEq M_Z] [Fintype M_X] [DecidableEq M_X]
    (pcode : CSSCode3D Q M_Z M_X) (M : ℕ) (mX : BDLStepXMX pcode M)
    (sv : ShellVertex pcode M) (b : Fin 3) : ZMod 2 :=
  if h_nd : ¬ IsDiagZeroVertex pcode M sv then
    bdlDeltaX0 pcode M mX (Sum.inl (⟨sv, h_nd⟩, b))
  else 0

lemma bdlDeltaX0Shell_eq_ite {Q M_Z M_X : Type}
    [Fintype Q] [DecidableEq Q] [Fintype M_Z] [DecidableEq M_Z] [Fintype M_X] [DecidableEq M_X]
    (pcode : CSSCode3D Q M_Z M_X) (M : ℕ) (mX : BDLStepXMX pcode M)
    (sv : ShellVertex pcode M) (b : Fin 3) :
    bdlDeltaX0Shell pcode M mX sv b =
      if sv.val.2.val = 0 then
        if IsDiagZeroVertex pcode M sv then 0
        else
          (if mX = Sum.inl (sv.val.1.val.1, b) then 1 else 0) +
          (if mX = Sum.inr (sv, b) then 1 else 0)
      else
        (if mX = Sum.inr (radialParentVertex pcode M sv, b) then 1 else 0) +
        (if mX = Sum.inr (sv, b) then 1 else 0) := by
  dsimp [bdlDeltaX0Shell]
  by_cases h_nd : ¬ IsDiagZeroVertex pcode M sv
  · rw [dif_pos h_nd]; dsimp [bdlDeltaX0]
    by_cases hr0 : sv.val.2.val = 0
    · rw [if_pos hr0, if_pos hr0, if_neg h_nd]
    · rw [if_neg hr0, if_neg hr0]
  · rw [dif_neg h_nd]; push_neg at h_nd; rw [if_pos h_nd.1, if_pos h_nd]

lemma sum_radialVertex_bdlDeltaX0 {Q M_Z M_X : Type}
    [Fintype Q] [DecidableEq Q] [Fintype M_Z] [DecidableEq M_Z] [Fintype M_X] [DecidableEq M_X]
    (pcode : CSSCode3D Q M_Z M_X) (M : ℕ) (mX : BDLStepXMX pcode M)
    (g : ShellVertex pcode M → ZMod 2) :
    (∑ rv : RadialVertex pcode M, bdlDeltaX0 pcode M mX (Sum.inl (rv, 0)) * g rv.val) =
    ∑ sv : ShellVertex pcode M, bdlDeltaX0Shell pcode M mX sv 0 * g sv := by
  have h0 : (∑ rv : RadialVertex pcode M, bdlDeltaX0 pcode M mX (Sum.inl (rv, 0)) * g rv.val) =
      ∑ rv : RadialVertex pcode M, bdlDeltaX0Shell pcode M mX rv.val 0 * g rv.val :=
    Finset.sum_congr rfl (fun rv _ => by dsimp [bdlDeltaX0Shell]; rw [dif_pos rv.property])
  have h1 : (∑ rv : RadialVertex pcode M, bdlDeltaX0Shell pcode M mX rv.val 0 * g rv.val) =
      ∑ sv ∈ Finset.univ.filter (fun sv : ShellVertex pcode M => ¬ IsDiagZeroVertex pcode M sv),
        bdlDeltaX0Shell pcode M mX sv 0 * g sv :=
    (Finset.sum_subtype (Finset.univ.filter (fun sv : ShellVertex pcode M => ¬ IsDiagZeroVertex pcode M sv))
      (p := fun sv : ShellVertex pcode M => ¬ IsDiagZeroVertex pcode M sv)
      (fun _ => Finset.mem_filter.trans (and_iff_right (Finset.mem_univ _)))
      (fun sv => bdlDeltaX0Shell pcode M mX sv 0 * g sv)).symm
  have h2 : (∑ sv ∈ Finset.univ.filter (fun sv : ShellVertex pcode M => ¬ IsDiagZeroVertex pcode M sv),
        bdlDeltaX0Shell pcode M mX sv 0 * g sv) =
      ∑ sv : ShellVertex pcode M,
        if ¬ IsDiagZeroVertex pcode M sv then bdlDeltaX0Shell pcode M mX sv 0 * g sv else 0 :=
    Finset.sum_filter (fun sv : ShellVertex pcode M => ¬ IsDiagZeroVertex pcode M sv)
      (fun sv => bdlDeltaX0Shell pcode M mX sv 0 * g sv)
  rw [h0, h1, h2]
  refine Finset.sum_congr rfl (fun sv _ => ?_)
  by_cases h_nd : ¬ IsDiagZeroVertex pcode M sv
  · rw [if_pos h_nd]
  · rw [if_neg h_nd]; dsimp [bdlDeltaX0Shell]; rw [dif_neg h_nd, zero_mul]

lemma sum_radial_deltaX0_shell_eq {Q M_Z M_X : Type}
    [Fintype Q] [DecidableEq Q] [Fintype M_Z] [DecidableEq M_Z] [Fintype M_X] [DecidableEq M_X]
    (pcode : CSSCode3D Q M_Z M_X) (M : ℕ) (L : Q → ZMod 2)
    (sv0 : ShellVertex pcode M) (xv : BoundaryX0Link pcode M)
    (hne : boundaryX0LinkLZ pcode M L xv ≠ 0) :
    (∑ r : Fin (M + 1),
      (if h : InShellR pcode M xv r then
        bdlDeltaX0Shell pcode M (Sum.inr (sv0, 0)) ⟨(xv, r), h⟩ 0
      else 0)) =
    if xv = sv0.val.1 ∧ sv0.val.2 = Fin.last M then 1 else 0 := by
  have h_in_all : ∀ r : Fin (M + 1), InShellR pcode M xv r :=
    fun r => inShellR_of_boundaryX0LinkLZ_ne_zero pcode M L xv r hne
  have h_par_all : ∀ r : Fin (M + 1), radialParentLink pcode M xv r = xv :=
    fun r => radialParentLink_of_boundaryX0LinkLZ_ne_zero pcode M L xv r hne
  by_cases hxv : xv = sv0.val.1
  · subst hxv
    let r0 := sv0.val.2
    have h_term : ∀ r : Fin (M + 1),
        (if h : InShellR pcode M sv0.val.1 r then
          bdlDeltaX0Shell pcode M (Sum.inr (sv0, 0)) ⟨(sv0.val.1, r), h⟩ 0
        else 0) =
        (if r.val = 0 then 0 else if r0 = finPred r then 1 else 0) +
        (if r = r0 then 1 else 0) := by
      intro r
      rw [dif_pos (h_in_all r), bdlDeltaX0Shell_eq_ite]
      dsimp only
      by_cases hr : r.val = 0
      · rw [if_pos hr, if_pos hr]
        have h_eq : ((Sum.inr (sv0, (0 : Fin 3)) : BDLStepXMX pcode M) =
            Sum.inr (⟨(sv0.val.1, r), h_in_all r⟩, 0)) ↔ r = r0 := by
          constructor
          · intro h; injection h with h; injection h with h _; exact (congr_arg (fun u : ShellVertex pcode M => u.val.2) h).symm
          · intro h; subst h; rfl
        have h_nd := not_isDiagZeroVertex_of_boundaryX0LinkLZ_ne_zero pcode M L sv0.val.1 r (h_in_all r) hne
        simp [h_nd, h_eq]
      · rw [if_neg hr, if_neg hr]
        have h_eq1 : ((Sum.inr (sv0, (0 : Fin 3)) : BDLStepXMX pcode M) =
            Sum.inr (radialParentVertex pcode M ⟨(sv0.val.1, r), h_in_all r⟩, 0)) ↔ r0 = finPred r := by
          constructor
          · intro h; injection h with h; injection h with h _
            exact congr_arg (fun u : ShellVertex pcode M => u.val.2) h
          · intro h; congr 2; apply Subtype.ext; apply Prod.ext
            · exact (h_par_all r).symm
            · exact h
        have h_eq2 : ((Sum.inr (sv0, (0 : Fin 3)) : BDLStepXMX pcode M) =
            Sum.inr (⟨(sv0.val.1, r), h_in_all r⟩, 0)) ↔ r = r0 := by
          constructor
          · intro h; injection h with h; injection h with h _; exact (congr_arg (fun u : ShellVertex pcode M => u.val.2) h).symm
          · intro h; subst h; rfl
        simp [h_eq1, h_eq2]
    simp_rw [h_term, Finset.sum_add_distrib]
    have h_second : (∑ r : Fin (M + 1), if r = r0 then (1 : ZMod 2) else 0) = 1 := by
      rw [Finset.sum_eq_single r0]
      · simp
      · intro r _ hne'; simp [hne']
      · intro h_abs; exact False.elim (h_abs (Finset.mem_univ r0))
    rw [h_second]
    by_cases hr_last : r0 = Fin.last M
    · have h_first : (∑ r : Fin (M + 1), if r.val = 0 then (0 : ZMod 2) else if r0 = finPred r then 1 else 0) = 0 := by
        apply Finset.sum_eq_zero; intro r _; split_ifs with hr0 h_fp
        · rfl
        · exfalso
          have h_lt : (finPred r).val < M := by dsimp [finPred]; omega
          have h_eq_M : r0.val = M := by rw [hr_last]; rfl
          omega
        · rfl
      rw [h_first, zero_add]
      have hr_last' : sv0.val.2 = Fin.last M := hr_last
      simp [hr_last']
    · have hr0_lt : r0.val < M :=
        Nat.lt_of_le_of_ne (Nat.le_of_lt_succ r0.isLt) (fun h_eq => hr_last (Fin.ext h_eq))
      let r_succ : Fin (M + 1) := ⟨r0.val + 1, Nat.succ_lt_succ hr0_lt⟩
      have h_first : (∑ r : Fin (M + 1), if r.val = 0 then (0 : ZMod 2) else if r0 = finPred r then 1 else 0) = 1 := by
        rw [Finset.sum_eq_single r_succ]
        · have hr_nz : r_succ.val ≠ 0 := Nat.succ_ne_zero r0.val
          have h_fp : r0 = finPred r_succ := by ext; dsimp [finPred, r_succ]
          rw [if_neg hr_nz, if_pos h_fp]
        · intro r _ hne'; split_ifs with hr0 h_fp
          · rfl
          · exfalso; apply hne'; ext
            dsimp [finPred] at h_fp
            have h_val : r0.val = r.val - 1 := congr_arg Fin.val h_fp
            dsimp [r_succ]; omega
          · rfl
        · intro h_abs; exact False.elim (h_abs (Finset.mem_univ r_succ))
      rw [h_first]
      have hr_last' : sv0.val.2 ≠ Fin.last M := hr_last
      simp [hr_last']
  · have hc : ¬ (xv = sv0.val.1 ∧ sv0.val.2 = Fin.last M) := fun h => hxv h.1
    rw [if_neg hc]; apply Finset.sum_eq_zero; intro r _
    rw [dif_pos (h_in_all r), bdlDeltaX0Shell_eq_ite]; dsimp only
    have h1 : (Sum.inr (sv0, (0 : Fin 3)) : BDLStepXMX pcode M) ≠
        Sum.inr (radialParentVertex pcode M ⟨(xv, r), h_in_all r⟩, 0) := by
      intro h; injection h with h; injection h with h _
      have h_link : sv0.val.1 = radialParentLink pcode M xv r := congr_arg (fun u : ShellVertex pcode M => u.val.1) h
      rw [h_par_all r] at h_link; exact hxv h_link.symm
    have h2 : (Sum.inr (sv0, (0 : Fin 3)) : BDLStepXMX pcode M) ≠ Sum.inr (⟨(xv, r), h_in_all r⟩, 0) := by
      intro h; injection h with h; injection h with h _; exact hxv (congr_arg (fun u : ShellVertex pcode M => u.val.1) h).symm
    by_cases hr : r.val = 0
    · have h_nd := not_isDiagZeroVertex_of_boundaryX0LinkLZ_ne_zero pcode M L xv r (h_in_all r) hne
      rw [if_pos hr, if_neg h_nd, if_neg h2]; simp
    · rw [if_neg hr, if_neg h1, if_neg h2]; simp

/-! ## 3. Primal and Dual Syndrome Vanishing and Symplectic Pairing Invariance -/

lemma cylinder_syndrome_primal_lift {Q M_Z M_X : Type}
    [Fintype Q] [DecidableEq Q] [Fintype M_Z] [DecidableEq M_Z] [Fintype M_X] [DecidableEq M_X]
    (pcode : CSSCode3D Q M_Z M_X) (M : ℕ) (L : Q → ZMod 2) (h_syn : syndrome pcode L = 0) :
    syndrome (bdlCylinderStepX pcode M) (liftCylinderLZ pcode M L) = 0 := by
  ext mX
  simp only [syndrome, f2Syndrome, bdlCylinderStepX, AddMonoidHom.coe_mk, ZeroHom.coe_mk, Pi.zero_apply]
  rw [Fintype.sum_sum_type]
  have h_qX : (∑ qX : BDLCX1 pcode M, bdlStepXCheckX pcode M mX (Sum.inl qX) *
      liftCylinderLZ pcode M L (Sum.inl qX)) =
      ∑ xv : BoundaryX0Link pcode M,
        (∑ r : Fin (M + 1), if h : InShellR pcode M xv r then bdlDeltaX0Shell pcode M mX ⟨(xv, r), h⟩ 0 else 0) *
        boundaryX0LinkLZ pcode M L xv := by
    rw [Fintype.sum_sum_type]
    have h_inr : (∑ qX23 : (ShellSegment pcode M × Fin 3) ⊕ (BoundaryX0Link pcode M × Fin 2),
        bdlStepXCheckX pcode M mX (Sum.inl (Sum.inr qX23)) * liftCylinderLZ pcode M L (Sum.inl (Sum.inr qX23))) = 0 :=
      Finset.sum_eq_zero (fun _ _ => by dsimp [liftCylinderLZ]; simp)
    rw [h_inr, add_zero, Fintype.sum_prod_type]
    have h_b : ∀ sv : RadialVertex pcode M,
        (∑ b : Fin 3, bdlStepXCheckX pcode M mX (Sum.inl (Sum.inl (sv, b))) *
          liftCylinderLZ pcode M L (Sum.inl (Sum.inl (sv, b)))) =
        bdlDeltaX0 pcode M mX (Sum.inl (sv, 0)) * boundaryX0LinkLZ pcode M L sv.val.val.1 := by
      intro sv; rw [Finset.sum_eq_single (0 : Fin 3)]
      · dsimp [bdlStepXCheckX, liftCylinderLZ]
      · intro b _ hne; dsimp [liftCylinderLZ]; rw [if_neg hne, mul_zero]
      · intro h_abs; exact False.elim (h_abs (Finset.mem_univ 0))
    simp_rw [h_b]
    rw [sum_radialVertex_bdlDeltaX0 pcode M mX (fun sv => boundaryX0LinkLZ pcode M L sv.val.1)]
    rw [sum_shellVertex_eq pcode M (fun sv => bdlDeltaX0Shell pcode M mX sv 0 * boundaryX0LinkLZ pcode M L sv.val.1)]
    refine Finset.sum_congr rfl (fun xv _ => ?_)
    rw [Finset.sum_mul]; refine Finset.sum_congr rfl (fun r _ => ?_); split_ifs with h <;> [rfl; rw [zero_mul]]
  rw [h_qX]
  rcases mX with ⟨x0, b0⟩ | ⟨sv0, b0⟩
  · have h_qQ : (∑ qQ : BDLCQ1 pcode M, bdlStepXCheckX pcode M (Sum.inl (x0, b0)) (Sum.inr qQ) *
        liftCylinderLZ pcode M L (Sum.inr qQ)) = 0 := Finset.sum_eq_zero (fun _ _ => zero_mul _)
    rw [h_qQ, add_zero]
    by_cases hb0 : b0 = 0
    · subst hb0
      have h_inner : ∀ xv : BoundaryX0Link pcode M,
          (∑ r : Fin (M + 1), if h : InShellR pcode M xv r then bdlDeltaX0Shell pcode M (Sum.inl (x0, 0)) ⟨(xv, r), h⟩ 0 else 0) *
          boundaryX0LinkLZ pcode M L xv = if xv.val.1 = x0 then boundaryX0LinkLZ pcode M L xv else 0 := by
        intro xv
        by_cases h_lz : boundaryX0LinkLZ pcode M L xv = 0
        · rw [h_lz, mul_zero]; split_ifs <;> rfl
        · have h_in0 : InShellR pcode M xv 0 := inShellR_of_boundaryX0LinkLZ_ne_zero pcode M L xv 0 h_lz
          rw [Finset.sum_eq_single (0 : Fin (M + 1))]
          · rw [dif_pos h_in0, bdlDeltaX0Shell_eq_ite]; dsimp only
            have h_nd := not_isDiagZeroVertex_of_boundaryX0LinkLZ_ne_zero pcode M L xv 0 h_in0 h_lz
            have h_eq : ((Sum.inl (x0, (0 : Fin 3)) : BDLStepXMX pcode M) = Sum.inl (xv.val.1, 0)) ↔ xv.val.1 = x0 := by simp [eq_comm]
            by_cases hx : xv.val.1 = x0 <;> simp [h_nd, h_eq, hx]
          · intro r _ hne
            have hr_nz : r.val ≠ 0 := fun h => hne (Fin.ext h)
            split_ifs with h_in <;> [ (rw [bdlDeltaX0Shell_eq_ite]; dsimp only; rw [if_neg hr_nz]; simp); rfl]
          · intro h_abs; exact False.elim (h_abs (Finset.mem_univ 0))
      simp_rw [h_inner]; rw [sum_boundaryX0LinkLZ_eq pcode M L x0]; exact congr_fun h_syn x0
    · apply Finset.sum_eq_zero; intro xv _
      have h_sum0 : (∑ r : Fin (M + 1), if h : InShellR pcode M xv r then bdlDeltaX0Shell pcode M (Sum.inl (x0, b0)) ⟨(xv, r), h⟩ 0 else 0) = 0 := by
        apply Finset.sum_eq_zero; intro r _; split_ifs with h_in
        · rw [bdlDeltaX0Shell_eq_ite]; dsimp only
          have h1 : (Sum.inl (x0, b0) : BDLStepXMX pcode M) ≠ Sum.inl (xv.val.1, 0) := by
            intro h; injection h with h; injection h with _ hb; exact hb0 hb
          by_cases hr0 : r.val = 0
          · by_cases h_diag : IsDiagZeroVertex pcode M ⟨(xv, r), h_in⟩ <;> [rw [if_pos hr0, if_pos h_diag]; (rw [if_pos hr0, if_neg h_diag, if_neg h1]; simp)]
          · rw [if_neg hr0]; simp
        · rfl
      rw [h_sum0, zero_mul]
  · dsimp [bdlStepXCheckX]; rw [sum_gXQ0_liftCylinderLZ pcode M L sv0 b0]
    by_cases hb0 : b0 = 0
    · subst hb0
      have h_term : ∀ xv : BoundaryX0Link pcode M,
          (∑ r : Fin (M + 1), if h : InShellR pcode M xv r then bdlDeltaX0Shell pcode M (Sum.inr (sv0, 0)) ⟨(xv, r), h⟩ 0 else 0) *
          boundaryX0LinkLZ pcode M L xv =
          if xv = sv0.val.1 then (if sv0.val.2 = Fin.last M then boundaryX0LinkLZ pcode M L sv0.val.1 else 0) else 0 := by
        intro xv
        by_cases h_lz : boundaryX0LinkLZ pcode M L xv = 0
        · rw [h_lz, mul_zero]; by_cases hxv : xv = sv0.val.1 <;> [ (subst hxv; rw [h_lz]; simp); simp [hxv]]
        · rw [sum_radial_deltaX0_shell_eq pcode M L sv0 xv h_lz]
          by_cases hxv : xv = sv0.val.1 <;> [ (subst hxv; by_cases hr : sv0.val.2 = Fin.last M <;> simp [hr]); simp [hxv]]
      simp_rw [h_term]; rw [Finset.sum_eq_single sv0.val.1]
      · rw [if_pos rfl]; by_cases hr : sv0.val.2 = Fin.last M <;> [simp [hr, zmod2_add_self]; simp [hr]]
      · intro xv _ hne; rw [if_neg hne]
      · intro h_abs; exact False.elim (h_abs (Finset.mem_univ sv0.val.1))
    · have h_zero : (∑ xv : BoundaryX0Link pcode M,
          (∑ r : Fin (M + 1), if h : InShellR pcode M xv r then bdlDeltaX0Shell pcode M (Sum.inr (sv0, b0)) ⟨(xv, r), h⟩ 0 else 0) *
          boundaryX0LinkLZ pcode M L xv) = 0 := by
        apply Finset.sum_eq_zero; intro xv _
        by_cases h_lz : boundaryX0LinkLZ pcode M L xv = 0
        · rw [h_lz, mul_zero]
        · have h_sum0 : (∑ r : Fin (M + 1), if h : InShellR pcode M xv r then bdlDeltaX0Shell pcode M (Sum.inr (sv0, b0)) ⟨(xv, r), h⟩ 0 else 0) = 0 := by
            apply Finset.sum_eq_zero; intro r _; split_ifs with h_in
            · rw [bdlDeltaX0Shell_eq_ite]; dsimp only
              have h1 : (Sum.inr (sv0, b0) : BDLStepXMX pcode M) ≠ Sum.inr (radialParentVertex pcode M ⟨(xv, r), h_in⟩, 0) := by
                intro h; injection h with h; injection h with _ hb; exact hb0 hb
              have h2 : (Sum.inr (sv0, b0) : BDLStepXMX pcode M) ≠ Sum.inr (⟨(xv, r), h_in⟩, 0) := by
                intro h; injection h with h; injection h with _ hb; exact hb0 hb
              by_cases hr0 : r.val = 0
              · have h_nd := not_isDiagZeroVertex_of_boundaryX0LinkLZ_ne_zero pcode M L xv r h_in h_lz
                rw [if_pos hr0, if_neg h_nd, if_neg h2]; simp
              · rw [if_neg hr0, if_neg h1, if_neg h2]; simp
            · rfl
          rw [h_sum0, zero_mul]
      have hc : ¬ (sv0.val.2 = Fin.last M ∧ b0 = 0) := fun h => hb0 h.2
      rw [h_zero, if_neg hc, add_zero]

lemma cylinder_syndrome_dual_lift {Q M_Z M_X : Type}
    [Fintype Q] [DecidableEq Q] [Fintype M_Z] [DecidableEq M_Z] [Fintype M_X] [DecidableEq M_X]
    (pcode : CSSCode3D Q M_Z M_X) (M : ℕ) (L : Q → ZMod 2) (h_syn : syndrome (dualCode pcode) L = 0) :
    syndrome (dualCode (bdlCylinderStepX pcode M)) (liftCylinderLX pcode M L) = 0 := by
  ext mZ
  simp only [syndrome, f2Syndrome, dualCode, dualF2ChainComplex, bdlCylinderStepX,
    AddMonoidHom.coe_mk, ZeroHom.coe_mk, Pi.zero_apply]
  rw [Fintype.sum_sum_type]
  have h_qX : (∑ qX : BDLCX1 pcode M, bdlStepXCheckZ pcode M mZ (Sum.inl qX) * liftCylinderLX pcode M L (Sum.inl qX)) = 0 :=
    Finset.sum_eq_zero (fun _ _ => by dsimp [liftCylinderLX]; simp)
  rw [h_qX, zero_add]
  rcases mZ with mZX | ⟨mZQ | mZZ⟩
  · exact Finset.sum_eq_zero (fun _ _ => zero_mul _)
  · dsimp [bdlStepXCheckZ]
    rcases mZQ with ⟨eZ, k, bZ⟩ | ⟨eZ, v⟩
    · have h_exp : ∀ qQ : BDLCQ1 pcode M,
          bdlDeltaQ1 pcode M (Sum.inl (eZ, k, bZ)) qQ * liftCylinderLX pcode M L (Sum.inr qQ) =
          (if qQ = (armStart pcode M eZ k, bZ) then 1 else 0) * liftCylinderLX pcode M L (Sum.inr qQ) +
          (if qQ = (armEnd pcode M eZ k, bZ) then 1 else 0) * liftCylinderLX pcode M L (Sum.inr qQ) := by
        intro qQ; dsimp [bdlDeltaQ1]; ring
      simp_rw [h_exp, Finset.sum_add_distrib]
      have h1 : (∑ qQ : BDLCQ1 pcode M, (if qQ = (armStart pcode M eZ k, bZ) then (1 : ZMod 2) else 0) *
          liftCylinderLX pcode M L (Sum.inr qQ)) = L eZ.val.1 := by
        rw [Finset.sum_eq_single (armStart pcode M eZ k, bZ)]
        · dsimp [liftCylinderLX]; rw [if_pos rfl, one_mul, xq0OwnerQ_armStart]
        · intro qQ _ hne; rw [if_neg hne, zero_mul]
        · intro h_abs; exact False.elim (h_abs (Finset.mem_univ _))
      have h2 : (∑ qQ : BDLCQ1 pcode M, (if qQ = (armEnd pcode M eZ k, bZ) then (1 : ZMod 2) else 0) *
          liftCylinderLX pcode M L (Sum.inr qQ)) = L eZ.val.1 := by
        rw [Finset.sum_eq_single (armEnd pcode M eZ k, bZ)]
        · dsimp [liftCylinderLX]; rw [if_pos rfl, one_mul, xq0OwnerQ_armEnd]
        · intro qQ _ hne; rw [if_neg hne, zero_mul]
        · intro h_abs; exact False.elim (h_abs (Finset.mem_univ _))
      rw [h1, h2, zmod2_add_self]
    · have h_exp : ∀ qQ : BDLCQ1 pcode M,
          bdlDeltaQ1 pcode M (Sum.inr (eZ, v)) qQ * liftCylinderLX pcode M L (Sum.inr qQ) =
          (if qQ = (Sum.inr (Sum.inr eZ), 0) then 1 else 0) * liftCylinderLX pcode M L (Sum.inr qQ) +
          (if qQ = (Sum.inr (Sum.inr eZ), v.succ) then 1 else 0) * liftCylinderLX pcode M L (Sum.inr qQ) := by
        intro qQ; dsimp [bdlDeltaQ1]; ring
      simp_rw [h_exp, Finset.sum_add_distrib]
      have h1 : (∑ qQ : BDLCQ1 pcode M, (if qQ = (Sum.inr (Sum.inr eZ), 0) then (1 : ZMod 2) else 0) *
          liftCylinderLX pcode M L (Sum.inr qQ)) = L eZ.val.1 := by
        rw [Finset.sum_eq_single (Sum.inr (Sum.inr eZ), 0)]
        · dsimp [liftCylinderLX, xq0OwnerQ]; rw [if_pos rfl, one_mul]
        · intro qQ _ hne; rw [if_neg hne, zero_mul]
        · intro h_abs; exact False.elim (h_abs (Finset.mem_univ _))
      have h2 : (∑ qQ : BDLCQ1 pcode M, (if qQ = (Sum.inr (Sum.inr eZ), v.succ) then (1 : ZMod 2) else 0) *
          liftCylinderLX pcode M L (Sum.inr qQ)) = L eZ.val.1 := by
        rw [Finset.sum_eq_single (Sum.inr (Sum.inr eZ), v.succ)]
        · dsimp [liftCylinderLX, xq0OwnerQ]; rw [if_pos rfl, one_mul]
        · intro qQ _ hne; rw [if_neg hne, zero_mul]
        · intro h_abs; exact False.elim (h_abs (Finset.mem_univ _))
      rw [h1, h2, zmod2_add_self]
  · dsimp [bdlStepXCheckZ]; rw [Fintype.sum_prod_type, Finset.sum_comm, Finset.sum_eq_single mZZ.2]
    · rw [Fintype.sum_sum_type, Fintype.sum_sum_type]
      have h_inl : (∑ q : Q, bdlGQZ1 pcode M mZZ (Sum.inl q, mZZ.2) * liftCylinderLX pcode M L (Sum.inr (Sum.inl q, mZZ.2))) = 0 :=
        Finset.sum_eq_zero (fun _ _ => by dsimp [bdlGQZ1]; simp)
      have h_mid : (∑ p : ActiveZ pcode × Fin M, bdlGQZ1 pcode M mZZ (Sum.inr (Sum.inl p), mZZ.2) *
          liftCylinderLX pcode M L (Sum.inr (Sum.inr (Sum.inl p), mZZ.2))) = 0 :=
        Finset.sum_eq_zero (fun _ _ => by dsimp [bdlGQZ1]; simp)
      rw [h_inl, zero_add, h_mid, zero_add]
      have h_term : ∀ eZ : ActiveZ pcode,
          bdlGQZ1 pcode M mZZ (Sum.inr (Sum.inr eZ), mZZ.2) * liftCylinderLX pcode M L (Sum.inr (Sum.inr (Sum.inr eZ), mZZ.2)) =
          if eZ.val.2 = mZZ.1 then L eZ.val.1 else 0 := by
        intro eZ; dsimp [bdlGQZ1, liftCylinderLX, xq0OwnerQ]; by_cases heZ : eZ.val.2 = mZZ.1 <;> simp [heZ]
      simp_rw [h_term]; rw [sum_activeZ_eq pcode mZZ.1 L]
      have h_dual := congr_fun h_syn mZZ.1
      simp only [syndrome, f2Syndrome, dualCode, dualF2ChainComplex, AddMonoidHom.coe_mk, ZeroHom.coe_mk, Pi.zero_apply] at h_dual
      simpa only [mul_comm] using h_dual
    · intro b _ hne; apply Finset.sum_eq_zero; intro v0 _; rcases v0 with _ | ⟨_ | eZ⟩ <;> dsimp [bdlGQZ1] <;> simp [hne]
    · intro h_abs; exact False.elim (h_abs (Finset.mem_univ _))

lemma cylinder_dualPairing_lift {Q M_Z M_X : Type}
    [Fintype Q] [DecidableEq Q] [Fintype M_Z] [DecidableEq M_Z] [Fintype M_X] [DecidableEq M_X]
    (pcode : CSSCode3D Q M_Z M_X) (M : ℕ) (L1 L2 : Q → ZMod 2) :
    dualPairing (liftCylinderLZ pcode M L1) (liftCylinderLX pcode M L2) = dualPairing L1 L2 := by
  dsimp [dualPairing]; rw [Fintype.sum_sum_type]
  have h_qX : (∑ qX : BDLCX1 pcode M, liftCylinderLZ pcode M L1 (Sum.inl qX) * liftCylinderLX pcode M L2 (Sum.inl qX)) = 0 :=
    Finset.sum_eq_zero (fun _ _ => by dsimp [liftCylinderLX]; simp)
  rw [h_qX, zero_add, Fintype.sum_prod_type, Finset.sum_comm, Finset.sum_eq_single (0 : Fin 3)]
  · rw [Fintype.sum_sum_type]
    have h_inr : (∑ v23 : (ActiveZ pcode × Fin M) ⊕ ActiveZ pcode,
        liftCylinderLZ pcode M L1 (Sum.inr (Sum.inr v23, 0)) * liftCylinderLX pcode M L2 (Sum.inr (Sum.inr v23, 0))) = 0 :=
      Finset.sum_eq_zero (fun _ _ => by dsimp [liftCylinderLZ, xq0LZ]; simp)
    rw [h_inr, add_zero]; rfl
  · intro b _ hne; apply Finset.sum_eq_zero; intro v0 _; dsimp [liftCylinderLZ]; rw [if_neg hne, zero_mul]
  · intro h_abs; exact False.elim (h_abs (Finset.mem_univ 0))

/-! ## 4. Transport Across `bdlCylinderStepX`, `bdlStepX`, `bdlStepZ`, and `bdlWeldedCode` -/

theorem hasDualLogicalPair_cylinderStepX {Q M_Z M_X : Type}
    [Fintype Q] [DecidableEq Q] [Fintype M_Z] [DecidableEq M_Z] [Fintype M_X] [DecidableEq M_X]
    (pcode : CSSCode3D Q M_Z M_X) (M : ℕ) (h : HasDualLogicalPair pcode) :
    HasDualLogicalPair (bdlCylinderStepX pcode M) := by
  rcases h with ⟨p⟩
  refine ⟨{
    L_Z := liftCylinderLX pcode M p.L_Z
    L_X := liftCylinderLZ pcode M p.L_X
    h_syn_Z := cylinder_syndrome_dual_lift pcode M p.L_Z p.h_syn_Z
    h_syn_X := cylinder_syndrome_primal_lift pcode M p.L_X p.h_syn_X
    h_pair := ?_
  }⟩
  change dualPairing (liftCylinderLX pcode M p.L_Z) (liftCylinderLZ pcode M p.L_X) = 1
  rw [dualPairing_comm, cylinder_dualPairing_lift, dualPairing_comm]
  exact p.h_pair

theorem hasDualLogicalPair_perturbStep {Q M_Z M_X : Type}
    [Fintype Q] [DecidableEq Q] [Fintype M_Z] [DecidableEq M_Z] [Fintype M_X] [DecidableEq M_X]
    (code : CSSCode3D Q M_Z M_X) (lam : ℕ)
    (cQ : Q → Point3D) (cZ : M_Z → Point3D) (cX : M_X → Point3D)
    (h : HasDualLogicalPair code) :
    HasDualLogicalPair (bdlPerturbStep code lam cQ cZ cX) := by
  rcases h with ⟨p⟩
  exact ⟨⟨p.L_Z, p.L_X, p.h_syn_Z, p.h_syn_X, p.h_pair⟩⟩

theorem hasDualLogicalPair_bdlStepX (B : BundledCSSCode3D) (h : HasDualLogicalPair B.code) :
    HasDualLogicalPair (bdlStepX B).code :=
  hasDualLogicalPair_cylinderStepX _ bdlSubdivPred
    (hasDualLogicalPair_perturbStep B.code bdlLambda
      (bdlLLLPerturbation B).1 (bdlLLLPerturbation B).2.1 (bdlLLLPerturbation B).2.2 h)

theorem hasDualLogicalPair_bdlStepZX (B : BundledCSSCode3D) (h : HasDualLogicalPair B.code) :
    HasDualLogicalPair ((bdlStepZ ∘ bdlStepX) B).code :=
  hasDualLogicalPair_dual
    (hasDualLogicalPair_bdlStepX (dualBundled (bdlStepX B))
      (hasDualLogicalPair_dual (hasDualLogicalPair_bdlStepX B h)))

theorem hasDualLogicalPair_iterated : ∀ (n : ℕ) (B : BundledCSSCode3D),
    HasDualLogicalPair B.code → HasDualLogicalPair ((bdlStepZ ∘ bdlStepX)^[n] B).code
  | 0, _, h => h
  | n + 1, B, h => hasDualLogicalPair_iterated n ((bdlStepZ ∘ bdlStepX) B)
      (hasDualLogicalPair_bdlStepZX B h)

/-- Canonical `X`-syndrome-zero logical representative on `bdlSurfaceSeedCode` (`q ∈ {0, 1}`). -/
def surfaceLZ : Fin 5 → ZMod 2
  | ⟨0, _⟩ => 1 | ⟨1, _⟩ => 1 | ⟨2, _⟩ => 0 | ⟨3, _⟩ => 0 | ⟨4, _⟩ => 0

/-- Canonical `Z`-syndrome-zero logical representative on `bdlSurfaceSeedCode` (`q ∈ {0, 3}`). -/
def surfaceLX : Fin 5 → ZMod 2
  | ⟨0, _⟩ => 1 | ⟨1, _⟩ => 0 | ⟨2, _⟩ => 0 | ⟨3, _⟩ => 1 | ⟨4, _⟩ => 0

lemma surfaceLZ_syndrome : syndrome bdlSurfaceSeedCode surfaceLZ = 0 := by
  ext m; fin_cases m <;> decide

lemma surfaceLX_syndrome : syndrome (dualCode bdlSurfaceSeedCode) surfaceLX = 0 := by
  ext m; fin_cases m <;> decide

lemma surface_dualPairing : (∑ q : Fin 5, surfaceLX q * surfaceLZ q) = 1 := by
  decide

theorem bdlSurfaceSeedCode_hasDualLogicalPair_aux : HasDualLogicalPair bdlSurfaceSeedCode :=
  ⟨⟨surfaceLX, surfaceLZ, surfaceLX_syndrome, surfaceLZ_syndrome, surface_dualPairing⟩⟩

/-- The `[[5, 1, 2]]` planar surface code seed `bdlSurfaceSeedCode` encodes a nontrivial dual logical
    pair `HasDualLogicalPair bdlSurfaceSeedCode` (`HasLogicalQubit bdlSurfaceSeedCode`). -/
theorem bdlSurfaceSeedCode_hasDualLogicalPair :
    HasDualLogicalPair bdlSurfaceSeedCode ∧ HasLogicalQubit bdlSurfaceSeedCode :=
  ⟨bdlSurfaceSeedCode_hasDualLogicalPair_aux,
   hasLogicalQubit_of_hasDualLogicalPair bdlSurfaceSeedCode_hasDualLogicalPair_aux⟩

/-- At every hierarchy level $k \in \mathbb{N}$, the 3-layer welded BDL code `bdlWeldedCode k`
    preserves a nontrivial dual logical pair `HasDualLogicalPair (bdlWeldedCode k)` and
    `HasLogicalQubit (bdlWeldedCode k)` (Part I, Section 3.2 (`subsec:nilpotent-hpl`), Proposition 3.7 (`prop:classical-hpl`)). -/
theorem bdlWeldedCode_hasDualLogicalPair (k : ℕ) :
    HasDualLogicalPair (bdlWeldedCode k) ∧ HasLogicalQubit (bdlWeldedCode k) := by
  have h : HasDualLogicalPair (bdlWeldedCode k) :=
    hasDualLogicalPair_iterated (k + 1) bdlSurfaceSeedBundled bdlSurfaceSeedCode_hasDualLogicalPair_aux
  exact ⟨h, hasLogicalQubit_of_hasDualLogicalPair h⟩
