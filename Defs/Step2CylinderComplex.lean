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

import Defs.Step1PeriodicLLL

/-!
# Step 2 Three-Layer Mapping Cone Cells, Star Interfaces, and Concentric Radial Shells

Defines active check-incidence edges (`ActiveZ`, `ActiveX`), subdivided 1D star cells (`Xq0`), check-link boundary cells (`BoundaryX0`, `projXq0ToBoundaryX0`), and concentric shell membership predicates (`InLinkOfX`, `InShellR`, `IsDiagZeroVertex`). Establishes the cellular carrier types (`BDLStepXMX`, `BDLStepXQ`, `BDLStepXMZ`) and 3D coordinates (`bdlStepXPosX`, `bdlStepXPosQ`, `bdlStepXPosZ`) for the three-layer cylinder $Y_x^{(3)}$, star interface $Y_q^{(3)}$, and total welded mapping cone.

## References

* Part I, Section 2.3 (`subsec:step2-mapping-cone`), Definition 2.5 (`def:three-layer-mapping-cone`)
* Part I, Section 3.2 (`subsec:nilpotent-hpl`), Lemma 3.6 (`lem:block-sdr`), Section 3.3 (`subsec:scale-matched-rca`), Lemma 3.8 (`lem:clean-shell-subcylinder`)
* Balasubramanian, Davydova, and Lin (2026)
-/

noncomputable section

open scoped Classical BigOperators

/-! ## 1. Subdivided 1D Star Complex $X'_q$ and Boundary Link $\partial X'_x$ -/

/-- Active $Z$-check edges `ActiveZ code`: pairs `(q, mZ)` with `checkZ mZ q ≠ 0`. -/
abbrev ActiveZ {Q M_Z M_X : Type}
    [Fintype Q] [DecidableEq Q] [Fintype M_Z] [DecidableEq M_Z] [Fintype M_X] [DecidableEq M_X]
    (code : CSSCode3D Q M_Z M_X) : Type :=
  {p : Q × M_Z // code.checkZ p.2 p.1 ≠ 0}

/-- Active $X$-check edges `ActiveX code`: pairs `(q, mX)` with `checkX mX q ≠ 0`. -/
abbrev ActiveX {Q M_Z M_X : Type}
    [Fintype Q] [DecidableEq Q] [Fintype M_Z] [DecidableEq M_Z] [Fintype M_X] [DecidableEq M_X]
    (code : CSSCode3D Q M_Z M_X) : Type :=
  {p : Q × M_X // code.checkX p.2 p.1 ≠ 0}

/-- Predecessor index `finPred j` in `Fin (M + 1)`. -/
def finPred {M : ℕ} (j : Fin (M + 1)) : Fin (M + 1) :=
  ⟨j.val - 1, Nat.lt_of_le_of_lt (Nat.pred_le _) j.isLt⟩

/-- 0-cells `Xq0 pcode M` of the $(M + 1)$-subdivided 1D star complex $\bigsqcup_{q \in Q} X'_q(0)$. -/
abbrev Xq0 {Q M_Z M_X : Type}
    [Fintype Q] [DecidableEq Q] [Fintype M_Z] [DecidableEq M_Z] [Fintype M_X] [DecidableEq M_X]
    (pcode : CSSCode3D Q M_Z M_X) (M : ℕ) : Type :=
  Q ⊕ (ActiveZ pcode × Fin M) ⊕ ActiveZ pcode

/-- 0-cells `BoundaryX0 pcode M` of the link complex $\partial X'_x(0)$. -/
abbrev BoundaryX0 {Q M_Z M_X : Type}
    [Fintype Q] [DecidableEq Q] [Fintype M_Z] [DecidableEq M_Z] [Fintype M_X] [DecidableEq M_X]
    (pcode : CSSCode3D Q M_Z M_X) (M : ℕ) : Type :=
  Q ⊕ (ActiveZ pcode × Fin M) ⊕ M_Z

/-- Canonical cellular map `projXq0ToBoundaryX0 : Xq0 pcode M → BoundaryX0 pcode M`. -/
def projXq0ToBoundaryX0 {Q M_Z M_X : Type}
    [Fintype Q] [DecidableEq Q] [Fintype M_Z] [DecidableEq M_Z] [Fintype M_X] [DecidableEq M_X]
    (pcode : CSSCode3D Q M_Z M_X) (M : ℕ) :
    Xq0 pcode M → BoundaryX0 pcode M
  | Sum.inl q => Sum.inl q
  | Sum.inr (Sum.inl p) => Sum.inr (Sum.inl p)
  | Sum.inr (Sum.inr eZ) => Sum.inr (Sum.inr eZ.val.2)

/-- The coarse qubit `xq0OwnerQ v ∈ Q` whose local complex $C_q$ owns `v ∈ Xq0 pcode M`. -/
def xq0OwnerQ {Q M_Z M_X : Type}
    [Fintype Q] [DecidableEq Q] [Fintype M_Z] [DecidableEq M_Z] [Fintype M_X] [DecidableEq M_X]
    (pcode : CSSCode3D Q M_Z M_X) (M : ℕ) :
    Xq0 pcode M → Q
  | Sum.inl q => q
  | Sum.inr (Sum.inl (eZ, _)) => eZ.val.1
  | Sum.inr (Sum.inr eZ) => eZ.val.1

/-- Start 0-cell `armStart eZ k ∈ Xq0 pcode M` of the `k`-th subdivided segment along `eZ = (q, z)`. -/
def armStart {Q M_Z M_X : Type}
    [Fintype Q] [DecidableEq Q] [Fintype M_Z] [DecidableEq M_Z] [Fintype M_X] [DecidableEq M_X]
    (pcode : CSSCode3D Q M_Z M_X) (M : ℕ)
    (eZ : ActiveZ pcode) (k : Fin (M + 1)) : Xq0 pcode M :=
  if h : k.val = 0 then
    Sum.inl eZ.val.1
  else
    Sum.inr (Sum.inl (eZ, ⟨k.val - 1, Nat.sub_lt_right_of_lt_add (Nat.pos_of_ne_zero h) k.isLt⟩))

/-- End 0-cell `armEnd eZ k ∈ Xq0 pcode M` of the `k`-th subdivided segment along `eZ = (q, z)`. -/
def armEnd {Q M_Z M_X : Type}
    [Fintype Q] [DecidableEq Q] [Fintype M_Z] [DecidableEq M_Z] [Fintype M_X] [DecidableEq M_X]
    (pcode : CSSCode3D Q M_Z M_X) (M : ℕ)
    (eZ : ActiveZ pcode) (k : Fin (M + 1)) : Xq0 pcode M :=
  if h : k.val < M then
    Sum.inr (Sum.inl (eZ, ⟨k.val, h⟩))
  else
    Sum.inr (Sum.inr eZ)

/-- Start 0-cell `bxStart eZ k ∈ BoundaryX0 pcode M` of `(eZ, k)` in $\partial X'_x(0)$. -/
def bxStart {Q M_Z M_X : Type}
    [Fintype Q] [DecidableEq Q] [Fintype M_Z] [DecidableEq M_Z] [Fintype M_X] [DecidableEq M_X]
    (pcode : CSSCode3D Q M_Z M_X) (M : ℕ)
    (eZ : ActiveZ pcode) (k : Fin (M + 1)) : BoundaryX0 pcode M :=
  projXq0ToBoundaryX0 pcode M (armStart pcode M eZ k)

/-- End 0-cell `bxEnd eZ k ∈ BoundaryX0 pcode M` of `(eZ, k)` in $\partial X'_x(0)$. -/
def bxEnd {Q M_Z M_X : Type}
    [Fintype Q] [DecidableEq Q] [Fintype M_Z] [DecidableEq M_Z] [Fintype M_X] [DecidableEq M_X]
    (pcode : CSSCode3D Q M_Z M_X) (M : ℕ)
    (eZ : ActiveZ pcode) (k : Fin (M + 1)) : BoundaryX0 pcode M :=
  projXq0ToBoundaryX0 pcode M (armEnd pcode M eZ k)

lemma xq0OwnerQ_armStart {Q M_Z M_X : Type}
    [Fintype Q] [DecidableEq Q] [Fintype M_Z] [DecidableEq M_Z] [Fintype M_X] [DecidableEq M_X]
    (pcode : CSSCode3D Q M_Z M_X) (M : ℕ) (eZ : ActiveZ pcode) (k : Fin (M + 1)) :
    xq0OwnerQ pcode M (armStart pcode M eZ k) = eZ.val.1 := by
  dsimp [armStart]; split_ifs <;> rfl

lemma xq0OwnerQ_armEnd {Q M_Z M_X : Type}
    [Fintype Q] [DecidableEq Q] [Fintype M_Z] [DecidableEq M_Z] [Fintype M_X] [DecidableEq M_X]
    (pcode : CSSCode3D Q M_Z M_X) (M : ℕ) (eZ : ActiveZ pcode) (k : Fin (M + 1)) :
    xq0OwnerQ pcode M (armEnd pcode M eZ k) = eZ.val.1 := by
  dsimp [armEnd]; split_ifs <;> rfl

/-- 3D coordinates `boundaryX0Pos` of 0-cells in `BoundaryX0 pcode M`. -/
def boundaryX0Pos {Q M_Z M_X : Type}
    [Fintype Q] [DecidableEq Q] [Fintype M_Z] [DecidableEq M_Z] [Fintype M_X] [DecidableEq M_X]
    (pcode : CSSCode3D Q M_Z M_X) (M : ℕ) :
    BoundaryX0 pcode M → Point3D
  | Sum.inl q => pcode.posQ q
  | Sum.inr (Sum.inl (eZ, j)) =>
      subdividePoint3D (pcode.posQ eZ.val.1) (pcode.posZ eZ.val.2) (M + 1) (j.val + 1)
  | Sum.inr (Sum.inr z) => pcode.posZ z

/-- 3D coordinates `xq0Pos` of 0-cells in `Xq0 pcode M`. -/
def xq0Pos {Q M_Z M_X : Type}
    [Fintype Q] [DecidableEq Q] [Fintype M_Z] [DecidableEq M_Z] [Fintype M_X] [DecidableEq M_X]
    (pcode : CSSCode3D Q M_Z M_X) (M : ℕ) (v : Xq0 pcode M) : Point3D :=
  boundaryX0Pos pcode M (projXq0ToBoundaryX0 pcode M v)

/-! ## 2. Link Subtypes and $(M + 1) \times (M + 1)$ Radial Shell Grid Subtypes -/

/-- Predicate `inLinkOfX pcode M x v` specifying whether `v ∈ BoundaryX0 pcode M` lies in $\partial X'_x(0)$. -/
def InLinkOfX {Q M_Z M_X : Type}
    [Fintype Q] [DecidableEq Q] [Fintype M_Z] [DecidableEq M_Z] [Fintype M_X] [DecidableEq M_X]
    (pcode : CSSCode3D Q M_Z M_X) (M : ℕ) (x : M_X) : BoundaryX0 pcode M → Prop
  | Sum.inl q => pcode.checkX x q ≠ 0
  | Sum.inr (Sum.inl (eZ, _)) => pcode.checkX x eZ.val.1 ≠ 0
  | Sum.inr (Sum.inr z) => ∃ q : Q, pcode.checkX x q ≠ 0 ∧ pcode.checkZ z q ≠ 0

instance instDecidableInLinkOfX {Q M_Z M_X : Type}
    [Fintype Q] [DecidableEq Q] [Fintype M_Z] [DecidableEq M_Z] [Fintype M_X] [DecidableEq M_X]
    (pcode : CSSCode3D Q M_Z M_X) (M : ℕ) (x : M_X) (v : BoundaryX0 pcode M) :
    Decidable (InLinkOfX pcode M x v) := by
  cases v with
  | inl q => dsimp [InLinkOfX]; infer_instance
  | inr v23 =>
    cases v23 with
    | inl ej => dsimp [InLinkOfX]; infer_instance
    | inr z => dsimp [InLinkOfX]; infer_instance

/-- Subtype `BoundaryX0Link pcode M` of pairs `(x, v)` where `v ∈ ∂X'_x(0)`. -/
abbrev BoundaryX0Link {Q M_Z M_X : Type}
    [Fintype Q] [DecidableEq Q] [Fintype M_Z] [DecidableEq M_Z] [Fintype M_X] [DecidableEq M_X]
    (pcode : CSSCode3D Q M_Z M_X) (M : ℕ) : Type :=
  {p : M_X × BoundaryX0 pcode M // InLinkOfX pcode M p.1 p.2}

/-- Subtype `ActiveZLink pcode` of pairs `(x, eZ)` where `eZ = (q, z) ∈ ∂X_x(1)` (`checkX x q ≠ 0`). -/
abbrev ActiveZLink {Q M_Z M_X : Type}
    [Fintype Q] [DecidableEq Q] [Fintype M_Z] [DecidableEq M_Z] [Fintype M_X] [DecidableEq M_X]
    (pcode : CSSCode3D Q M_Z M_X) : Type :=
  {p : M_X × ActiveZ pcode // pcode.checkX p.1 p.2.val.1 ≠ 0}

lemma inLinkOfX_bxStart {Q M_Z M_X : Type}
    [Fintype Q] [DecidableEq Q] [Fintype M_Z] [DecidableEq M_Z] [Fintype M_X] [DecidableEq M_X]
    (pcode : CSSCode3D Q M_Z M_X) (M : ℕ) (s : ActiveZLink pcode) (k : Fin (M + 1)) :
    InLinkOfX pcode M s.val.1 (bxStart pcode M s.val.2 k) := by
  dsimp [bxStart, armStart]; split_ifs <;> exact s.property

lemma inLinkOfX_bxEnd {Q M_Z M_X : Type}
    [Fintype Q] [DecidableEq Q] [Fintype M_Z] [DecidableEq M_Z] [Fintype M_X] [DecidableEq M_X]
    (pcode : CSSCode3D Q M_Z M_X) (M : ℕ) (s : ActiveZLink pcode) (k : Fin (M + 1)) :
    InLinkOfX pcode M s.val.1 (bxEnd pcode M s.val.2 k) := by
  dsimp [bxEnd, armEnd]; split_ifs
  · exact s.property
  · exact ⟨s.val.2.val.1, s.property, s.val.2.property⟩

/-- Start boundary link 0-cell `bxStartLink s k ∈ BoundaryX0Link pcode M`. -/
def bxStartLink {Q M_Z M_X : Type}
    [Fintype Q] [DecidableEq Q] [Fintype M_Z] [DecidableEq M_Z] [Fintype M_X] [DecidableEq M_X]
    (pcode : CSSCode3D Q M_Z M_X) (M : ℕ) (s : ActiveZLink pcode) (k : Fin (M + 1)) :
    BoundaryX0Link pcode M :=
  ⟨(s.val.1, bxStart pcode M s.val.2 k), inLinkOfX_bxStart pcode M s k⟩

/-- End boundary link 0-cell `bxEndLink s k ∈ BoundaryX0Link pcode M`. -/
def bxEndLink {Q M_Z M_X : Type}
    [Fintype Q] [DecidableEq Q] [Fintype M_Z] [DecidableEq M_Z] [Fintype M_X] [DecidableEq M_X]
    (pcode : CSSCode3D Q M_Z M_X) (M : ℕ) (s : ActiveZLink pcode) (k : Fin (M + 1)) :
    BoundaryX0Link pcode M :=
  ⟨(s.val.1, bxEnd pcode M s.val.2 k), inLinkOfX_bxEnd pcode M s k⟩

/-- Predicate `inShellR pcode M xv r` specifying whether `xv : BoundaryX0Link pcode M` is present in shell `r`. -/
def InShellR {Q M_Z M_X : Type}
    [Fintype Q] [DecidableEq Q] [Fintype M_Z] [DecidableEq M_Z] [Fintype M_X] [DecidableEq M_X]
    (pcode : CSSCode3D Q M_Z M_X) (M : ℕ)
    (xv : BoundaryX0Link pcode M) (r : Fin (M + 1)) : Prop :=
  match xv.val.2 with
  | Sum.inl _ => True
  | Sum.inr (Sum.inl (_, j)) => j.val < r.val
  | Sum.inr (Sum.inr _) => True

instance instDecidableInShellR {Q M_Z M_X : Type}
    [Fintype Q] [DecidableEq Q] [Fintype M_Z] [DecidableEq M_Z] [Fintype M_X] [DecidableEq M_X]
    (pcode : CSSCode3D Q M_Z M_X) (M : ℕ)
    (xv : BoundaryX0Link pcode M) (r : Fin (M + 1)) :
    Decidable (InShellR pcode M xv r) := by
  cases h : xv.val.2 with
  | inl _ => dsimp [InShellR]; rw [h]; infer_instance
  | inr v23 =>
    cases v23 with
    | inl ej => dsimp [InShellR]; rw [h]; infer_instance
    | inr _ => dsimp [InShellR]; rw [h]; infer_instance

/-- Grid 0-cells `ShellVertex pcode M` in shells `r : Fin (M + 1)` of $X'_x(0)$. -/
abbrev ShellVertex {Q M_Z M_X : Type}
    [Fintype Q] [DecidableEq Q] [Fintype M_Z] [DecidableEq M_Z] [Fintype M_X] [DecidableEq M_X]
    (pcode : CSSCode3D Q M_Z M_X) (M : ℕ) : Type :=
  {p : BoundaryX0Link pcode M × Fin (M + 1) // InShellR pcode M p.1 p.2}

/-- Grid azimuthal segments `ShellSegment pcode M` (`(s, r, k)` with `k.val ≤ r.val`) in $X'_x$. -/
abbrev ShellSegment {Q M_Z M_X : Type}
    [Fintype Q] [DecidableEq Q] [Fintype M_Z] [DecidableEq M_Z] [Fintype M_X] [DecidableEq M_X]
    (pcode : CSSCode3D Q M_Z M_X) (M : ℕ) : Type :=
  {p : ActiveZLink pcode × Fin (M + 1) × Fin (M + 1) // p.2.2.val ≤ p.2.1.val}

lemma inShellR_last {Q M_Z M_X : Type}
    [Fintype Q] [DecidableEq Q] [Fintype M_Z] [DecidableEq M_Z] [Fintype M_X] [DecidableEq M_X]
    (pcode : CSSCode3D Q M_Z M_X) (M : ℕ) (xv : BoundaryX0Link pcode M) :
    InShellR pcode M xv (Fin.last M) := by
  rcases xv with ⟨⟨x, v⟩, hp⟩
  rcases v with _ | ⟨⟨_, j⟩ | _⟩
  · trivial
  · exact j.isLt
  · trivial

/-- Outer boundary vertex `mkOuterShellVertex pcode M xv` at `r = Fin.last M`. -/
def mkOuterShellVertex {Q M_Z M_X : Type}
    [Fintype Q] [DecidableEq Q] [Fintype M_Z] [DecidableEq M_Z] [Fintype M_X] [DecidableEq M_X]
    (pcode : CSSCode3D Q M_Z M_X) (M : ℕ) (xv : BoundaryX0Link pcode M) :
    ShellVertex pcode M :=
  ⟨(xv, Fin.last M), inShellR_last pcode M xv⟩

/-- Outer boundary segment `mkOuterShellSegment pcode M s k` at `r = Fin.last M`. -/
def mkOuterShellSegment {Q M_Z M_X : Type}
    [Fintype Q] [DecidableEq Q] [Fintype M_Z] [DecidableEq M_Z] [Fintype M_X] [DecidableEq M_X]
    (pcode : CSSCode3D Q M_Z M_X) (M : ℕ) (s : ActiveZLink pcode) (k : Fin (M + 1)) :
    ShellSegment pcode M :=
  ⟨(s, Fin.last M, k), Nat.le_of_lt_succ k.isLt⟩

/-- Radial parent boundary index in `BoundaryX0 pcode M` at shell `finPred r`. -/
def radialParentV {Q M_Z M_X : Type}
    [Fintype Q] [DecidableEq Q] [Fintype M_Z] [DecidableEq M_Z] [Fintype M_X] [DecidableEq M_X]
    (pcode : CSSCode3D Q M_Z M_X) (M : ℕ)
    (v : BoundaryX0 pcode M) (r : Fin (M + 1)) : BoundaryX0 pcode M :=
  match v with
  | Sum.inl q => Sum.inl q
  | Sum.inr (Sum.inl (eZ, j)) =>
      if j.val < (finPred r).val then Sum.inr (Sum.inl (eZ, j)) else Sum.inr (Sum.inr eZ.val.2)
  | Sum.inr (Sum.inr z) => Sum.inr (Sum.inr z)

lemma inLinkOfX_radialParentV {Q M_Z M_X : Type}
    [Fintype Q] [DecidableEq Q] [Fintype M_Z] [DecidableEq M_Z] [Fintype M_X] [DecidableEq M_X]
    (pcode : CSSCode3D Q M_Z M_X) (M : ℕ)
    (xv : BoundaryX0Link pcode M) (r : Fin (M + 1)) :
    InLinkOfX pcode M xv.val.1 (radialParentV pcode M xv.val.2 r) := by
  rcases xv with ⟨⟨x, v⟩, hp⟩
  rcases v with q | ⟨⟨eZ, j⟩ | z⟩
  · exact hp
  · dsimp [radialParentV]; split_ifs with hj
    · exact hp
    · exact ⟨eZ.val.1, hp, eZ.property⟩
  · exact hp

/-- Radial parent link vertex at shell `finPred r`. -/
def radialParentLink {Q M_Z M_X : Type}
    [Fintype Q] [DecidableEq Q] [Fintype M_Z] [DecidableEq M_Z] [Fintype M_X] [DecidableEq M_X]
    (pcode : CSSCode3D Q M_Z M_X) (M : ℕ)
    (xv : BoundaryX0Link pcode M) (r : Fin (M + 1)) : BoundaryX0Link pcode M :=
  ⟨(xv.val.1, radialParentV pcode M xv.val.2 r), inLinkOfX_radialParentV pcode M xv r⟩

lemma inShellR_radialParentLink {Q M_Z M_X : Type}
    [Fintype Q] [DecidableEq Q] [Fintype M_Z] [DecidableEq M_Z] [Fintype M_X] [DecidableEq M_X]
    (pcode : CSSCode3D Q M_Z M_X) (M : ℕ)
    (xv : BoundaryX0Link pcode M) (r : Fin (M + 1)) :
    InShellR pcode M (radialParentLink pcode M xv r) (finPred r) := by
  rcases xv with ⟨⟨x, v⟩, hp⟩
  rcases v with _ | ⟨⟨eZ, j⟩ | _⟩
  · trivial
  · dsimp [radialParentLink, radialParentV]; split_ifs with hj
    · exact hj
    · trivial
  · trivial

/-- Radial parent `ShellVertex` at shell `finPred sv.val.2`. -/
def radialParentVertex {Q M_Z M_X : Type}
    [Fintype Q] [DecidableEq Q] [Fintype M_Z] [DecidableEq M_Z] [Fintype M_X] [DecidableEq M_X]
    (pcode : CSSCode3D Q M_Z M_X) (M : ℕ)
    (sv : ShellVertex pcode M) : ShellVertex pcode M :=
  ⟨(radialParentLink pcode M sv.val.1 sv.val.2, finPred sv.val.2),
    inShellR_radialParentLink pcode M sv.val.1 sv.val.2⟩

lemma inShellR_bxStartLink {Q M_Z M_X : Type}
    [Fintype Q] [DecidableEq Q] [Fintype M_Z] [DecidableEq M_Z] [Fintype M_X] [DecidableEq M_X]
    (pcode : CSSCode3D Q M_Z M_X) (M : ℕ) (seg : ShellSegment pcode M) :
    InShellR pcode M (bxStartLink pcode M seg.val.1 seg.val.2.2) seg.val.2.1 := by
  have h_le : seg.val.2.2.val ≤ seg.val.2.1.val := seg.property
  dsimp [bxStartLink, bxStart, armStart, projXq0ToBoundaryX0]
  split_ifs with hk0
  · trivial
  · dsimp [InShellR]; omega

/-- Left endpoint `shellSegStartVertex pcode M seg ∈ ShellVertex pcode M` of azimuthal segment `seg`. -/
def shellSegStartVertex {Q M_Z M_X : Type}
    [Fintype Q] [DecidableEq Q] [Fintype M_Z] [DecidableEq M_Z] [Fintype M_X] [DecidableEq M_X]
    (pcode : CSSCode3D Q M_Z M_X) (M : ℕ) (seg : ShellSegment pcode M) :
    ShellVertex pcode M :=
  ⟨(bxStartLink pcode M seg.val.1 seg.val.2.2, seg.val.2.1), inShellR_bxStartLink pcode M seg⟩

/-- Right endpoint boundary index `shellSegEndV pcode M seg ∈ BoundaryX0 pcode M` of azimuthal segment `seg`. -/
def shellSegEndV {Q M_Z M_X : Type}
    [Fintype Q] [DecidableEq Q] [Fintype M_Z] [DecidableEq M_Z] [Fintype M_X] [DecidableEq M_X]
    (pcode : CSSCode3D Q M_Z M_X) (M : ℕ) (seg : ShellSegment pcode M) :
    BoundaryX0 pcode M :=
  if hk : seg.val.2.2.val < seg.val.2.1.val then
    Sum.inr (Sum.inl (seg.val.1.val.2,
      ⟨seg.val.2.2.val, Nat.lt_of_lt_of_le hk (Nat.le_of_lt_succ seg.val.2.1.isLt)⟩))
  else
    Sum.inr (Sum.inr seg.val.1.val.2.val.2)

lemma inLinkOfX_shellSegEndV {Q M_Z M_X : Type}
    [Fintype Q] [DecidableEq Q] [Fintype M_Z] [DecidableEq M_Z] [Fintype M_X] [DecidableEq M_X]
    (pcode : CSSCode3D Q M_Z M_X) (M : ℕ) (seg : ShellSegment pcode M) :
    InLinkOfX pcode M seg.val.1.val.1 (shellSegEndV pcode M seg) := by
  dsimp [shellSegEndV]; split_ifs with hk
  · exact seg.val.1.property
  · exact ⟨seg.val.1.val.2.val.1, seg.val.1.property, seg.val.1.val.2.property⟩

/-- Right endpoint link vertex `shellSegEndLink pcode M seg ∈ BoundaryX0Link pcode M`. -/
def shellSegEndLink {Q M_Z M_X : Type}
    [Fintype Q] [DecidableEq Q] [Fintype M_Z] [DecidableEq M_Z] [Fintype M_X] [DecidableEq M_X]
    (pcode : CSSCode3D Q M_Z M_X) (M : ℕ) (seg : ShellSegment pcode M) :
    BoundaryX0Link pcode M :=
  ⟨(seg.val.1.val.1, shellSegEndV pcode M seg), inLinkOfX_shellSegEndV pcode M seg⟩

lemma inShellR_shellSegEndLink {Q M_Z M_X : Type}
    [Fintype Q] [DecidableEq Q] [Fintype M_Z] [DecidableEq M_Z] [Fintype M_X] [DecidableEq M_X]
    (pcode : CSSCode3D Q M_Z M_X) (M : ℕ) (seg : ShellSegment pcode M) :
    InShellR pcode M (shellSegEndLink pcode M seg) seg.val.2.1 := by
  dsimp [shellSegEndLink, shellSegEndV]; split_ifs with hk
  · exact hk
  · trivial

/-- Right endpoint `shellSegEndVertex pcode M seg ∈ ShellVertex pcode M` of azimuthal segment `seg`. -/
def shellSegEndVertex {Q M_Z M_X : Type}
    [Fintype Q] [DecidableEq Q] [Fintype M_Z] [DecidableEq M_Z] [Fintype M_X] [DecidableEq M_X]
    (pcode : CSSCode3D Q M_Z M_X) (M : ℕ) (seg : ShellSegment pcode M) :
    ShellVertex pcode M :=
  ⟨(shellSegEndLink pcode M seg, seg.val.2.1), inShellR_shellSegEndLink pcode M seg⟩

/-- Predecessor azimuthal segment at shell `finPred r` when `k.val ≠ r.val`. -/
def shellSegPred {Q M_Z M_X : Type}
    [Fintype Q] [DecidableEq Q] [Fintype M_Z] [DecidableEq M_Z] [Fintype M_X] [DecidableEq M_X]
    (pcode : CSSCode3D Q M_Z M_X) (M : ℕ) (seg : ShellSegment pcode M)
    (hne : seg.val.2.2.val ≠ seg.val.2.1.val) : ShellSegment pcode M :=
  ⟨(seg.val.1, finPred seg.val.2.1, seg.val.2.2), by
    have h_le : seg.val.2.2.val ≤ seg.val.2.1.val := seg.property
    dsimp [finPred]; omega⟩

/-! ## 3. 3-Layer Cochain Bases $C^0_{(i+1)}, C^1_{(i+1)}, C^2_{(i+1)}$ and 3D Positions -/

/-- 0-Cochain Basis $C^0_{(i+1)} = C_X^0$ (`BDLStepXMX pcode M`, $X$-Check Generators). -/
abbrev BDLStepXMX {Q M_Z M_X : Type}
    [Fintype Q] [DecidableEq Q] [Fintype M_Z] [DecidableEq M_Z] [Fintype M_X] [DecidableEq M_X]
    (pcode : CSSCode3D Q M_Z M_X) (M : ℕ) : Type :=
  (M_X × Fin 3) ⊕ (ShellVertex pcode M × Fin 3)

/-- Predicate identifying the `r = 0` auxiliary diagonal vertex `((x, Sum.inr (Sum.inr z)), 0)`. -/
def IsDiagZeroVertex {Q M_Z M_X : Type}
    [Fintype Q] [DecidableEq Q] [Fintype M_Z] [DecidableEq M_Z] [Fintype M_X] [DecidableEq M_X]
    (pcode : CSSCode3D Q M_Z M_X) (M : ℕ) (sv : ShellVertex pcode M) : Prop :=
  sv.val.2.val = 0 ∧ ∃ z : M_Z, sv.val.1.val.2 = Sum.inr (Sum.inr z)

instance instDecidableIsDiagZeroVertex {Q M_Z M_X : Type}
    [Fintype Q] [DecidableEq Q] [Fintype M_Z] [DecidableEq M_Z] [Fintype M_X] [DecidableEq M_X]
    (pcode : CSSCode3D Q M_Z M_X) (M : ℕ) (sv : ShellVertex pcode M) :
    Decidable (IsDiagZeroVertex pcode M sv) := by
  dsimp [IsDiagZeroVertex]; infer_instance

/-- Non-diagonal radial 1-cell endpoints `RadialVertex pcode M`. -/
abbrev RadialVertex {Q M_Z M_X : Type}
    [Fintype Q] [DecidableEq Q] [Fintype M_Z] [DecidableEq M_Z] [Fintype M_X] [DecidableEq M_X]
    (pcode : CSSCode3D Q M_Z M_X) (M : ℕ) : Type :=
  {sv : ShellVertex pcode M // ¬ IsDiagZeroVertex pcode M sv}

/-- 1-Cochain Basis $C_X^1$ of $Y_x$ (`BDLCX1 pcode M`, Qubits in $C_X^1$). -/
abbrev BDLCX1 {Q M_Z M_X : Type}
    [Fintype Q] [DecidableEq Q] [Fintype M_Z] [DecidableEq M_Z] [Fintype M_X] [DecidableEq M_X]
    (pcode : CSSCode3D Q M_Z M_X) (M : ℕ) : Type :=
  (RadialVertex pcode M × Fin 3) ⊕
  (ShellSegment pcode M × Fin 3) ⊕
  (BoundaryX0Link pcode M × Fin 2)

/-- 1-Cochain Basis $C_Q^1 = Y_q(0)$ (`BDLCQ1 pcode M`, Qubits in $C_Q^1$). -/
abbrev BDLCQ1 {Q M_Z M_X : Type}
    [Fintype Q] [DecidableEq Q] [Fintype M_Z] [DecidableEq M_Z] [Fintype M_X] [DecidableEq M_X]
    (pcode : CSSCode3D Q M_Z M_X) (M : ℕ) : Type :=
  Xq0 pcode M × Fin 3

/-- Total 1-Cochain Basis $C^1_{(i+1)} = C_X^1 \oplus C_Q^1$ (`BDLStepXQ pcode M`, Physical Qubits). -/
abbrev BDLStepXQ {Q M_Z M_X : Type}
    [Fintype Q] [DecidableEq Q] [Fintype M_Z] [DecidableEq M_Z] [Fintype M_X] [DecidableEq M_X]
    (pcode : CSSCode3D Q M_Z M_X) (M : ℕ) : Type :=
  BDLCX1 pcode M ⊕ BDLCQ1 pcode M

/-- 2-Cochain Basis $C_X^2$ of $Y_x$ (`BDLCX2 pcode M`, $Z$-Checks in $C_X^2$). -/
abbrev BDLCX2 {Q M_Z M_X : Type}
    [Fintype Q] [DecidableEq Q] [Fintype M_Z] [DecidableEq M_Z] [Fintype M_X] [DecidableEq M_X]
    (pcode : CSSCode3D Q M_Z M_X) (M : ℕ) : Type :=
  (ShellSegment pcode M × Fin 3) ⊕
  (ActiveZLink pcode × Fin (M + 1) × Fin 2)

/-- 2-Cochain Basis $C_Q^2 = Y_q(1)$ (`BDLCQ2 pcode M`, $Z$-Checks in $C_Q^2$). -/
abbrev BDLCQ2 {Q M_Z M_X : Type}
    [Fintype Q] [DecidableEq Q] [Fintype M_Z] [DecidableEq M_Z] [Fintype M_X] [DecidableEq M_X]
    (pcode : CSSCode3D Q M_Z M_X) (M : ℕ) : Type :=
  (ActiveZ pcode × Fin (M + 1) × Fin 3) ⊕ (ActiveZ pcode × Fin 2)

/-- 2-Cochain Basis $C_Z^2 = Y_z(0)$ (`BDLCZ2 M_Z`, $Z$-Checks in $C_Z^2$). -/
abbrev BDLCZ2 (M_Z : Type) : Type :=
  M_Z × Fin 3

/-- Total 2-Cochain Basis $C^2_{(i+1)} = C_X^2 \oplus C_Q^2 \oplus C_Z^2$ (`BDLStepXMZ pcode M`, $Z$-Check Generators). -/
abbrev BDLStepXMZ {Q M_Z M_X : Type}
    [Fintype Q] [DecidableEq Q] [Fintype M_Z] [DecidableEq M_Z] [Fintype M_X] [DecidableEq M_X]
    (pcode : CSSCode3D Q M_Z M_X) (M : ℕ) : Type :=
  BDLCX2 pcode M ⊕ BDLCQ2 pcode M ⊕ BDLCZ2 M_Z

/-- Piecewise-linear triangular grid interpolation `triGridPos3D pX pQ pZ m u v` on $\Delta(x, q, z)$. -/
def triGridPos3D (pX pQ pZ : Point3D) (m u v : ℕ) : Point3D :=
  fun i => pX i + (((u - v : ℕ) : ℝ) / (m : ℝ)) * (pQ i - pX i) +
    ((v : ℝ) / (m : ℝ)) * (pZ i - pX i)

/-- 3D position `shellVertexPos pcode M sv` of a grid 0-cell `sv : ShellVertex pcode M`. -/
def shellVertexPos {Q M_Z M_X : Type}
    [Fintype Q] [DecidableEq Q] [Fintype M_Z] [DecidableEq M_Z] [Fintype M_X] [DecidableEq M_X]
    (pcode : CSSCode3D Q M_Z M_X) (M : ℕ) (sv : ShellVertex pcode M) : Point3D :=
  match sv.val.1.val.2 with
  | Sum.inl q =>
      subdividePoint3D (pcode.posX sv.val.1.val.1) (pcode.posQ q) (M + 1) (sv.val.2.val + 1)
  | Sum.inr (Sum.inl (eZ, j)) =>
      triGridPos3D (pcode.posX sv.val.1.val.1) (pcode.posQ eZ.val.1) (pcode.posZ eZ.val.2)
        (M + 1) (sv.val.2.val + 1) (j.val + 1)
  | Sum.inr (Sum.inr z) =>
      subdividePoint3D (pcode.posX sv.val.1.val.1) (pcode.posZ z) (M + 1) (sv.val.2.val + 1)

/-- 3D position of $X$-checks in `BDLStepXMX pcode M`. -/
def bdlStepXPosX {Q M_Z M_X : Type}
    [Fintype Q] [DecidableEq Q] [Fintype M_Z] [DecidableEq M_Z] [Fintype M_X] [DecidableEq M_X]
    (pcode : CSSCode3D Q M_Z M_X) (M : ℕ) :
    BDLStepXMX pcode M → Point3D
  | Sum.inl (x, _) => pcode.posX x
  | Sum.inr (sv, _) => shellVertexPos pcode M sv

/-- 3D position of physical qubits in `BDLStepXQ pcode M`. -/
def bdlStepXPosQ {Q M_Z M_X : Type}
    [Fintype Q] [DecidableEq Q] [Fintype M_Z] [DecidableEq M_Z] [Fintype M_X] [DecidableEq M_X]
    (pcode : CSSCode3D Q M_Z M_X) (M : ℕ) :
    BDLStepXQ pcode M → Point3D
  | Sum.inl (Sum.inl (sv, _)) => shellVertexPos pcode M sv.val
  | Sum.inl (Sum.inr (Sum.inl (seg, _))) => shellVertexPos pcode M (shellSegEndVertex pcode M seg)
  | Sum.inl (Sum.inr (Sum.inr (xv, _))) => boundaryX0Pos pcode M xv.val.2
  | Sum.inr (v0, _) => xq0Pos pcode M v0

/-- 3D position of $Z$-checks in `BDLStepXMZ pcode M`. -/
def bdlStepXPosZ {Q M_Z M_X : Type}
    [Fintype Q] [DecidableEq Q] [Fintype M_Z] [DecidableEq M_Z] [Fintype M_X] [DecidableEq M_X]
    (pcode : CSSCode3D Q M_Z M_X) (M : ℕ) :
    BDLStepXMZ pcode M → Point3D
  | Sum.inl (Sum.inl (seg, _)) => shellVertexPos pcode M (shellSegEndVertex pcode M seg)
  | Sum.inl (Sum.inr (s, k, _)) => boundaryX0Pos pcode M (bxEnd pcode M s.val.2 k)
  | Sum.inr (Sum.inl (Sum.inl (eZ, k, _))) => xq0Pos pcode M (armEnd pcode M eZ k)
  | Sum.inr (Sum.inl (Sum.inr (eZ, _))) => pcode.posZ eZ.val.2
  | Sum.inr (Sum.inr (z, _)) => pcode.posZ z

/-! ## 4. Shell Endpoint Identities -/

lemma radialParent_start_eq_end_of_eq {Q M_Z M_X : Type}
    [Fintype Q] [DecidableEq Q] [Fintype M_Z] [DecidableEq M_Z] [Fintype M_X] [DecidableEq M_X]
    (pcode : CSSCode3D Q M_Z M_X) (M : ℕ) (seg : ShellSegment pcode M)
    (hr_nz : seg.val.2.1.val ≠ 0) (h_tri : seg.val.2.2.val = seg.val.2.1.val) :
    radialParentVertex pcode M (shellSegStartVertex pcode M seg) =
    radialParentVertex pcode M (shellSegEndVertex pcode M seg) := by
  have hk_nz : seg.val.2.2.val ≠ 0 := by rw [h_tri]; exact hr_nz
  have h_not_lt : ¬ (seg.val.2.2.val - 1 < (finPred seg.val.2.1).val) := by dsimp [finPred]; omega
  have h_not_lt2 : ¬ (seg.val.2.2.val < seg.val.2.1.val) := by omega
  apply Subtype.ext; apply Prod.ext
  · apply Subtype.ext; apply Prod.ext
    · rfl
    · dsimp [radialParentVertex, shellSegStartVertex, shellSegEndVertex,
        bxStartLink, bxStart, armStart, projXq0ToBoundaryX0, shellSegEndLink, shellSegEndV,
        radialParentLink, radialParentV]
      rw [dif_neg hk_nz, dif_neg h_not_lt2]; dsimp; rw [if_neg h_not_lt]
  · rfl

lemma radialParent_start_eq_start_pred {Q M_Z M_X : Type}
    [Fintype Q] [DecidableEq Q] [Fintype M_Z] [DecidableEq M_Z] [Fintype M_X] [DecidableEq M_X]
    (pcode : CSSCode3D Q M_Z M_X) (M : ℕ) (seg : ShellSegment pcode M)
    (hne : seg.val.2.2.val ≠ seg.val.2.1.val) :
    radialParentVertex pcode M (shellSegStartVertex pcode M seg) =
    shellSegStartVertex pcode M (shellSegPred pcode M seg hne) := by
  have h_le : seg.val.2.2.val ≤ seg.val.2.1.val := seg.property
  apply Subtype.ext; apply Prod.ext
  · apply Subtype.ext; apply Prod.ext
    · rfl
    · dsimp [radialParentVertex, shellSegStartVertex, shellSegPred,
        bxStartLink, bxStart, armStart, projXq0ToBoundaryX0, radialParentLink, radialParentV]
      by_cases hk0 : seg.val.2.2.val = 0
      · rw [dif_pos hk0]
      · have h_lt : seg.val.2.2.val - 1 < (finPred seg.val.2.1).val := by dsimp [finPred]; omega
        rw [dif_neg hk0]; dsimp; rw [if_pos h_lt]
  · rfl

lemma radialParent_end_eq_end_pred {Q M_Z M_X : Type}
    [Fintype Q] [DecidableEq Q] [Fintype M_Z] [DecidableEq M_Z] [Fintype M_X] [DecidableEq M_X]
    (pcode : CSSCode3D Q M_Z M_X) (M : ℕ) (seg : ShellSegment pcode M)
    (hne : seg.val.2.2.val ≠ seg.val.2.1.val) :
    radialParentVertex pcode M (shellSegEndVertex pcode M seg) =
    shellSegEndVertex pcode M (shellSegPred pcode M seg hne) := by
  have h_lt : seg.val.2.2.val < seg.val.2.1.val := Nat.lt_of_le_of_ne seg.property hne
  apply Subtype.ext; apply Prod.ext
  · apply Subtype.ext; apply Prod.ext
    · rfl
    · dsimp [radialParentVertex, shellSegEndVertex, shellSegPred,
        shellSegEndLink, shellSegEndV, radialParentLink, radialParentV]
      rw [dif_pos h_lt]; dsimp; split_ifs <;> rfl
  · rfl

lemma shellSegStartVertex_outer {Q M_Z M_X : Type}
    [Fintype Q] [DecidableEq Q] [Fintype M_Z] [DecidableEq M_Z] [Fintype M_X] [DecidableEq M_X]
    (pcode : CSSCode3D Q M_Z M_X) (M : ℕ) (s : ActiveZLink pcode) (k : Fin (M + 1)) :
    shellSegStartVertex pcode M (mkOuterShellSegment pcode M s k) =
    mkOuterShellVertex pcode M (bxStartLink pcode M s k) := rfl

lemma shellSegEndVertex_outer {Q M_Z M_X : Type}
    [Fintype Q] [DecidableEq Q] [Fintype M_Z] [DecidableEq M_Z] [Fintype M_X] [DecidableEq M_X]
    (pcode : CSSCode3D Q M_Z M_X) (M : ℕ) (s : ActiveZLink pcode) (k : Fin (M + 1)) :
    shellSegEndVertex pcode M (mkOuterShellSegment pcode M s k) =
    mkOuterShellVertex pcode M (bxEndLink pcode M s k) := by
  apply Subtype.ext; apply Prod.ext
  · apply Subtype.ext; apply Prod.ext
    · rfl
    · dsimp [shellSegEndVertex, mkOuterShellSegment, mkOuterShellVertex,
        shellSegEndLink, shellSegEndV, bxEndLink, bxEnd, armEnd, projXq0ToBoundaryX0]
      split_ifs <;> rfl
  · rfl
