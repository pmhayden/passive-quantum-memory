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

import Defs.Step2CylinderComplex

/-!
# Step 2 Three-Layer Mapping Cone Differentials, Welded Check Matrices, and Code Hierarchy

Constructs the local coboundary and connecting differentials (`bdlDeltaX0`, `bdlGXQ0`, `bdlStepXCheckX`), combinatorial `(offset, slot)` square tie-breakers, and Euclidean cell embeddings for Step 2 three-layer cylinder welding. Iterates the primal/dual welding step from `bdlSurfaceSeedBundled` to define the multiscale 3D welded CSS code hierarchy `bdlWeldedCode k`.

## References

* Part I, Section 2.3 (`subsec:step2-mapping-cone`), Definition 2.5 (`def:three-layer-mapping-cone`), Proposition 2.6 (`prop:mapping-cone-invariants`)
* Part II, Section 4 (`subsec:welded-hierarchy-cleaner`), Definition 4.2 (`def:multiscale-cluster-decoder`)
* Balasubramanian, Davydova, and Lin (2026)
-/

noncomputable section

open scoped Classical BigOperators

/-! ## 1. Local Combinatorial `(offset, slot)` Square Tie-Breaker & Coboundary Maps -/

/-- Local coboundary $\delta_X^0 : C_X^0 \to C_X^1$ (`bdlDeltaX0 pcode M`). -/
def bdlDeltaX0 {Q M_Z M_X : Type}
    [Fintype Q] [DecidableEq Q] [Fintype M_Z] [DecidableEq M_Z] [Fintype M_X] [DecidableEq M_X]
    (pcode : CSSCode3D Q M_Z M_X) (M : ℕ)
    (mX : BDLStepXMX pcode M) (qX : BDLCX1 pcode M) : ZMod 2 :=
  match qX with
  | Sum.inl (sv, b) =>
      if sv.val.val.2.val = 0 then
        (if mX = Sum.inl (sv.val.val.1.val.1, b) then 1 else 0) +
        (if mX = Sum.inr (sv.val, b) then 1 else 0)
      else
        (if mX = Sum.inr (radialParentVertex pcode M sv.val, b) then 1 else 0) +
        (if mX = Sum.inr (sv.val, b) then 1 else 0)
  | Sum.inr (Sum.inl (seg, b)) =>
      (if mX = Sum.inr (shellSegStartVertex pcode M seg, b) then 1 else 0) +
      (if mX = Sum.inr (shellSegEndVertex pcode M seg, b) then 1 else 0)
  | Sum.inr (Sum.inr (xv, v)) =>
      (if mX = Sum.inr (mkOuterShellVertex pcode M xv, 0) then 1 else 0) +
      (if mX = Sum.inr (mkOuterShellVertex pcode M xv, v.succ) then 1 else 0)

/-- Connecting coboundary $g_{XQ}^0 : C_X^0 \to C_Q^1$ (`bdlGXQ0 pcode M`). -/
def bdlGXQ0 {Q M_Z M_X : Type}
    [Fintype Q] [DecidableEq Q] [Fintype M_Z] [DecidableEq M_Z] [Fintype M_X] [DecidableEq M_X]
    (pcode : CSSCode3D Q M_Z M_X) (M : ℕ)
    (mX : BDLStepXMX pcode M) (qQ : BDLCQ1 pcode M) : ZMod 2 :=
  match mX with
  | Sum.inl _ => 0
  | Sum.inr (sv, b) =>
      if sv.val.2 = Fin.last M ∧ sv.val.1.val.2 = projXq0ToBoundaryX0 pcode M qQ.1 ∧ b = qQ.2 then
        pcode.checkX sv.val.1.val.1 (xq0OwnerQ pcode M qQ.1)
      else 0

/-- Full $X$-check matrix $\delta^0 = \delta_X^0 + g_{XQ}^0 : C_X^0 \to C_X^1 \oplus C_Q^1$. -/
def bdlStepXCheckX {Q M_Z M_X : Type}
    [Fintype Q] [DecidableEq Q] [Fintype M_Z] [DecidableEq M_Z] [Fintype M_X] [DecidableEq M_X]
    (pcode : CSSCode3D Q M_Z M_X) (M : ℕ)
    (mX : BDLStepXMX pcode M) (q : BDLStepXQ pcode M) : ZMod 2 :=
  match q with
  | Sum.inl qX => bdlDeltaX0 pcode M mX qX
  | Sum.inr qQ => bdlGXQ0 pcode M mX qQ

/-- Lexicographically ordered discrete local `(offset, slot)` key carrier $\mathbb{Z}^3 \times_{\mathrm{lex}} \mathbb{N}$. -/
abbrev LocalOffsetSlotLex : Type := ℤ ×ₗ (ℤ ×ₗ (ℤ ×ₗ ℕ))

/-- Purely local combinatorial `(offset, slot)` tie-breaker key relative to check site `x`:
    orders candidate qubits $q \in \mathrm{supp}(x) \cap \mathrm{supp}(z)$ by their discrete integer
    offset $(\lfloor q_0 \rfloor - \lfloor x_0 \rfloor, \lfloor q_1 \rfloor - \lfloor x_1 \rfloor,
    \lfloor q_2 \rfloor - \lfloor x_2 \rfloor)$ and local slot index `slotQ q`. -/
def localOffsetSlotKey {Q M_Z M_X : Type}
    [Fintype Q] [DecidableEq Q] [Fintype M_Z] [DecidableEq M_Z] [Fintype M_X] [DecidableEq M_X]
    (pcode : CSSCode3D Q M_Z M_X) (slotQ : Q → ℕ) (x : M_X) (q : Q) : LocalOffsetSlotLex :=
  toLex (⌊pcode.posQ q 0⌋ - ⌊pcode.posX x 0⌋,
    toLex (⌊pcode.posQ q 1⌋ - ⌊pcode.posX x 1⌋,
      toLex (⌊pcode.posQ q 2⌋ - ⌊pcode.posX x 2⌋, slotQ q)))

/-- Minimum local `(offset, slot)` key over `q ∈ supp(x) ∩ supp(z)` via `Finset.min'`. -/
noncomputable def canonicalSquareMinKey {Q M_Z M_X : Type}
    [Fintype Q] [DecidableEq Q] [Fintype M_Z] [DecidableEq M_Z] [Fintype M_X] [DecidableEq M_X]
    (pcode : CSSCode3D Q M_Z M_X) (slotQ : Q → ℕ) (x : M_X) (z : M_Z)
    (h : ∃ q : Q, pcode.checkX x q ≠ 0 ∧ pcode.checkZ z q ≠ 0) : LocalOffsetSlotLex :=
  ((Finset.univ.filter (fun q : Q => pcode.checkX x q ≠ 0 ∧ pcode.checkZ z q ≠ 0)).image
    (localOffsetSlotKey pcode slotQ x)).min'
    (by rcases h with ⟨q, hq⟩; exact ⟨_, Finset.mem_image.mpr ⟨q, Finset.mem_filter.mpr ⟨Finset.mem_univ q, hq⟩, rfl⟩⟩)

lemma exists_canonicalSquareQ_at_minKey {Q M_Z M_X : Type}
    [Fintype Q] [DecidableEq Q] [Fintype M_Z] [DecidableEq M_Z] [Fintype M_X] [DecidableEq M_X]
    (pcode : CSSCode3D Q M_Z M_X) (slotQ : Q → ℕ) (x : M_X) (z : M_Z)
    (h : ∃ q : Q, pcode.checkX x q ≠ 0 ∧ pcode.checkZ z q ≠ 0) :
    ∃ q : Q, (pcode.checkX x q ≠ 0 ∧ pcode.checkZ z q ≠ 0) ∧
      localOffsetSlotKey pcode slotQ x q = canonicalSquareMinKey pcode slotQ x z h := by
  have h_mem := Finset.min'_mem
    ((Finset.univ.filter (fun q : Q => pcode.checkX x q ≠ 0 ∧ pcode.checkZ z q ≠ 0)).image
      (localOffsetSlotKey pcode slotQ x))
    (by rcases h with ⟨q, hq⟩; exact ⟨_, Finset.mem_image.mpr ⟨q, Finset.mem_filter.mpr ⟨Finset.mem_univ q, hq⟩, rfl⟩⟩)
  rcases Finset.mem_image.mp h_mem with ⟨q, hq_mem, hq_eq⟩
  exact ⟨q, (Finset.mem_filter.mp hq_mem).2, hq_eq⟩

/-- Canonical qubit representative `q` of a corner square `(x, z)`, selected deterministically by
    minimizing the local combinatorial `(offset, slot)` key `localOffsetSlotKey`. -/
noncomputable def canonicalSquareQ {Q M_Z M_X : Type}
    [Fintype Q] [DecidableEq Q] [Fintype M_Z] [DecidableEq M_Z] [Fintype M_X] [DecidableEq M_X]
    (pcode : CSSCode3D Q M_Z M_X) (slotQ : Q → ℕ := fun _ => 0) (x : M_X) (z : M_Z)
    (h : ∃ q : Q, pcode.checkX x q ≠ 0 ∧ pcode.checkZ z q ≠ 0) : Q :=
  Classical.choose (exists_canonicalSquareQ_at_minKey pcode slotQ x z h)

lemma canonicalSquareQ_spec {Q M_Z M_X : Type}
    [Fintype Q] [DecidableEq Q] [Fintype M_Z] [DecidableEq M_Z] [Fintype M_X] [DecidableEq M_X]
    (pcode : CSSCode3D Q M_Z M_X) (slotQ : Q → ℕ := fun _ => 0) (x : M_X) (z : M_Z)
    (h : ∃ q : Q, pcode.checkX x q ≠ 0 ∧ pcode.checkZ z q ≠ 0) :
    pcode.checkX x (canonicalSquareQ pcode slotQ x z h) ≠ 0 ∧
    pcode.checkZ z (canonicalSquareQ pcode slotQ x z h) ≠ 0 :=
  (Classical.choose_spec (exists_canonicalSquareQ_at_minKey pcode slotQ x z h)).1

/-- The `r = 0` radial spoke vertex `((x, Sum.inl q), 0)` for `checkX x q ≠ 0`. -/
def cornerSpoke {Q M_Z M_X : Type}
    [Fintype Q] [DecidableEq Q] [Fintype M_Z] [DecidableEq M_Z] [Fintype M_X] [DecidableEq M_X]
    (pcode : CSSCode3D Q M_Z M_X) (M : ℕ) (x : M_X) (q : Q) (hX : pcode.checkX x q ≠ 0) :
    ShellVertex pcode M :=
  ⟨(⟨(x, Sum.inl q), hX⟩, ⟨0, Nat.zero_lt_succ M⟩), trivial⟩

lemma cornerSpoke_not_isDiagZeroVertex {Q M_Z M_X : Type}
    [Fintype Q] [DecidableEq Q] [Fintype M_Z] [DecidableEq M_Z] [Fintype M_X] [DecidableEq M_X]
    (pcode : CSSCode3D Q M_Z M_X) (M : ℕ) (x : M_X) (q : Q) (hX : pcode.checkX x q ≠ 0) :
    ¬ IsDiagZeroVertex pcode M (cornerSpoke pcode M x q hX) := by
  rintro ⟨_, z', hz'⟩; dsimp [cornerSpoke] at hz'; exact Sum.inl_ne_inr hz'

def cornerSpokeRadial {Q M_Z M_X : Type}
    [Fintype Q] [DecidableEq Q] [Fintype M_Z] [DecidableEq M_Z] [Fintype M_X] [DecidableEq M_X]
    (pcode : CSSCode3D Q M_Z M_X) (M : ℕ) (x : M_X) (q : Q) (hX : pcode.checkX x q ≠ 0) :
    RadialVertex pcode M :=
  ⟨cornerSpoke pcode M x q hX, cornerSpoke_not_isDiagZeroVertex pcode M x q hX⟩

lemma shellSegStartVertex_not_isDiagZeroVertex {Q M_Z M_X : Type}
    [Fintype Q] [DecidableEq Q] [Fintype M_Z] [DecidableEq M_Z] [Fintype M_X] [DecidableEq M_X]
    (pcode : CSSCode3D Q M_Z M_X) (M : ℕ) (seg : ShellSegment pcode M) :
    ¬ IsDiagZeroVertex pcode M (shellSegStartVertex pcode M seg) := by
  rintro ⟨_, z', hz'⟩; dsimp [shellSegStartVertex, bxStartLink, bxStart, armStart] at hz'
  split_ifs at hz' <;> dsimp [projXq0ToBoundaryX0] at hz' <;> nomatch hz'

def shellSegStartRadial {Q M_Z M_X : Type}
    [Fintype Q] [DecidableEq Q] [Fintype M_Z] [DecidableEq M_Z] [Fintype M_X] [DecidableEq M_X]
    (pcode : CSSCode3D Q M_Z M_X) (M : ℕ) (seg : ShellSegment pcode M) :
    RadialVertex pcode M :=
  ⟨shellSegStartVertex pcode M seg, shellSegStartVertex_not_isDiagZeroVertex pcode M seg⟩

def shellSegEndRadial {Q M_Z M_X : Type}
    [Fintype Q] [DecidableEq Q] [Fintype M_Z] [DecidableEq M_Z] [Fintype M_X] [DecidableEq M_X]
    (pcode : CSSCode3D Q M_Z M_X) (M : ℕ) (seg : ShellSegment pcode M) (hr : seg.val.2.1.val ≠ 0) :
    RadialVertex pcode M :=
  ⟨shellSegEndVertex pcode M seg, fun h => hr h.1⟩

/-- The `r = 0` auxiliary diagonal vertex `((x, Sum.inr (Sum.inr z)), 0)`. -/
def cornerDiagVertex {Q M_Z M_X : Type}
    [Fintype Q] [DecidableEq Q] [Fintype M_Z] [DecidableEq M_Z] [Fintype M_X] [DecidableEq M_X]
    (pcode : CSSCode3D Q M_Z M_X) (M : ℕ) (x : M_X) (z : M_Z)
    (h_ex : ∃ q : Q, pcode.checkX x q ≠ 0 ∧ pcode.checkZ z q ≠ 0) :
    ShellVertex pcode M :=
  ⟨(⟨(x, Sum.inr (Sum.inr z)), h_ex⟩, ⟨0, Nat.zero_lt_succ M⟩), trivial⟩

/-- The `r = 0, k = 0` corner segment `((x, (q, z)), (0, 0))` for `checkX x q ≠ 0` and `checkZ z q ≠ 0`. -/
def cornerSeg {Q M_Z M_X : Type}
    [Fintype Q] [DecidableEq Q] [Fintype M_Z] [DecidableEq M_Z] [Fintype M_X] [DecidableEq M_X]
    (pcode : CSSCode3D Q M_Z M_X) (M : ℕ) (x : M_X) (q : Q) (z : M_Z)
    (hX : pcode.checkX x q ≠ 0) (hZ : pcode.checkZ z q ≠ 0) :
    ShellSegment pcode M :=
  ⟨(⟨(x, ⟨(q, z), hZ⟩), hX⟩, (⟨0, Nat.zero_lt_succ M⟩, ⟨0, Nat.zero_lt_succ M⟩)), le_rfl⟩

/-- Local coboundary $\delta_X^1 : C_X^1 \to C_X^2$ (`bdlDeltaX1 pcode M`) with local `(offset, slot)` square tie-breaking. -/
noncomputable def bdlDeltaX1 {Q M_Z M_X : Type}
    [Fintype Q] [DecidableEq Q] [Fintype M_Z] [DecidableEq M_Z] [Fintype M_X] [DecidableEq M_X]
    (pcode : CSSCode3D Q M_Z M_X) (M : ℕ)
    (mZX : BDLCX2 pcode M) (qX : BDLCX1 pcode M) : ZMod 2 :=
  match mZX with
  | Sum.inl (seg, b) =>
      if h_tri : seg.val.2.2.val = seg.val.2.1.val then
        if hr0 : seg.val.2.1.val = 0 then
          if seg.val.1.val.2.val.1 = canonicalSquareQ pcode (fun _ => 0) seg.val.1.val.1 seg.val.1.val.2.val.2
                ⟨seg.val.1.val.2.val.1, seg.val.1.property, seg.val.1.val.2.property⟩ then
            ∑ q' : Q,
              if hX' : pcode.checkX seg.val.1.val.1 q' ≠ 0 then
                if hZ' : pcode.checkZ seg.val.1.val.2.val.2 q' ≠ 0 then
                  (if qX = Sum.inl (cornerSpokeRadial pcode M seg.val.1.val.1 q' hX', b) then 1 else 0) +
                  (if qX = Sum.inr (Sum.inl (cornerSeg pcode M seg.val.1.val.1 q' seg.val.1.val.2.val.2 hX' hZ', b)) then 1 else 0)
                else 0
              else 0
          else 0
        else
          (if qX = Sum.inl (shellSegStartRadial pcode M seg, b) then 1 else 0) +
          (if qX = Sum.inl (shellSegEndRadial pcode M seg hr0, b) then 1 else 0) +
          (if qX = Sum.inr (Sum.inl (seg, b)) then 1 else 0)
      else
        (if qX = Sum.inl (shellSegStartRadial pcode M seg, b) then 1 else 0) +
        (if qX = Sum.inl (shellSegEndRadial pcode M seg (by have := seg.property; omega), b) then 1 else 0) +
        (if qX = Sum.inr (Sum.inl (shellSegPred pcode M seg h_tri, b)) then 1 else 0) +
        (if qX = Sum.inr (Sum.inl (seg, b)) then 1 else 0)
  | Sum.inr (s, k, v) =>
      (if qX = Sum.inr (Sum.inl (mkOuterShellSegment pcode M s k, 0)) then 1 else 0) +
      (if qX = Sum.inr (Sum.inl (mkOuterShellSegment pcode M s k, v.succ)) then 1 else 0) +
      (if qX = Sum.inr (Sum.inr (bxStartLink pcode M s k, v)) then 1 else 0) +
      (if qX = Sum.inr (Sum.inr (bxEndLink pcode M s k, v)) then 1 else 0)

/-- Connecting coboundary $g_{XQ}^1 : C_X^1 \to C_Q^2$ (`bdlGXQ1 pcode M`). -/
def bdlGXQ1 {Q M_Z M_X : Type}
    [Fintype Q] [DecidableEq Q] [Fintype M_Z] [DecidableEq M_Z] [Fintype M_X] [DecidableEq M_X]
    (pcode : CSSCode3D Q M_Z M_X) (M : ℕ)
    (mZQ : BDLCQ2 pcode M) (qX : BDLCX1 pcode M) : ZMod 2 :=
  match mZQ, qX with
  | Sum.inl (eZ, k, bZ), Sum.inr (Sum.inl (seg, bX)) =>
      if seg.val.2.1 = Fin.last M ∧ seg.val.1.val.2 = eZ ∧ seg.val.2.2 = k ∧ bX = bZ then
        pcode.checkX seg.val.1.val.1 eZ.val.1
      else 0
  | Sum.inr (eZ, vZ), Sum.inr (Sum.inr (xv, vX)) =>
      if xv.val.2 = Sum.inr (Sum.inr eZ.val.2) ∧ vX = vZ then
        pcode.checkX xv.val.1 eZ.val.1
      else 0
  | _, _ => 0

/-- Local coboundary $\delta_Q^1 : C_Q^1 \to C_Q^2$ (`bdlDeltaQ1 pcode M`). -/
def bdlDeltaQ1 {Q M_Z M_X : Type}
    [Fintype Q] [DecidableEq Q] [Fintype M_Z] [DecidableEq M_Z] [Fintype M_X] [DecidableEq M_X]
    (pcode : CSSCode3D Q M_Z M_X) (M : ℕ)
    (mZQ : BDLCQ2 pcode M) (qQ : BDLCQ1 pcode M) : ZMod 2 :=
  match mZQ with
  | Sum.inl (eZ, k, bZ) =>
      (if qQ = (armStart pcode M eZ k, bZ) then 1 else 0) +
      (if qQ = (armEnd pcode M eZ k, bZ) then 1 else 0)
  | Sum.inr (eZ, v) =>
      (if qQ = (Sum.inr (Sum.inr eZ), 0) then 1 else 0) +
      (if qQ = (Sum.inr (Sum.inr eZ), v.succ) then 1 else 0)

/-- Connecting coboundary $g_{QZ}^1 : C_Q^1 \to C_Z^2$ (`bdlGQZ1 pcode M`). -/
def bdlGQZ1 {Q M_Z M_X : Type}
    [Fintype Q] [DecidableEq Q] [Fintype M_Z] [DecidableEq M_Z] [Fintype M_X] [DecidableEq M_X]
    (pcode : CSSCode3D Q M_Z M_X) (M : ℕ)
    (mZZ : BDLCZ2 M_Z) (qQ : BDLCQ1 pcode M) : ZMod 2 :=
  match qQ.1 with
  | Sum.inr (Sum.inr eZ) => if eZ.val.2 = mZZ.1 ∧ qQ.2 = mZZ.2 then 1 else 0
  | _ => 0

/-- Full $Z$-check matrix $\delta^1 = \delta_X^1 + g_{XQ}^1 + \delta_Q^1 + g_{QZ}^1$. -/
noncomputable def bdlStepXCheckZ {Q M_Z M_X : Type}
    [Fintype Q] [DecidableEq Q] [Fintype M_Z] [DecidableEq M_Z] [Fintype M_X] [DecidableEq M_X]
    (pcode : CSSCode3D Q M_Z M_X) (M : ℕ)
    (mZ : BDLStepXMZ pcode M) (q : BDLStepXQ pcode M) : ZMod 2 :=
  match mZ, q with
  | Sum.inl mZX, Sum.inl qX => bdlDeltaX1 pcode M mZX qX
  | Sum.inl _, Sum.inr _ => 0
  | Sum.inr (Sum.inl mZQ), Sum.inl qX => bdlGXQ1 pcode M mZQ qX
  | Sum.inr (Sum.inl mZQ), Sum.inr qQ => bdlDeltaQ1 pcode M mZQ qQ
  | Sum.inr (Sum.inr _), Sum.inl _ => 0
  | Sum.inr (Sum.inr mZZ), Sum.inr qQ => bdlGQZ1 pcode M mZZ qQ

/-! ## 2. Exactness $\delta^1 \circ \delta^0 = 0$ and Replacement Operators $R_X, R_Z$ -/

lemma sum_activeZ_eq {Q M_Z M_X : Type}
    [Fintype Q] [DecidableEq Q] [Fintype M_Z] [DecidableEq M_Z] [Fintype M_X] [DecidableEq M_X]
    (pcode : CSSCode3D Q M_Z M_X) (z0 : M_Z) (f : Q → ZMod 2) :
    (∑ eZ : ActiveZ pcode, if eZ.val.2 = z0 then f eZ.val.1 else 0) =
    ∑ q : Q, f q * pcode.checkZ z0 q := by
  have h1 : (∑ eZ : ActiveZ pcode, if eZ.val.2 = z0 then f eZ.val.1 else 0) =
      ∑ p ∈ Finset.univ.filter (fun p : Q × M_Z => pcode.checkZ p.2 p.1 ≠ 0),
        (if p.2 = z0 then f p.1 else 0) :=
    (Finset.sum_subtype (Finset.univ.filter (fun p : Q × M_Z => pcode.checkZ p.2 p.1 ≠ 0))
      (p := fun p : Q × M_Z => pcode.checkZ p.2 p.1 ≠ 0)
      (fun _ => Finset.mem_filter.trans (and_iff_right (Finset.mem_univ _)))
      (fun p => if p.2 = z0 then f p.1 else 0)).symm
  have h2 : (∑ p ∈ Finset.univ.filter (fun p : Q × M_Z => pcode.checkZ p.2 p.1 ≠ 0),
        (if p.2 = z0 then f p.1 else 0)) =
      ∑ p : Q × M_Z, if pcode.checkZ p.2 p.1 ≠ 0 then (if p.2 = z0 then f p.1 else 0) else 0 :=
    Finset.sum_filter (fun p : Q × M_Z => pcode.checkZ p.2 p.1 ≠ 0)
      (fun p => if p.2 = z0 then f p.1 else 0)
  rw [h1, h2, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl (fun q _ => ?_)
  rw [Finset.sum_eq_single z0]
  · simp only [↓reduceIte, ne_eq, ite_not]
    exact zmod2_if_eq_zero_mul (f q) (pcode.checkZ z0 q)
  · intro z _ hne; simp [hne]
  · intro h_abs; exact False.elim (h_abs (Finset.mem_univ z0))

lemma sum_deltaX0_mul_indicator {Q M_Z M_X : Type}
    [Fintype Q] [DecidableEq Q] [Fintype M_Z] [DecidableEq M_Z] [Fintype M_X] [DecidableEq M_X]
    (pcode : CSSCode3D Q M_Z M_X) (M : ℕ) (mX : BDLStepXMX pcode M) (q0 : BDLCX1 pcode M) :
    (∑ qX : BDLCX1 pcode M, bdlDeltaX0 pcode M mX qX * (if qX = q0 then 1 else 0)) =
    bdlDeltaX0 pcode M mX q0 := by
  rw [Finset.sum_eq_single q0] <;> [simp; (intro qX _ hne; simp [hne]); (intro h_abs; exact False.elim (h_abs (Finset.mem_univ q0)))]

lemma sum_gXQ0_mul_indicator {Q M_Z M_X : Type}
    [Fintype Q] [DecidableEq Q] [Fintype M_Z] [DecidableEq M_Z] [Fintype M_X] [DecidableEq M_X]
    (pcode : CSSCode3D Q M_Z M_X) (M : ℕ) (mX : BDLStepXMX pcode M) (q0 : BDLCQ1 pcode M) :
    (∑ qQ : BDLCQ1 pcode M, bdlGXQ0 pcode M mX qQ * (if qQ = q0 then 1 else 0)) =
    bdlGXQ0 pcode M mX q0 := by
  rw [Finset.sum_eq_single q0] <;> [simp; (intro qQ _ hne; simp [hne]); (intro h_abs; exact False.elim (h_abs (Finset.mem_univ q0)))]

lemma sum_cornerSquare_deltaX0 {Q M_Z M_X : Type}
    [Fintype Q] [DecidableEq Q] [Fintype M_Z] [DecidableEq M_Z] [Fintype M_X] [DecidableEq M_X]
    (pcode : CSSCode3D Q M_Z M_X) (M : ℕ) (mX : BDLStepXMX pcode M) (x : M_X) (z : M_Z)
    (h_ex : ∃ q : Q, pcode.checkX x q ≠ 0 ∧ pcode.checkZ z q ≠ 0) (b : Fin 3) :
    (∑ qX : BDLCX1 pcode M, bdlDeltaX0 pcode M mX qX *
      (∑ q' : Q, if hX' : pcode.checkX x q' ≠ 0 then if hZ' : pcode.checkZ z q' ≠ 0 then
        (if qX = Sum.inl (cornerSpokeRadial pcode M x q' hX', b) then 1 else 0) +
        (if qX = Sum.inr (Sum.inl (cornerSeg pcode M x q' z hX' hZ', b)) then 1 else 0)
      else 0 else 0)) = 0 := by
  simp_rw [Finset.mul_sum]; rw [Finset.sum_comm]
  have h_term : ∀ q' : Q,
      (∑ qX : BDLCX1 pcode M, bdlDeltaX0 pcode M mX qX *
        (if hX' : pcode.checkX x q' ≠ 0 then if hZ' : pcode.checkZ z q' ≠ 0 then
          (if qX = Sum.inl (cornerSpokeRadial pcode M x q' hX', b) then 1 else 0) +
          (if qX = Sum.inr (Sum.inl (cornerSeg pcode M x q' z hX' hZ', b)) then 1 else 0)
        else 0 else 0)) =
      ((if mX = Sum.inl (x, b) then (1 : ZMod 2) else 0) +
       (if mX = Sum.inr (cornerDiagVertex pcode M x z h_ex, b) then (1 : ZMod 2) else 0)) *
      pcode.checkX x q' * pcode.checkZ z q' := by
    intro q'
    by_cases hX' : pcode.checkX x q' ≠ 0
    · by_cases hZ' : pcode.checkZ z q' ≠ 0
      · have h_in : ∀ qX : BDLCX1 pcode M, bdlDeltaX0 pcode M mX qX *
            (if hX'' : pcode.checkX x q' ≠ 0 then if hZ'' : pcode.checkZ z q' ≠ 0 then
              (if qX = Sum.inl (cornerSpokeRadial pcode M x q' hX'', b) then 1 else 0) +
              (if qX = Sum.inr (Sum.inl (cornerSeg pcode M x q' z hX'' hZ'', b)) then 1 else 0)
            else 0 else 0) =
            bdlDeltaX0 pcode M mX qX * (if qX = Sum.inl (cornerSpokeRadial pcode M x q' hX', b) then 1 else 0) +
            bdlDeltaX0 pcode M mX qX * (if qX = Sum.inr (Sum.inl (cornerSeg pcode M x q' z hX' hZ', b)) then 1 else 0) :=
          fun qX => by rw [dif_pos hX', dif_pos hZ', mul_add]
        simp_rw [h_in, Finset.sum_add_distrib, sum_deltaX0_mul_indicator]
        have hr0 : (cornerSpokeRadial pcode M x q' hX').val.val.2.val = 0 := rfl
        have h_start : shellSegStartVertex pcode M (cornerSeg pcode M x q' z hX' hZ') = cornerSpoke pcode M x q' hX' := by
          apply Subtype.ext; apply Prod.ext <;> [ (apply Subtype.ext; apply Prod.ext <;> [rfl; dsimp [shellSegStartVertex, cornerSeg, cornerSpoke, bxStartLink, bxStart, armStart, projXq0ToBoundaryX0]]); rfl]
        have h_end : shellSegEndVertex pcode M (cornerSeg pcode M x q' z hX' hZ') = cornerDiagVertex pcode M x z h_ex := by
          apply Subtype.ext; apply Prod.ext <;> [ (apply Subtype.ext; apply Prod.ext <;> [rfl; dsimp [shellSegEndVertex, cornerSeg, cornerDiagVertex, shellSegEndLink, shellSegEndV]]); rfl]
        have hx_spoke : (cornerSpokeRadial pcode M x q' hX').val.val.1.val.1 = x := rfl
        have h_spoke_val : (cornerSpokeRadial pcode M x q' hX').val = cornerSpoke pcode M x q' hX' := rfl
        dsimp [bdlDeltaX0]; rw [if_pos hr0, hx_spoke, h_spoke_val, h_start, h_end]
        rw [zmod2_ne_zero_iff_eq_one _ hX', zmod2_ne_zero_iff_eq_one _ hZ', mul_one, mul_one]
        exact zmod2_add_mid_cancel _ _ _
      · have hZ0 : pcode.checkZ z q' = 0 := Classical.not_not.mp hZ'
        rw [Finset.sum_eq_zero (fun qX _ => by rw [dif_pos hX', dif_neg hZ', mul_zero]), hZ0, mul_zero]
    · have hX0 : pcode.checkX x q' = 0 := Classical.not_not.mp hX'
      rw [Finset.sum_eq_zero (fun qX _ => by rw [dif_neg hX', mul_zero]), hX0, mul_zero, zero_mul]
  simp_rw [h_term]
  have h_fac : (∑ q' : Q, ((if mX = Sum.inl (x, b) then (1 : ZMod 2) else 0) +
        (if mX = Sum.inr (cornerDiagVertex pcode M x z h_ex, b) then (1 : ZMod 2) else 0)) *
        pcode.checkX x q' * pcode.checkZ z q') =
      ((if mX = Sum.inl (x, b) then (1 : ZMod 2) else 0) +
       (if mX = Sum.inr (cornerDiagVertex pcode M x z h_ex, b) then (1 : ZMod 2) else 0)) *
        (∑ q' : Q, pcode.checkX x q' * pcode.checkZ z q') := by
    rw [Finset.mul_sum]; refine Finset.sum_congr rfl (fun _ _ => by ring)
  rw [h_fac, pcode.commutativity x z, mul_zero]

/-- Top-row exactness $\delta_X^1 \circ \delta_X^0 = 0$. -/
lemma bdlDeltaX1_comp_bdlDeltaX0 {Q M_Z M_X : Type}
    [Fintype Q] [DecidableEq Q] [Fintype M_Z] [DecidableEq M_Z] [Fintype M_X] [DecidableEq M_X]
    (pcode : CSSCode3D Q M_Z M_X) (M : ℕ) (mX : BDLStepXMX pcode M) (mZX : BDLCX2 pcode M) :
    (∑ qX : BDLCX1 pcode M, bdlDeltaX0 pcode M mX qX * bdlDeltaX1 pcode M mZX qX) = 0 := by
  rcases mZX with ⟨seg, b⟩ | ⟨s, k, v⟩
  · by_cases h_tri : seg.val.2.2.val = seg.val.2.1.val
    · by_cases hr : seg.val.2.1.val = 0
      · have h_exp : ∀ qX : BDLCX1 pcode M, bdlDeltaX0 pcode M mX qX * bdlDeltaX1 pcode M (Sum.inl (seg, b)) qX =
            if seg.val.1.val.2.val.1 = canonicalSquareQ pcode (fun _ => 0) seg.val.1.val.1 seg.val.1.val.2.val.2
                  ⟨seg.val.1.val.2.val.1, seg.val.1.property, seg.val.1.val.2.property⟩ then
              bdlDeltaX0 pcode M mX qX * (∑ q' : Q, if hX' : pcode.checkX seg.val.1.val.1 q' ≠ 0 then
                if hZ' : pcode.checkZ seg.val.1.val.2.val.2 q' ≠ 0 then
                  (if qX = Sum.inl (cornerSpokeRadial pcode M seg.val.1.val.1 q' hX', b) then 1 else 0) +
                  (if qX = Sum.inr (Sum.inl (cornerSeg pcode M seg.val.1.val.1 q' seg.val.1.val.2.val.2 hX' hZ', b)) then 1 else 0)
                else 0 else 0) else 0 := by
          intro qX; dsimp [bdlDeltaX1]; rw [dif_pos h_tri, dif_pos hr]
          split_ifs <;> [rfl; rw [mul_zero]]
        simp_rw [h_exp]
        split_ifs with h_can
        · exact sum_cornerSquare_deltaX0 pcode M mX seg.val.1.val.1 seg.val.1.val.2.val.2 ⟨seg.val.1.val.2.val.1, seg.val.1.property, seg.val.1.val.2.property⟩ b
        · exact Finset.sum_const_zero
      · have h_exp : ∀ qX : BDLCX1 pcode M, bdlDeltaX0 pcode M mX qX * bdlDeltaX1 pcode M (Sum.inl (seg, b)) qX =
            bdlDeltaX0 pcode M mX qX * (if qX = Sum.inl (shellSegStartRadial pcode M seg, b) then 1 else 0) +
            bdlDeltaX0 pcode M mX qX * (if qX = Sum.inl (shellSegEndRadial pcode M seg hr, b) then 1 else 0) +
            bdlDeltaX0 pcode M mX qX * (if qX = Sum.inr (Sum.inl (seg, b)) then 1 else 0) :=
          fun qX => by dsimp [bdlDeltaX1]; rw [dif_pos h_tri, dif_neg hr]; ring
        simp_rw [h_exp, Finset.sum_add_distrib, sum_deltaX0_mul_indicator]
        have hr_s : (shellSegStartVertex pcode M seg).val.2.val ≠ 0 := hr
        have hr_e : (shellSegEndVertex pcode M seg).val.2.val ≠ 0 := hr
        dsimp [bdlDeltaX0, shellSegStartRadial, shellSegEndRadial]
        rw [if_neg hr_s, if_neg hr_e, radialParent_start_eq_end_of_eq pcode M seg hr h_tri]
        exact zmod2_cancel3 _ _ _
    · have hr : seg.val.2.1.val ≠ 0 := by have := seg.property; omega
      have h_exp : ∀ qX : BDLCX1 pcode M, bdlDeltaX0 pcode M mX qX * bdlDeltaX1 pcode M (Sum.inl (seg, b)) qX =
          bdlDeltaX0 pcode M mX qX * (if qX = Sum.inl (shellSegStartRadial pcode M seg, b) then 1 else 0) +
          bdlDeltaX0 pcode M mX qX * (if qX = Sum.inl (shellSegEndRadial pcode M seg hr, b) then 1 else 0) +
          bdlDeltaX0 pcode M mX qX * (if qX = Sum.inr (Sum.inl (shellSegPred pcode M seg h_tri, b)) then 1 else 0) +
          bdlDeltaX0 pcode M mX qX * (if qX = Sum.inr (Sum.inl (seg, b)) then 1 else 0) :=
        fun qX => by dsimp [bdlDeltaX1]; rw [dif_neg h_tri]; ring
      simp_rw [h_exp, Finset.sum_add_distrib, sum_deltaX0_mul_indicator]
      have hr_s : (shellSegStartVertex pcode M seg).val.2.val ≠ 0 := hr
      have hr_e : (shellSegEndVertex pcode M seg).val.2.val ≠ 0 := hr
      dsimp [bdlDeltaX0, shellSegStartRadial, shellSegEndRadial]
      rw [if_neg hr_s, if_neg hr_e, radialParent_start_eq_start_pred pcode M seg h_tri, radialParent_end_eq_end_pred pcode M seg h_tri]
      exact zmod2_cancel4 _ _ _ _
  · have h_exp : ∀ qX : BDLCX1 pcode M, bdlDeltaX0 pcode M mX qX * bdlDeltaX1 pcode M (Sum.inr (s, k, v)) qX =
        bdlDeltaX0 pcode M mX qX * (if qX = Sum.inr (Sum.inl (mkOuterShellSegment pcode M s k, 0)) then 1 else 0) +
        bdlDeltaX0 pcode M mX qX * (if qX = Sum.inr (Sum.inl (mkOuterShellSegment pcode M s k, v.succ)) then 1 else 0) +
        bdlDeltaX0 pcode M mX qX * (if qX = Sum.inr (Sum.inr (bxStartLink pcode M s k, v)) then 1 else 0) +
        bdlDeltaX0 pcode M mX qX * (if qX = Sum.inr (Sum.inr (bxEndLink pcode M s k, v)) then 1 else 0) :=
      fun qX => by dsimp [bdlDeltaX1]; ring
    simp_rw [h_exp, Finset.sum_add_distrib, sum_deltaX0_mul_indicator]
    dsimp [bdlDeltaX0]; rw [shellSegStartVertex_outer, shellSegEndVertex_outer]
    exact zmod2_cancel4 _ _ _ _

set_option maxHeartbeats 800000 in
/-- Middle-row compatibility $g_{XQ}^1 \circ \delta_X^0 + \delta_Q^1 \circ g_{XQ}^0 = 0$. -/
lemma bdlGXQ1_deltaX0_add_deltaQ1_gXQ0 {Q M_Z M_X : Type}
    [Fintype Q] [DecidableEq Q] [Fintype M_Z] [DecidableEq M_Z] [Fintype M_X] [DecidableEq M_X]
    (pcode : CSSCode3D Q M_Z M_X) (M : ℕ) (mX : BDLStepXMX pcode M) (mZQ : BDLCQ2 pcode M) :
    (∑ qX : BDLCX1 pcode M, bdlDeltaX0 pcode M mX qX * bdlGXQ1 pcode M mZQ qX) +
    (∑ qQ : BDLCQ1 pcode M, bdlGXQ0 pcode M mX qQ * bdlDeltaQ1 pcode M mZQ qQ) = 0 := by
  rcases mZQ with ⟨eZ, k, bZ⟩ | ⟨eZ, v⟩
  · have h_qQ : (∑ qQ : BDLCQ1 pcode M, bdlGXQ0 pcode M mX qQ * bdlDeltaQ1 pcode M (Sum.inl (eZ, k, bZ)) qQ) =
        bdlGXQ0 pcode M mX (armStart pcode M eZ k, bZ) + bdlGXQ0 pcode M mX (armEnd pcode M eZ k, bZ) := by
      have h_exp : ∀ qQ : BDLCQ1 pcode M, bdlGXQ0 pcode M mX qQ * bdlDeltaQ1 pcode M (Sum.inl (eZ, k, bZ)) qQ =
          bdlGXQ0 pcode M mX qQ * (if qQ = (armStart pcode M eZ k, bZ) then 1 else 0) +
          bdlGXQ0 pcode M mX qQ * (if qQ = (armEnd pcode M eZ k, bZ) then 1 else 0) := fun qQ => by dsimp [bdlDeltaQ1]; ring
      simp_rw [h_exp, Finset.sum_add_distrib, sum_gXQ0_mul_indicator]
    rw [h_qQ]
    rcases mX with ⟨x0, b0⟩ | ⟨sv, b0⟩
    · have h_qX_zero : (∑ qX : BDLCX1 pcode M, bdlDeltaX0 pcode M (Sum.inl (x0, b0)) qX * bdlGXQ1 pcode M (Sum.inl (eZ, k, bZ)) qX) = 0 := by
        apply Finset.sum_eq_zero; intro qX _; rcases qX with _ | (_ | _) <;> dsimp [bdlDeltaX0, bdlGXQ1] <;> simp
      rw [h_qX_zero]; dsimp [bdlGXQ0]; simp
    · let xv := sv.val.1
      by_cases hs : pcode.checkX xv.val.1 eZ.val.1 ≠ 0
      · let s0 : ActiveZLink pcode := ⟨(xv.val.1, eZ), hs⟩
        let seg0 : ShellSegment pcode M := mkOuterShellSegment pcode M s0 k
        have h_qX : (∑ qX : BDLCX1 pcode M, bdlDeltaX0 pcode M (Sum.inr (sv, b0)) qX * bdlGXQ1 pcode M (Sum.inl (eZ, k, bZ)) qX) =
            bdlDeltaX0 pcode M (Sum.inr (sv, b0)) (Sum.inr (Sum.inl (seg0, bZ))) * pcode.checkX xv.val.1 eZ.val.1 := by
          rw [Finset.sum_eq_single (Sum.inr (Sum.inl (seg0, bZ)))]
          · dsimp [bdlGXQ1, seg0, mkOuterShellSegment, s0]; simp
          · intro qX _ hne; rcases qX with _ | (⟨seg', bX'⟩ | _)
            · dsimp [bdlGXQ1]; simp
            · by_cases hx : seg'.val.1.val.1 = xv.val.1
              · by_cases hcond : seg'.val.2.1 = Fin.last M ∧ seg'.val.1.val.2 = eZ ∧ seg'.val.2.2 = k ∧ bX' = bZ
                · rcases hcond with ⟨hr', heZ', hk', hbX'⟩
                  exfalso; apply hne
                  have hs_eq : seg'.val.1 = s0 := Subtype.ext (Prod.ext hx heZ')
                  have hseg_eq : seg' = seg0 := Subtype.ext (Prod.ext hs_eq (Prod.ext hr' hk'))
                  rw [hseg_eq, hbX']
                · dsimp [bdlGXQ1]; rw [if_neg hcond, mul_zero]
              · dsimp [bdlDeltaX0]
                have h1 : (Sum.inr (sv, b0) : BDLStepXMX pcode M) ≠ Sum.inr (shellSegStartVertex pcode M seg', bX') := by
                  intro h; injection h with h; injection h with hsv _; exact hx (congr_arg (fun u : ShellVertex pcode M => u.val.1.val.1) hsv).symm
                have h2 : (Sum.inr (sv, b0) : BDLStepXMX pcode M) ≠ Sum.inr (shellSegEndVertex pcode M seg', bX') := by
                  intro h; injection h with h; injection h with hsv _
                  have hx_end : (shellSegEndVertex pcode M seg').val.1.val.1 = seg'.val.1.val.1 := rfl
                  exact hx (hx_end ▸ (congr_arg (fun u : ShellVertex pcode M => u.val.1.val.1) hsv).symm)
                rw [if_neg h1, if_neg h2]; simp
            · dsimp [bdlGXQ1]; simp
          · intro h_abs; exact False.elim (h_abs (Finset.mem_univ _))
        rw [h_qX]; dsimp [bdlDeltaX0, seg0]; rw [shellSegStartVertex_outer, shellSegEndVertex_outer]
        dsimp [bdlGXQ0]; rw [xq0OwnerQ_armStart, xq0OwnerQ_armEnd, add_mul]
        have h_if1 : (if (Sum.inr (sv, b0) : BDLStepXMX pcode M) =
              Sum.inr (mkOuterShellVertex pcode M (bxStartLink pcode M s0 k), bZ) then (1 : ZMod 2) else 0) *
              pcode.checkX xv.val.1 eZ.val.1 =
            (if sv.val.2 = Fin.last M ∧ sv.val.1.val.2 = projXq0ToBoundaryX0 pcode M (armStart pcode M eZ k) ∧ b0 = bZ then pcode.checkX xv.val.1 eZ.val.1 else 0) := by
          by_cases hc : sv.val.2 = Fin.last M ∧ sv.val.1.val.2 = projXq0ToBoundaryX0 pcode M (armStart pcode M eZ k) ∧ b0 = bZ
          · rcases hc with ⟨hr0, hv0, hb0⟩
            have hsv_eq : sv = mkOuterShellVertex pcode M (bxStartLink pcode M s0 k) :=
              Subtype.ext (Prod.ext (Subtype.ext (Prod.ext rfl hv0)) hr0)
            rw [if_pos (by rw [← hsv_eq, hb0]), if_pos ⟨hr0, hv0, hb0⟩, one_mul]
          · have hne : (Sum.inr (sv, b0) : BDLStepXMX pcode M) ≠
                Sum.inr (mkOuterShellVertex pcode M (bxStartLink pcode M s0 k), bZ) := by
              intro h; apply hc; injection h with h; injection h with hsv hb
              exact ⟨congr_arg (fun u : ShellVertex pcode M => u.val.2) hsv, congr_arg (fun u : ShellVertex pcode M => u.val.1.val.2) hsv, hb⟩
            rw [if_neg hne, if_neg hc, zero_mul]
        have h_if2 : (if (Sum.inr (sv, b0) : BDLStepXMX pcode M) =
              Sum.inr (mkOuterShellVertex pcode M (bxEndLink pcode M s0 k), bZ) then (1 : ZMod 2) else 0) *
              pcode.checkX xv.val.1 eZ.val.1 =
            (if sv.val.2 = Fin.last M ∧ sv.val.1.val.2 = projXq0ToBoundaryX0 pcode M (armEnd pcode M eZ k) ∧ b0 = bZ then pcode.checkX xv.val.1 eZ.val.1 else 0) := by
          by_cases hc : sv.val.2 = Fin.last M ∧ sv.val.1.val.2 = projXq0ToBoundaryX0 pcode M (armEnd pcode M eZ k) ∧ b0 = bZ
          · rcases hc with ⟨hr0, hv0, hb0⟩
            have hsv_eq : sv = mkOuterShellVertex pcode M (bxEndLink pcode M s0 k) :=
              Subtype.ext (Prod.ext (Subtype.ext (Prod.ext rfl hv0)) hr0)
            rw [if_pos (by rw [← hsv_eq, hb0]), if_pos ⟨hr0, hv0, hb0⟩, one_mul]
          · have hne : (Sum.inr (sv, b0) : BDLStepXMX pcode M) ≠
                Sum.inr (mkOuterShellVertex pcode M (bxEndLink pcode M s0 k), bZ) := by
              intro h; apply hc; injection h with h; injection h with hsv hb
              exact ⟨congr_arg (fun u : ShellVertex pcode M => u.val.2) hsv, congr_arg (fun u : ShellVertex pcode M => u.val.1.val.2) hsv, hb⟩
            rw [if_neg hne, if_neg hc, zero_mul]
        rw [h_if1, h_if2]; exact zmod2_add_self _
      · have hx0 : pcode.checkX xv.val.1 eZ.val.1 = 0 := not_not.mp hs
        have h_qX_zero : (∑ qX : BDLCX1 pcode M, bdlDeltaX0 pcode M (Sum.inr (sv, b0)) qX * bdlGXQ1 pcode M (Sum.inl (eZ, k, bZ)) qX) = 0 := by
          apply Finset.sum_eq_zero; intro qX _; rcases qX with _ | (⟨seg', bX'⟩ | _)
          · dsimp [bdlGXQ1]; simp
          · by_cases hx : seg'.val.1.val.1 = xv.val.1
            · dsimp [bdlGXQ1]; rw [hx, hx0]; simp
            · dsimp [bdlDeltaX0]
              have h1 : (Sum.inr (sv, b0) : BDLStepXMX pcode M) ≠ Sum.inr (shellSegStartVertex pcode M seg', bX') := by
                intro h; injection h with h; injection h with hsv _; exact hx (congr_arg (fun u : ShellVertex pcode M => u.val.1.val.1) hsv).symm
              have h2 : (Sum.inr (sv, b0) : BDLStepXMX pcode M) ≠ Sum.inr (shellSegEndVertex pcode M seg', bX') := by
                intro h; injection h with h; injection h with hsv _
                have hx_end : (shellSegEndVertex pcode M seg').val.1.val.1 = seg'.val.1.val.1 := rfl
                exact hx (hx_end ▸ (congr_arg (fun u : ShellVertex pcode M => u.val.1.val.1) hsv).symm)
              rw [if_neg h1, if_neg h2]; simp
          · dsimp [bdlGXQ1]; simp
        rw [h_qX_zero]; dsimp [bdlGXQ0]; rw [xq0OwnerQ_armStart, xq0OwnerQ_armEnd]
        have hx0' : pcode.checkX sv.val.1.val.1 eZ.val.1 = 0 := hx0
        simp [hx0']
  · have h_qQ : (∑ qQ : BDLCQ1 pcode M, bdlGXQ0 pcode M mX qQ * bdlDeltaQ1 pcode M (Sum.inr (eZ, v)) qQ) =
        bdlGXQ0 pcode M mX (Sum.inr (Sum.inr eZ), 0) + bdlGXQ0 pcode M mX (Sum.inr (Sum.inr eZ), v.succ) := by
      have h_exp : ∀ qQ : BDLCQ1 pcode M, bdlGXQ0 pcode M mX qQ * bdlDeltaQ1 pcode M (Sum.inr (eZ, v)) qQ =
          bdlGXQ0 pcode M mX qQ * (if qQ = (Sum.inr (Sum.inr eZ), 0) then 1 else 0) +
          bdlGXQ0 pcode M mX qQ * (if qQ = (Sum.inr (Sum.inr eZ), v.succ) then 1 else 0) := fun qQ => by dsimp [bdlDeltaQ1]; ring
      simp_rw [h_exp, Finset.sum_add_distrib, sum_gXQ0_mul_indicator]
    rw [h_qQ]
    rcases mX with ⟨x0, b0⟩ | ⟨sv, b0⟩
    · have h_qX_zero : (∑ qX : BDLCX1 pcode M, bdlDeltaX0 pcode M (Sum.inl (x0, b0)) qX * bdlGXQ1 pcode M (Sum.inr (eZ, v)) qX) = 0 := by
        apply Finset.sum_eq_zero; intro qX _; rcases qX with _ | (_ | ⟨_, _⟩) <;> dsimp [bdlDeltaX0, bdlGXQ1] <;> simp
      rw [h_qX_zero]; dsimp [bdlGXQ0]; simp
    · let xv := sv.val.1
      by_cases hs : pcode.checkX xv.val.1 eZ.val.1 ≠ 0
      · have hv_link : InLinkOfX pcode M xv.val.1 (Sum.inr (Sum.inr eZ.val.2)) := ⟨eZ.val.1, hs, eZ.property⟩
        let xv0 : BoundaryX0Link pcode M := ⟨(xv.val.1, Sum.inr (Sum.inr eZ.val.2)), hv_link⟩
        have h_qX : (∑ qX : BDLCX1 pcode M, bdlDeltaX0 pcode M (Sum.inr (sv, b0)) qX * bdlGXQ1 pcode M (Sum.inr (eZ, v)) qX) =
            bdlDeltaX0 pcode M (Sum.inr (sv, b0)) (Sum.inr (Sum.inr (xv0, v))) * pcode.checkX xv.val.1 eZ.val.1 := by
          rw [Finset.sum_eq_single (Sum.inr (Sum.inr (xv0, v)))]
          · dsimp [bdlGXQ1, xv0]; simp
          · intro qX _ hne; rcases qX with _ | (_ | ⟨xv', vX'⟩)
            · dsimp [bdlGXQ1]; simp
            · dsimp [bdlGXQ1]; simp
            · dsimp [bdlGXQ1]
              by_cases hv : xv'.val.2 = Sum.inr (Sum.inr eZ.val.2) ∧ vX' = v
              · rcases hv with ⟨hv1, hv2⟩
                by_cases hx : xv'.val.1 = xv.val.1
                · exfalso; apply hne
                  have hxv'_eq : xv' = xv0 := Subtype.ext (Prod.ext hx hv1)
                  rw [hxv'_eq, hv2]
                · dsimp [bdlDeltaX0]
                  have h1 : (Sum.inr (sv, b0) : BDLStepXMX pcode M) ≠ Sum.inr (mkOuterShellVertex pcode M xv', 0) := by
                    intro h; injection h with h; injection h with hsv _; exact hx (congr_arg (fun u : ShellVertex pcode M => u.val.1.val.1) hsv).symm
                  have h2 : (Sum.inr (sv, b0) : BDLStepXMX pcode M) ≠ Sum.inr (mkOuterShellVertex pcode M xv', vX'.succ) := by
                    intro h; injection h with h; injection h with hsv _; exact hx (congr_arg (fun u : ShellVertex pcode M => u.val.1.val.1) hsv).symm
                  rw [if_neg h1, if_neg h2]; simp
              · rw [if_neg hv, mul_zero]
          · intro h_abs; exact False.elim (h_abs (Finset.mem_univ _))
        rw [h_qX]; dsimp [bdlDeltaX0, bdlGXQ0, projXq0ToBoundaryX0, xq0OwnerQ]; rw [add_mul]
        have h_if0 : (if (Sum.inr (sv, b0) : BDLStepXMX pcode M) = Sum.inr (mkOuterShellVertex pcode M xv0, 0) then (1 : ZMod 2) else 0) * pcode.checkX xv.val.1 eZ.val.1 =
            (if sv.val.2 = Fin.last M ∧ sv.val.1.val.2 = Sum.inr (Sum.inr eZ.val.2) ∧ b0 = 0 then pcode.checkX xv.val.1 eZ.val.1 else 0) := by
          by_cases hc : sv.val.2 = Fin.last M ∧ sv.val.1.val.2 = Sum.inr (Sum.inr eZ.val.2) ∧ b0 = 0
          · rcases hc with ⟨hr0, hv0, hb0⟩
            have hsv_eq : sv = mkOuterShellVertex pcode M xv0 := Subtype.ext (Prod.ext (Subtype.ext (Prod.ext rfl hv0)) hr0)
            rw [if_pos (by rw [← hsv_eq, hb0]), if_pos ⟨hr0, hv0, hb0⟩, one_mul]
          · have hne : (Sum.inr (sv, b0) : BDLStepXMX pcode M) ≠ Sum.inr (mkOuterShellVertex pcode M xv0, 0) := by
              intro h; apply hc; injection h with h; injection h with hsv hb
              exact ⟨congr_arg (fun u : ShellVertex pcode M => u.val.2) hsv, congr_arg (fun u : ShellVertex pcode M => u.val.1.val.2) hsv, hb⟩
            rw [if_neg hne, if_neg hc, zero_mul]
        have h_if1 : (if (Sum.inr (sv, b0) : BDLStepXMX pcode M) = Sum.inr (mkOuterShellVertex pcode M xv0, v.succ) then (1 : ZMod 2) else 0) * pcode.checkX xv.val.1 eZ.val.1 =
            (if sv.val.2 = Fin.last M ∧ sv.val.1.val.2 = Sum.inr (Sum.inr eZ.val.2) ∧ b0 = v.succ then pcode.checkX xv.val.1 eZ.val.1 else 0) := by
          by_cases hc : sv.val.2 = Fin.last M ∧ sv.val.1.val.2 = Sum.inr (Sum.inr eZ.val.2) ∧ b0 = v.succ
          · rcases hc with ⟨hr0, hv0, hb0⟩
            have hsv_eq : sv = mkOuterShellVertex pcode M xv0 := Subtype.ext (Prod.ext (Subtype.ext (Prod.ext rfl hv0)) hr0)
            rw [if_pos (by rw [← hsv_eq, hb0]), if_pos ⟨hr0, hv0, hb0⟩, one_mul]
          · have hne : (Sum.inr (sv, b0) : BDLStepXMX pcode M) ≠ Sum.inr (mkOuterShellVertex pcode M xv0, v.succ) := by
              intro h; apply hc; injection h with h; injection h with hsv hb
              exact ⟨congr_arg (fun u : ShellVertex pcode M => u.val.2) hsv, congr_arg (fun u : ShellVertex pcode M => u.val.1.val.2) hsv, hb⟩
            rw [if_neg hne, if_neg hc, zero_mul]
        rw [h_if0, h_if1]; exact zmod2_add_self _
      · have hx0 : pcode.checkX xv.val.1 eZ.val.1 = 0 := not_not.mp hs
        have h_qX_zero : (∑ qX : BDLCX1 pcode M, bdlDeltaX0 pcode M (Sum.inr (sv, b0)) qX * bdlGXQ1 pcode M (Sum.inr (eZ, v)) qX) = 0 := by
          apply Finset.sum_eq_zero; intro qX _; rcases qX with _ | (_ | ⟨xv', vX'⟩)
          · dsimp [bdlGXQ1]; simp
          · dsimp [bdlGXQ1]; simp
          · by_cases hx : xv'.val.1 = xv.val.1
            · dsimp [bdlGXQ1]; rw [hx, hx0]; simp
            · dsimp [bdlDeltaX0]
              have h1 : (Sum.inr (sv, b0) : BDLStepXMX pcode M) ≠ Sum.inr (mkOuterShellVertex pcode M xv', 0) := by
                intro h; injection h with h; injection h with hsv _; exact hx (congr_arg (fun u : ShellVertex pcode M => u.val.1.val.1) hsv).symm
              have h2 : (Sum.inr (sv, b0) : BDLStepXMX pcode M) ≠ Sum.inr (mkOuterShellVertex pcode M xv', vX'.succ) := by
                intro h; injection h with h; injection h with hsv _; exact hx (congr_arg (fun u : ShellVertex pcode M => u.val.1.val.1) hsv).symm
              rw [if_neg h1, if_neg h2]; simp
        rw [h_qX_zero]; dsimp [bdlGXQ0, xq0OwnerQ]
        have hx0' : pcode.checkX sv.val.1.val.1 eZ.val.1 = 0 := hx0
        simp [hx0']

/-- Bottom-row exactness $g_{QZ}^1 \circ g_{XQ}^0 = 0$. -/
lemma bdlGQZ1_comp_bdlGXQ0 {Q M_Z M_X : Type}
    [Fintype Q] [DecidableEq Q] [Fintype M_Z] [DecidableEq M_Z] [Fintype M_X] [DecidableEq M_X]
    (pcode : CSSCode3D Q M_Z M_X) (M : ℕ) (mX : BDLStepXMX pcode M) (mZZ : BDLCZ2 M_Z) :
    (∑ qQ : BDLCQ1 pcode M, bdlGXQ0 pcode M mX qQ * bdlGQZ1 pcode M mZZ qQ) = 0 := by
  rcases mX with ⟨x0, b0⟩ | ⟨sv, b0⟩
  · exact Finset.sum_eq_zero (fun _ _ => by dsimp [bdlGXQ0]; simp)
  · rw [Fintype.sum_prod_type, Finset.sum_comm, Finset.sum_eq_single mZZ.2]
    · rw [Fintype.sum_sum_type, Fintype.sum_sum_type]
      have h_inl : (∑ x : Q, bdlGXQ0 pcode M (Sum.inr (sv, b0)) (Sum.inl x, mZZ.2) * bdlGQZ1 pcode M mZZ (Sum.inl x, mZZ.2)) = 0 :=
        Finset.sum_eq_zero (fun _ _ => by dsimp [bdlGQZ1]; simp)
      have h_mid : (∑ x : ActiveZ pcode × Fin M, bdlGXQ0 pcode M (Sum.inr (sv, b0)) (Sum.inr (Sum.inl x), mZZ.2) * bdlGQZ1 pcode M mZZ (Sum.inr (Sum.inl x), mZZ.2)) = 0 :=
        Finset.sum_eq_zero (fun _ _ => by dsimp [bdlGQZ1]; simp)
      rw [h_inl, zero_add, h_mid, zero_add]
      by_cases hc : sv.val.2 = Fin.last M ∧ sv.val.1.val.2 = Sum.inr (Sum.inr mZZ.1) ∧ b0 = mZZ.2
      · rcases hc with ⟨hr0, hv0, hb0⟩
        have h_term : ∀ eZ : ActiveZ pcode,
            bdlGXQ0 pcode M (Sum.inr (sv, b0)) (Sum.inr (Sum.inr eZ), mZZ.2) * bdlGQZ1 pcode M mZZ (Sum.inr (Sum.inr eZ), mZZ.2) =
            if eZ.val.2 = mZZ.1 then pcode.checkX sv.val.1.val.1 eZ.val.1 else 0 := by
          intro eZ; unfold bdlGXQ0 bdlGQZ1 projXq0ToBoundaryX0 xq0OwnerQ; simp only
          by_cases heZ : eZ.val.2 = mZZ.1 <;> [ (rw [heZ, if_pos ⟨hr0, hv0, hb0⟩]; simp); simp [heZ]]
        simp_rw [h_term]; rw [sum_activeZ_eq pcode mZZ.1 (fun q => pcode.checkX sv.val.1.val.1 q)]
        exact pcode.commutativity sv.val.1.val.1 mZZ.1
      · apply Finset.sum_eq_zero; intro eZ _; unfold bdlGXQ0 bdlGQZ1 projXq0ToBoundaryX0 xq0OwnerQ; simp only
        by_cases heZ : eZ.val.2 = mZZ.1 <;> [ (rw [heZ, if_neg hc, zero_mul]); simp [heZ]]
    · intro b _ hne; apply Finset.sum_eq_zero; intro v _; rcases v with _ | (_ | _) <;> dsimp [bdlGQZ1] <;> simp [hne]
    · intro h_abs; exact False.elim (h_abs (Finset.mem_univ _))

/-- Full CSS commutativity $\delta^1 \circ \delta^0 = 0$ ($H_X H_Z^T = 0$) for `bdlCylinderStepX`. -/
theorem bdlStepX_commutativity {Q M_Z M_X : Type}
    [Fintype Q] [DecidableEq Q] [Fintype M_Z] [DecidableEq M_Z] [Fintype M_X] [DecidableEq M_X]
    (pcode : CSSCode3D Q M_Z M_X) (M : ℕ) (mX : BDLStepXMX pcode M) (mZ : BDLStepXMZ pcode M) :
    (∑ q : BDLStepXQ pcode M, bdlStepXCheckX pcode M mX q * bdlStepXCheckZ pcode M mZ q) = 0 := by
  rw [Fintype.sum_sum_type]
  rcases mZ with mZX | (mZQ | mZZ)
  · have h_inr : (∑ qQ : BDLCQ1 pcode M,
        bdlStepXCheckX pcode M mX (Sum.inr qQ) * bdlStepXCheckZ pcode M (Sum.inl mZX) (Sum.inr qQ)) = 0 :=
      Finset.sum_eq_zero (fun _ _ => rfl)
    rw [h_inr, add_zero]; exact bdlDeltaX1_comp_bdlDeltaX0 pcode M mX mZX
  · exact bdlGXQ1_deltaX0_add_deltaQ1_gXQ0 pcode M mX mZQ
  · have h_inl : (∑ qX : BDLCX1 pcode M,
        bdlStepXCheckX pcode M mX (Sum.inl qX) * bdlStepXCheckZ pcode M (Sum.inr (Sum.inr mZZ)) (Sum.inl qX)) = 0 :=
      Finset.sum_eq_zero (fun _ _ => rfl)
    rw [h_inl, zero_add]; exact bdlGQZ1_comp_bdlGXQ0 pcode M mX mZZ

/-- Coupled 3-layer cylinder replacement complex $\mathcal{C}_{(i+1)} = C_X^\bullet \oplus C_Q^\bullet \oplus C_Z^\bullet$. -/
noncomputable def bdlCylinderStepX {Q M_Z M_X : Type}
    [Fintype Q] [DecidableEq Q] [Fintype M_Z] [DecidableEq M_Z] [Fintype M_X] [DecidableEq M_X]
    (pcode : CSSCode3D Q M_Z M_X) (M : ℕ) :
    CSSCode3D (BDLStepXQ pcode M) (BDLStepXMZ pcode M) (BDLStepXMX pcode M) where
  posQ := bdlStepXPosQ pcode M
  posZ := bdlStepXPosZ pcode M
  posX := bdlStepXPosX pcode M
  checkX := bdlStepXCheckX pcode M
  checkZ := bdlStepXCheckZ pcode M
  commutativity := bdlStepX_commutativity pcode M

/-- Full BDL replacement operator $R_X$ composing Step 1 (`bdlPerturbStep`) and Step 2 (`bdlCylinderStepX`). -/
noncomputable def bdlReplaceStepX {Q M_Z M_X : Type}
    [Fintype Q] [DecidableEq Q] [Fintype M_Z] [DecidableEq M_Z] [Fintype M_X] [DecidableEq M_X]
    (code : CSSCode3D Q M_Z M_X) (lam M : ℕ)
    (cQ : Q → Point3D) (cZ : M_Z → Point3D) (cX : M_X → Point3D) :
    CSSCode3D
      (BDLStepXQ (bdlPerturbStep code lam cQ cZ cX) M)
      (BDLStepXMZ (bdlPerturbStep code lam cQ cZ cX) M)
      (BDLStepXMX (bdlPerturbStep code lam cQ cZ cX) M) :=
  bdlCylinderStepX (bdlPerturbStep code lam cQ cZ cX) M

/-- Bundled replacement step $R_X$ (`bdlStepX`). -/
noncomputable def bdlStepX (B : BundledCSSCode3D) : BundledCSSCode3D where
  Q := BDLStepXQ (bdlPerturbStep B.code bdlLambda (bdlLLLPerturbation B).1 (bdlLLLPerturbation B).2.1 (bdlLLLPerturbation B).2.2) bdlSubdivPred
  M_Z := BDLStepXMZ (bdlPerturbStep B.code bdlLambda (bdlLLLPerturbation B).1 (bdlLLLPerturbation B).2.1 (bdlLLLPerturbation B).2.2) bdlSubdivPred
  M_X := BDLStepXMX (bdlPerturbStep B.code bdlLambda (bdlLLLPerturbation B).1 (bdlLLLPerturbation B).2.1 (bdlLLLPerturbation B).2.2) bdlSubdivPred
  code := bdlReplaceStepX B.code bdlLambda bdlSubdivPred (bdlLLLPerturbation B).1 (bdlLLLPerturbation B).2.1 (bdlLLLPerturbation B).2.2

/-- Dual bundled replacement step $R_Z = \mathrm{dual} \circ R_X \circ \mathrm{dual}$ (`bdlStepZ`). -/
noncomputable def bdlStepZ (B : BundledCSSCode3D) : BundledCSSCode3D :=
  dualBundled (bdlStepX (dualBundled B))

/-- Level-$k$ inductively-defined 3-layer BDL code bundle $\mathcal{C}_{2(k+1)} = (R_Z \circ R_X)^{k+1}(\mathcal{C}_0)$. -/
noncomputable def bdlWeldedBundled (k : ℕ) : BundledCSSCode3D :=
  (bdlStepZ ∘ bdlStepX)^[k + 1] bdlSurfaceSeedBundled

abbrev BDLWeldedQubit (k : ℕ) : Type := (bdlWeldedBundled k).Q
abbrev BDLWeldedCheckZ (k : ℕ) : Type := (bdlWeldedBundled k).M_Z
abbrev BDLWeldedCheckX (k : ℕ) : Type := (bdlWeldedBundled k).M_X

/-- Level-$k$ 3-layer welded BDL CSS code `bdlWeldedCode k`. -/
noncomputable def bdlWeldedCode (k : ℕ) :
    CSSCode3D (BDLWeldedQubit k) (BDLWeldedCheckZ k) (BDLWeldedCheckX k) :=
  (bdlWeldedBundled k).code
