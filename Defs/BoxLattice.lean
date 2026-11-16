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

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Fin.Basic
import Mathlib.Tactic

/-!
# Open-Box Lattice Geometry, Metric Balls, and Cube Decompositions

Defines the D-dimensional open-box lattice `BoxD D L` (`Box3D L` in three dimensions), the l_infinity metric `boxDist`, metric balls `boxBall`, integer-anchored boxes `boxCube`, and dilated enclosing collars `enclosingBoxCube` with `linearExpansionRadius`, together with the collection `boxCubes` of scale-r subcubes.

## References

* Part I, Section 3.1 (`subsec:rca-trinity`), Definition 3.1 (`def:rca`), Section 5.4 (`subsec:safe-decoded-observables`), Definition 5.6 (`def:safe-decoded-observables`)
* Part I, Section 6.1 (`subsec:dsuper-banach`), Definition 6.1 (`def:banach-quasilocal`)
* Part II, Section 2 (`subsec:setup`), Definition 2.1 (`def:bdl-lattice`), Definition 2.2 (`def:RCA`)
-/

noncomputable section

open scoped Classical BigOperators

/-!
## 1. Open $D$-Dimensional Box Lattice `BoxD D L` and $\ell_\infty$ Metric
-/

/-- The $D$-dimensional open discrete box lattice $\Lambda_L = \{0, 1, \dots, L-1\}^D$,
    represented as `Fin D → Fin L` with open (non-periodic) boundary conditions. -/
abbrev BoxD (D L : ℕ) : Type := Fin D → Fin L

/-- The $3$-dimensional open discrete box lattice $\Lambda_L = \{0, 1, \dots, L-1\}^3$. -/
abbrev Box3D (L : ℕ) : Type := BoxD 3 L

/-- Non-periodic 1D coordinate distance $|a - b| \in \mathbb{N}$ on `Fin L`. -/
def coordDist {L : ℕ} (a b : Fin L) : ℕ :=
  ((a.val : ℤ) - (b.val : ℤ)).natAbs

lemma coordDist_self {L : ℕ} (a : Fin L) : coordDist a a = 0 := by
  simp [coordDist]

lemma coordDist_comm {L : ℕ} (a b : Fin L) : coordDist a b = coordDist b a := by
  dsimp [coordDist]
  omega

lemma coordDist_triangle {L : ℕ} (a b c : Fin L) :
    coordDist a c ≤ coordDist a b + coordDist b c := by
  dsimp [coordDist]
  omega

/-- Non-periodic $\ell_\infty$ distance $\mathrm{dist}_\infty(x, y) = \max_{i \in \mathrm{Fin}\ D} |x_i - y_i|$
    on the open box `BoxD D L`. -/
def boxDist {D L : ℕ} (x y : BoxD D L) : ℕ :=
  Finset.univ.sup (fun i : Fin D => coordDist (x i) (y i))

/-- Minimum $\ell_\infty$ distance between two lattice regions $A, B \subseteq \mathrm{BoxD}\ D\ L$
    (returns $0$ if $A$ or $B$ is empty). -/
def regionDist {D L : ℕ} (A B : Finset (BoxD D L)) : ℕ :=
  if h : A.Nonempty ∧ B.Nonempty then
    (A ×ˢ B).inf' (h.1.product h.2) (fun p => boxDist p.1 p.2)
  else 0

/-!
## 2. Metric Balls and Collars on `BoxD D L`
-/

/-- Discrete $\ell_\infty$-ball $B(x, r) = \{y \in \Lambda_L : \mathrm{boxDist}(x, y) \le r\}$ of radius $r$ around $x$. -/
def boxBall {D L : ℕ} (x : BoxD D L) (r : ℕ) : Finset (BoxD D L) :=
  Finset.univ.filter (fun y => boxDist x y ≤ r)

/-!
## 3. Non-Wrapping Open-Box Integer Translations
-/

/-- Non-wrapping open-box containment condition $v + \delta \in \{0, 1, \dots, L-1\}^D$ for a vertex
    $v \in \mathrm{BoxD}\ D\ L$ and an integer displacement vector $\delta \in \mathbb{Z}^D$. -/
def InOpenBoxD {D L : ℕ} (v : BoxD D L) (δ : Fin D → ℤ) : Prop :=
  ∀ μ : Fin D, 0 ≤ ((v μ).val : ℤ) + δ μ ∧ ((v μ).val : ℤ) + δ μ < (L : ℤ)

/-- Non-wrapping 3D open-box containment condition $v + \delta \in \{0, 1, \dots, L-1\}^3$. -/
abbrev InOpenBox {L : ℕ} (v : Box3D L) (δ : Fin 3 → ℤ) : Prop :=
  InOpenBoxD v δ

/-- Non-wrapping open-box integer translation $v + \delta$ on `BoxD D L` (clamped at $v_\mu$ if out of bounds). -/
def shiftOpenBoxD {D L : ℕ} (v : BoxD D L) (δ : Fin D → ℤ) : BoxD D L :=
  fun μ =>
    if h : 0 ≤ ((v μ).val : ℤ) + δ μ ∧ ((v μ).val : ℤ) + δ μ < (L : ℤ) then
      ⟨(((v μ).val : ℤ) + δ μ).toNat, by omega⟩
    else
      v μ

/-- Non-wrapping 3D open-box integer translation $v + \delta$ on `Box3D L`. -/
abbrev shiftOpenBox {L : ℕ} (v : Box3D L) (δ : Fin 3 → ℤ) : Box3D L :=
  shiftOpenBoxD v δ

/-!
## 4. Open-Box Cubes and Enclosing Collars
-/

/-- Open-box cube $\mathrm{boxCube}(x_0, r) = \{x \in \Lambda_L : \forall i,\ (x_0)_i \le x_i < (x_0)_i + r\}$
    of linear side length $r$ anchored at $x_0 \in \mathrm{BoxD}\ D\ L$ (clamped to the open box). -/
def boxCube {D L : ℕ} (x0 : BoxD D L) (r : ℕ) : Finset (BoxD D L) :=
  Finset.univ.filter (fun x : BoxD D L =>
    ∀ i : Fin D, (x0 i).val ≤ (x i).val ∧ (x i).val < (x0 i).val + r)

/-- The family $\mathcal{S}(r)$ of all open-box cubes of linear size $r$ on `BoxD D L`. -/
def boxCubes (D L r : ℕ) : Finset (Finset (BoxD D L)) :=
  Finset.univ.image (fun x0 : BoxD D L => boxCube x0 r)

/-- Concentric enclosing open-box cube $B(A, R)$ of scale $R$ around $A = \mathrm{boxCube}(x_0, r)$,
    anchored at $\max(0, x_{0,i} - \lfloor(R - r)/2\rfloor)$ and clamped to `BoxD D L`. -/
def enclosingBoxCube {D L : ℕ} (x0 : BoxD D L) (r R : ℕ) : Finset (BoxD D L) :=
  boxCube (fun i : Fin D => ⟨(x0 i).val - (R - r) / 2, Nat.sub_lt_of_lt (x0 i).isLt⟩) R

/-- Linear neighborhood expansion radius $R(r) = \lceil C \cdot r \rceil$ as a natural number scale. -/
def linearExpansionRadius (C : ℝ) (r : ℕ) : ℕ :=
  Nat.ceil (C * (r : ℝ))

/-- Region $B$ is a $1$-collar of $A$ if $A \subseteq B$ and every elementary $2$-cube $K \in \mathcal{S}(2)$
    that intersects $A$ is contained in $B$. -/
def IsOneCollarOf {D L : ℕ} (A B : Finset (BoxD D L)) : Prop :=
  A ⊆ B ∧ ∀ K ∈ boxCubes D L 2, ¬Disjoint K A → K ⊆ B
