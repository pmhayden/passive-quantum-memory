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

import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Finset.Card
import Mathlib.Tactic

/-!
# F_2 Chain Complexes, 3D CSS Codes, and Symplectic Dual Logical Pairs

Defines three-term F_2 chain complexes (`F2ChainComplex`), Euclidean 3D CSS codes (`CSSCode3D`) with Euclidean metric balls (`ball3D`) and X/Z dual code construction (`dualCode`), syndrome and stabilizer-generator maps (`syndrome`, `checkGen`), and symplectic dual logical operator pairs (`DualLogicalPair`, `HasDualLogicalPair`) together with elementary `ZMod 2` cancellation identities.

## References

* Part I, Section 2.1 (`subsec:css-complexes`), Definition 2.1 (`def:3d-css-complex`)
* Part I, Section 5.2 (`subsec:cluster-decoder`), Definition 5.2 (`def:multiscale-cluster-decoder`), Section 5.3 (`subsec:walsh-fourier-peierls`), Theorem 5.5 (`thm:walsh-fourier-peierls`)
-/

noncomputable section

open scoped Classical BigOperators

/-! ## 1. Elementary `ZMod 2` Algebraic Identities -/

/-- Every element of `ZMod 2` is either `0` or `1`. -/
lemma zmod2_eq_zero_or_one (x : ZMod 2) : x = 0 ∨ x = 1 := by
  revert x; decide

/-- Characteristic-2 cancellation `a + a = 0` in `ZMod 2`. -/
@[simp] lemma zmod2_add_self (a : ZMod 2) : a + a = 0 := by
  revert a; decide

/-- Conditional indicator multiplication in `ZMod 2`. -/
lemma zmod2_if_eq_zero_mul (a x : ZMod 2) :
    (if x = 0 then 0 else a) = a * x := by
  revert a x; decide

/-- Nonzero elements of `ZMod 2` equal `1`. -/
lemma zmod2_ne_zero_iff_eq_one (a : ZMod 2) (h : a ≠ 0) : a = 1 := by
  rcases zmod2_eq_zero_or_one a with rfl | rfl
  · exact False.elim (h rfl)
  · rfl

/-- Three-term boundary cancellation `(a + b) + (a + c) + (b + c) = 0` over `ZMod 2`. -/
lemma zmod2_cancel3 (a b c : ZMod 2) : (a + b) + (a + c) + (b + c) = 0 := by
  revert a b c; decide

/-- Four-term square boundary cancellation `(a + b) + (c + d) + (a + c) + (b + d) = 0` over `ZMod 2`. -/
lemma zmod2_cancel4 (a b c d : ZMod 2) : (a + b) + (c + d) + (a + c) + (b + d) = 0 := by
  revert a b c d; decide

/-- Middle-term telescope `(a + u) + (u + c) = a + c` over `ZMod 2`. -/
lemma zmod2_add_mid_cancel (a u c : ZMod 2) : (a + u) + (u + c) = a + c := by
  revert a u c; decide

/-! ## 2. 3-Term $\mathbb{F}_2$ Chain Complexes and Abstract CSS Codes -/

/-- A 3-term $\mathbb{F}_2$ chain/cochain complex $C_2 \xrightarrow{\partial_2} C_1 \xrightarrow{\partial_1} C_0$
    over finite basis types `M_Z`, `Q`, `M_X`, i.e., a Calderbank–Shor–Steane (CSS) stabilizer code. -/
structure F2ChainComplex (Q M_Z M_X : Type)
    [Fintype Q] [DecidableEq Q]
    [Fintype M_Z] [DecidableEq M_Z]
    [Fintype M_X] [DecidableEq M_X] where
  checkX : M_X → Q → ZMod 2
  checkZ : M_Z → Q → ZMod 2
  commutativity : ∀ (mX : M_X) (mZ : M_Z), (∑ q : Q, checkX mX q * checkZ mZ q) = 0

/-- Dual $\mathbb{F}_2$ chain complex (dual CSS code) swapping $X$-checks and $Z$-checks. -/
def dualF2ChainComplex {Q M_Z M_X : Type}
    [Fintype Q] [DecidableEq Q] [Fintype M_Z] [DecidableEq M_Z] [Fintype M_X] [DecidableEq M_X]
    (C : F2ChainComplex Q M_Z M_X) : F2ChainComplex Q M_X M_Z where
  checkX := C.checkZ
  checkZ := C.checkX
  commutativity mZ mX := by
    have h := C.commutativity mX mZ
    simpa only [mul_comm] using h

/-- Boundary / syndrome map $\partial_1 = H_X : (Q \to \mathbb{Z}_2) \to_+ (M_X \to \mathbb{Z}_2)$. -/
def f2Syndrome {Q M_Z M_X : Type}
    [Fintype Q] [DecidableEq Q] [Fintype M_Z] [DecidableEq M_Z] [Fintype M_X] [DecidableEq M_X]
    (C : F2ChainComplex Q M_Z M_X) : (Q → ZMod 2) →+ (M_X → ZMod 2) where
  toFun g mX := ∑ q : Q, C.checkX mX q * g q
  map_zero' := by ext mX; simp
  map_add' g1 g2 := by ext mX; simp [mul_add, Finset.sum_add_distrib]

/-- Stabilizer generator map $\partial_2 = H_Z^T : (M_Z \to \mathbb{Z}_2) \to_+ (Q \to \mathbb{Z}_2)$. -/
def f2CheckGen {Q M_Z M_X : Type}
    [Fintype Q] [DecidableEq Q] [Fintype M_Z] [DecidableEq M_Z] [Fintype M_X] [DecidableEq M_X]
    (C : F2ChainComplex Q M_Z M_X) : (M_Z → ZMod 2) →+ (Q → ZMod 2) where
  toFun c2 q := ∑ mZ : M_Z, C.checkZ mZ q * c2 mZ
  map_zero' := by ext q; simp
  map_add' c1 c2 := by ext q; simp [mul_add, Finset.sum_add_distrib]

/-- Exact chain complex property $\partial_1 \circ \partial_2 = 0$: every $Z$-stabilizer generator
    has vanishing $X$-syndrome. -/
theorem f2Syndrome_f2CheckGen_eq_zero {Q M_Z M_X : Type}
    [Fintype Q] [DecidableEq Q] [Fintype M_Z] [DecidableEq M_Z] [Fintype M_X] [DecidableEq M_X]
    (C : F2ChainComplex Q M_Z M_X) (c2 : M_Z → ZMod 2) :
    f2Syndrome C (f2CheckGen C c2) = 0 := by
  ext mX
  change (∑ q : Q, C.checkX mX q * (∑ mZ : M_Z, C.checkZ mZ q * c2 mZ)) = 0
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  have h_inner : ∀ mZ : M_Z,
      (∑ q : Q, C.checkX mX q * (C.checkZ mZ q * c2 mZ)) =
        (∑ q : Q, C.checkX mX q * C.checkZ mZ q) * c2 mZ := by
    intro mZ
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl (fun q _ => by ring)
  simp_rw [h_inner, C.commutativity mX, zero_mul, Finset.sum_const_zero]

/-! ## 3. 3D Geometrically Embedded CSS Codes (`CSSCode3D`) -/

/-- A point in 3D space $\mathbb{R}^3$. -/
abbrev Point3D : Type := Fin 3 → ℝ

/-- Squared Euclidean distance $\|x - y\|_2^2$ in $\mathbb{R}^3$. -/
def distSq3D (x y : Point3D) : ℝ :=
  (x 0 - y 0) ^ 2 + (x 1 - y 1) ^ 2 + (x 2 - y 2) ^ 2

/-- Closed Euclidean ball $B(x_0, r) = \{x \in \mathbb{R}^3 \mid \|x - x_0\|_2^2 \le r^2\}$. -/
def ball3D (x0 : Point3D) (r : ℝ) : Set Point3D :=
  {x : Point3D | distSq3D x x0 ≤ r ^ 2}

/-- A 3D CSS stabilizer code equipped with spatial positions for physical qubits and checks. -/
structure CSSCode3D (Q M_Z M_X : Type)
    [Fintype Q] [DecidableEq Q]
    [Fintype M_Z] [DecidableEq M_Z]
    [Fintype M_X] [DecidableEq M_X] extends F2ChainComplex Q M_Z M_X where
  posQ : Q → Point3D
  posZ : M_Z → Point3D
  posX : M_X → Point3D

/-- Dual 3D CSS code obtained by swapping $X$-checks and $Z$-checks. -/
def dualCode {Q M_Z M_X : Type}
    [Fintype Q] [DecidableEq Q] [Fintype M_Z] [DecidableEq M_Z] [Fintype M_X] [DecidableEq M_X]
    (code : CSSCode3D Q M_Z M_X) : CSSCode3D Q M_X M_Z where
  toF2ChainComplex := dualF2ChainComplex code.toF2ChainComplex
  posQ := code.posQ
  posZ := code.posX
  posX := code.posZ

/-- Syndrome homomorphism $\partial_1 = H_X$ of `code : CSSCode3D Q M_Z M_X`. -/
def syndrome {Q M_Z M_X : Type}
    [Fintype Q] [DecidableEq Q] [Fintype M_Z] [DecidableEq M_Z] [Fintype M_X] [DecidableEq M_X]
    (code : CSSCode3D Q M_Z M_X) : (Q → ZMod 2) →+ (M_X → ZMod 2) :=
  f2Syndrome code.toF2ChainComplex

/-- Stabilizer generator homomorphism $\partial_2 = H_Z^T$ of `code : CSSCode3D Q M_Z M_X`. -/
def checkGen {Q M_Z M_X : Type}
    [Fintype Q] [DecidableEq Q] [Fintype M_Z] [DecidableEq M_Z] [Fintype M_X] [DecidableEq M_X]
    (code : CSSCode3D Q M_Z M_X) : (M_Z → ZMod 2) →+ (Q → ZMod 2) :=
  f2CheckGen code.toF2ChainComplex

/-- Single-qubit indicator 1-chain $e_q : Q \to \mathbb{Z}_2$. -/
def singleQubit {Q : Type} [DecidableEq Q] (q : Q) : Q → ZMod 2 :=
  fun q' => if q' = q then 1 else 0

/-! ## 4. Homology and Dual Logical Pairs -/

/-- Non-trivial first homology $H_1(\mathcal{C}) \neq 0$: existence of a non-trivial logical cycle. -/
def HasLogicalQubit {Q M_Z M_X : Type}
    [Fintype Q] [DecidableEq Q] [Fintype M_Z] [DecidableEq M_Z] [Fintype M_X] [DecidableEq M_X]
    (code : CSSCode3D Q M_Z M_X) : Prop :=
  ∃ g : (Q → ZMod 2), syndrome code g = 0 ∧ (∀ c2 : (M_Z → ZMod 2), checkGen code c2 ≠ g)

/-- Symplectic dual logical pair $(L_Z, L_X)$ with $\langle L_Z, L_X \rangle = 1 \pmod 2$. -/
structure DualLogicalPair {Q M_Z M_X : Type}
    [Fintype Q] [DecidableEq Q] [Fintype M_Z] [DecidableEq M_Z] [Fintype M_X] [DecidableEq M_X]
    (code : CSSCode3D Q M_Z M_X) where
  L_Z : Q → ZMod 2
  L_X : Q → ZMod 2
  h_syn_Z : syndrome (dualCode code) L_Z = 0
  h_syn_X : syndrome code L_X = 0
  h_pair : (∑ q : Q, L_Z q * L_X q) = 1

/-- Existence of a dual logical pair $(L_Z, L_X)$. -/
def HasDualLogicalPair {Q M_Z M_X : Type}
    [Fintype Q] [DecidableEq Q] [Fintype M_Z] [DecidableEq M_Z] [Fintype M_X] [DecidableEq M_X]
    (code : CSSCode3D Q M_Z M_X) : Prop :=
  Nonempty (DualLogicalPair code)

end
