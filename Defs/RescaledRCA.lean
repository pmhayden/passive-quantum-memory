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

import Defs.BoxLattice
import Defs.ManyBodyHilbert
import Defs.LocalHamiltonian
import Defs.F2ChainAndCSS
import Defs.WeylPauli
import Defs.LocalCSSDescriptor
import Defs.ContractionAndHPL

/-!
# Relative Cone Acyclicity (RCA) on Continuum Balls, Open-Box Cubes, and Descriptor Fields

Defines continuum l_infinity balls (`distInf3D`, `ballQ`, `ballMZ`, `ballMX`), affine radius recurrences (`affineRadiusRecurrence`), and homological Relative Cone Acyclicity on 3D CSS codes in R^3 (`RescaledRelativeConeAcyclicity`, `SatisfiesF2LinearTQO`). Formulates chain support predicates (`BoxSlotChainSupportedIn`) and open-box descriptor-field Relative Cone Acyclicity (`SatisfiesBoxF2LinearTQO`) on `Box3D L`.

## References

* Part I, Section 3.1 (`subsec:rca-trinity`), Definition 3.1 (`def:rca`), Proposition 3.3 (`prop:trinity-equivalence`), Section 3.3 (`subsec:scale-matched-rca`), Theorem 3.9 (`thm:rca-welded-hierarchy`)
* Part II, Section 2 (`subsec:setup`), Definition 2.2 (`def:RCA`), Section 4 (`subsec:welded-hierarchy-cleaner`), Proposition 4.3 (`prop:rca-hierarchy`)
-/

noncomputable section

open scoped Classical BigOperators InnerProduct ComplexConjugate
open ContinuousLinearMap

/-! ## 1. Continuum $\ell_\infty$ Balls on 3D CSS Codes -/

/-- Continuum $\ell_\infty$ distance $\|x - y\|_\infty = \max_{\mu \in \{0,1,2\}} |x_\mu - y_\mu|$ on `Point3D`. -/
def distInf3D (x y : Point3D) : ℝ :=
  max (max |x 0 - y 0| |x 1 - y 1|) |x 2 - y 2|

/-- Set of physical qubits `q : Q` of `code` in the $\ell_\infty$-ball $B_\infty(x, r) \subset \mathbb{R}^3$. -/
def ballQ {Q M_Z M_X : Type}
    [Fintype Q] [DecidableEq Q] [Fintype M_Z] [DecidableEq M_Z] [Fintype M_X] [DecidableEq M_X]
    (code : CSSCode3D Q M_Z M_X) (x : Point3D) (r : ℝ) : Set Q :=
  {q : Q | distInf3D (code.posQ q) x ≤ r}

/-- Set of $Z$-checks `mZ : M_Z` of `code` in the $\ell_\infty$-ball $B_\infty(x, r) \subset \mathbb{R}^3$. -/
def ballMZ {Q M_Z M_X : Type}
    [Fintype Q] [DecidableEq Q] [Fintype M_Z] [DecidableEq M_Z] [Fintype M_X] [DecidableEq M_X]
    (code : CSSCode3D Q M_Z M_X) (x : Point3D) (r : ℝ) : Set M_Z :=
  {mZ : M_Z | distInf3D (code.posZ mZ) x ≤ r}

/-- Set of $X$-checks `mX : M_X` of `code` in the $\ell_\infty$-ball $B_\infty(x, r) \subset \mathbb{R}^3$. -/
def ballMX {Q M_Z M_X : Type}
    [Fintype Q] [DecidableEq Q] [Fintype M_Z] [DecidableEq M_Z] [Fintype M_X] [DecidableEq M_X]
    (code : CSSCode3D Q M_Z M_X) (x : Point3D) (r : ℝ) : Set M_X :=
  {mX : M_X | distInf3D (code.posX mX) x ≤ r}

lemma ballMZ_mono {Q M_Z M_X : Type}
    [Fintype Q] [DecidableEq Q] [Fintype M_Z] [DecidableEq M_Z] [Fintype M_X] [DecidableEq M_X]
    (code : CSSCode3D Q M_Z M_X) (x : Point3D) {r₁ r₂ : ℝ} (h : r₁ ≤ r₂) :
    ballMZ code x r₁ ⊆ ballMZ code x r₂ :=
  fun _ hm => le_trans hm h

lemma ballMX_mono {Q M_Z M_X : Type}
    [Fintype Q] [DecidableEq Q] [Fintype M_Z] [DecidableEq M_Z] [Fintype M_X] [DecidableEq M_X]
    (code : CSSCode3D Q M_Z M_X) (x : Point3D) {r₁ r₂ : ℝ} (h : r₁ ≤ r₂) :
    ballMX code x r₁ ⊆ ballMX code x r₂ :=
  fun _ hm => le_trans hm h

/-! ## 2. Affine Radius Recurrence & `RescaledRelativeConeAcyclicity` -/

/-- Iterated affine radius recurrence
    $R_0(r) = r$, $R_{t+1}(r) = r + \lambda^{-1} R_t(\lambda r + C_{\mathrm{step}})$. -/
def affineRadiusRecurrence (lam C_step : ℝ) : ℕ → ℝ → ℝ
  | 0, r => r
  | t + 1, r => r + lam⁻¹ * affineRadiusRecurrence lam C_step t (lam * r + C_step)

/-- **Rescaled Relative Cone Acyclicity (`RescaledRelativeConeAcyclicity`)**:
    Captures the single-step homological cone-cleaning recurrence from depth $s+1$ down to depth $s$:
    every cocycle $z_1$ whose boundary is supported outside $B_\infty(\lambda x, \lambda r + C_{\mathrm{step}})$
    differs by a local coboundary supported inside $B_\infty(\lambda x, \lambda r + C_{\mathrm{step}})$
    from the lift of a coarse cocycle at depth $s$. -/
def RescaledRelativeConeAcyclicity
    {Q M_Z M_X : ℕ → Type}
    [∀ s, Fintype (Q s)] [∀ s, DecidableEq (Q s)]
    [∀ s, Fintype (M_Z s)] [∀ s, DecidableEq (M_Z s)]
    [∀ s, Fintype (M_X s)] [∀ s, DecidableEq (M_X s)]
    (code : ∀ s, CSSCode3D (Q s) (M_Z s) (M_X s))
    (lam C_step r_base L_macro : ℝ) : Prop :=
  1 < lam ∧ 0 ≤ C_step ∧ 0 < r_base ∧
  ∀ (s : ℕ) (x : Point3D) (r : ℝ),
    0 ≤ r → r ≤ L_macro * lam ^ s →
    ∀ z1 : Q s → ZMod 2,
      (∀ q : Q s, z1 q ≠ (0 : ZMod 2) → q ∈ ballQ (code s) x r) →
      syndrome (code s) z1 = 0 →
      ∃ c2 : M_Z s → ZMod 2,
        checkGen (code s) c2 = z1 ∧
        ∀ mZ : M_Z s, c2 mZ ≠ (0 : ZMod 2) →
          mZ ∈ ballMZ (code s) x (affineRadiusRecurrence lam C_step s r)

/-- **$\mathbb{F}_2$-Chain Linear TQO (`SatisfiesF2LinearTQO`)** on a 3D CSS code `code`:
    For every ball $B_\infty(x, r)$ ($0 \le r \le L^*$), every primal cocycle ($\partial_1 a = 0$)
    supported in $B_\infty(x, r)$ is generated by $Z$-checks in $B_\infty(x, C_{\mathrm{lin}} r + C_{\mathrm{add}})$,
    and every dual cocycle ($\delta^1 b = 0$) supported in $B_\infty(x, r)$ is generated by $X$-checks in
    $B_\infty(x, C_{\mathrm{lin}} r + C_{\mathrm{add}})$. -/
def SatisfiesF2LinearTQO {Q M_Z M_X : Type}
    [Fintype Q] [DecidableEq Q] [Fintype M_Z] [DecidableEq M_Z] [Fintype M_X] [DecidableEq M_X]
    (code : CSSCode3D Q M_Z M_X) (L_star C_lin C_add : ℝ) : Prop :=
  (∀ (x : Point3D) (r : ℝ), 0 ≤ r → r ≤ L_star →
    ∀ a : Q → ZMod 2,
      (∀ q : Q, a q ≠ (0 : ZMod 2) → q ∈ ballQ code x r) →
      syndrome code a = 0 →
      ∃ c2 : M_Z → ZMod 2,
        checkGen code c2 = a ∧
        ∀ mZ : M_Z, c2 mZ ≠ (0 : ZMod 2) → mZ ∈ ballMZ code x (C_lin * r + C_add)) ∧
  (∀ (x : Point3D) (r : ℝ), 0 ≤ r → r ≤ L_star →
    ∀ b : Q → ZMod 2,
      (∀ q : Q, b q ≠ (0 : ZMod 2) → q ∈ ballQ code x r) →
      syndrome (dualCode code) b = 0 →
      ∃ d2 : M_X → ZMod 2,
        checkGen (dualCode code) d2 = b ∧
        ∀ mX : M_X, d2 mX ≠ (0 : ZMod 2) → mX ∈ ballMX code x (C_lin * r + C_add))

/-! ## 3. Open-Box Lattice $\mathbb{F}_2$-Chain Linear TQO (`SatisfiesBoxF2LinearTQO`) -/

/-- A bitstring $a : \mathrm{BoxSlot3D}\ L\ q_{\mathrm{code}} \to \mathrm{ZMod}\ 2$ is supported inside
    a lattice region $A \subseteq \mathrm{Box3D}\ L$ if $a(v, s) \neq 0 \implies v \in A$. -/
def BoxSlotChainSupportedIn {L q_code : ℕ}
    (a : BoxSlot3D L q_code → ZMod 2) (A : Finset (Box3D L)) : Prop :=
  ∀ p : BoxSlot3D L q_code, a p ≠ (0 : ZMod 2) → p.1 ∈ A

/-- **Open-Box $\mathbb{F}_2$ Linear TQO (`SatisfiesBoxF2LinearTQO`)** for a descriptor field $\omega$:
    For every scale $1 \le r \le L^*$ and cube $A = \mathrm{boxCube}(x_0, r)$, with enclosing collar
    $B = \mathrm{enclosingBoxCube}(x_0, r, \mathrm{linearExpansionRadius}\ C\ r)$:
    1. Every $Z$-type Pauli string $Z(a)$ supported on $A$ that commutes with all active $X$-checks of $\omega$
       is generated by inactive-slot pins and active $Z$-checks whose supports are contained in $B$;
    2. Every $X$-type Pauli string $X(b)$ supported on $A$ that vanishes on inactive slots and commutes
       with all active $Z$-checks of $\omega$ is generated by active $X$-checks whose supports are contained in $B$. -/
def SatisfiesBoxF2LinearTQO {L q_code r_0 m_max : ℕ}
    (ω : Box3D L → LocalCSSDescriptor q_code r_0 m_max) (L_star : ℕ) (C : ℝ) : Prop :=
  ∀ (r : ℕ), 1 ≤ r → r ≤ L_star →
    ∀ x0 : Box3D L,
      let A := boxCube x0 r
      let B := enclosingBoxCube x0 r (linearExpansionRadius C r)
      (∀ a : BoxSlot3D L q_code → ZMod 2,
        BoxSlotChainSupportedIn a A →
        (∀ (v : Box3D L) (idx : Fin m_max), idx.val < (ω v).numXChecks.val →
          (∑ p : BoxSlot3D L q_code, a p * descriptorCheckXChain ω v idx p) = 0) →
        ∃ (c_pin : Box3D L × Fin q_code → ZMod 2) (c_Z : Box3D L × Fin m_max → ZMod 2),
          (∀ p, c_pin p ≠ (0 : ZMod 2) → (ω p.1).activeSlot p.2 = false ∧ p.1 ∈ B) ∧
          (∀ p, c_Z p ≠ (0 : ZMod 2) → p.2.val < (ω p.1).numZChecks.val ∧ boxBall p.1 r_0 ⊆ B) ∧
          a = (∑ p : Box3D L × Fin q_code, c_pin p • singleSlotChain p.1 p.2) +
              (∑ p : Box3D L × Fin m_max, c_Z p • descriptorCheckZChain ω p.1 p.2)) ∧
      (∀ b : BoxSlot3D L q_code → ZMod 2,
        BoxSlotChainSupportedIn b A →
        (∀ p : BoxSlot3D L q_code, b p ≠ (0 : ZMod 2) → (ω p.1).activeSlot p.2 = true) →
        (∀ (v : Box3D L) (idx : Fin m_max), idx.val < (ω v).numZChecks.val →
          (∑ p : BoxSlot3D L q_code, b p * descriptorCheckZChain ω v idx p) = 0) →
        ∃ c_X : Box3D L × Fin m_max → ZMod 2,
          (∀ p, c_X p ≠ (0 : ZMod 2) → p.2.val < (ω p.1).numXChecks.val ∧ boxBall p.1 r_0 ⊆ B) ∧
          b = ∑ p : Box3D L × Fin m_max, c_X p • descriptorCheckXChain ω p.1 p.2)
