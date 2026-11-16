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

import Defs.WeylPauli

/-!
# Multi-Site Local CSS Check-Incidence Descriptors on Open-Box Lattices

Defines relative l_infinity neighborhood offset indices (`LocalNeighborhoodIdx`) and the finite, scale-independent combinatorial descriptor `LocalCSSDescriptor` recording active qubit slots and local X/Z check masks at a single lattice site. Provides conversion from a descriptor field on `Box3D L` (`ValidDescriptorField`) to concrete F_2 check operators (`descriptorCheckXChain`, `descriptorCheckZChain`) and open-box commuting-projector Hamiltonians (`staticCSSCheckProj`).

## References

* Part I, Section 2.1 (`subsec:css-complexes`), Definition 2.1 (`def:3d-css-complex`)
* Part I, Section 5.4 (`subsec:safe-decoded-observables`), Definition 5.6 (`def:safe-decoded-observables`)
* Part II, Section 2 (`subsec:setup`), Definition 2.1 (`def:bdl-lattice`)
-/

noncomputable section

open scoped Classical BigOperators InnerProduct ComplexConjugate
open ContinuousLinearMap

/-! ## 1. Relative Neighborhood Indices and Finite `LocalCSSDescriptor` -/

/-- Relative $\ell_\infty$-ball index `LocalNeighborhoodIdx r_0 := Fin 3 → Fin (2 * r_0 + 1)`
    representing integer displacements $\delta \in [-r_0, r_0]^3$. -/
abbrev LocalNeighborhoodIdx (r_0 : ℕ) : Type := Fin 3 → Fin (2 * r_0 + 1)

/-- Integer offset vector $\delta \in [-r_0, r_0]^3 \subset \mathbb{Z}^3$ of `nb : LocalNeighborhoodIdx r_0`. -/
def neighborhoodOffset (r_0 : ℕ) (nb : LocalNeighborhoodIdx r_0) : Fin 3 → ℤ :=
  fun μ => ((nb μ).val : ℤ) - (r_0 : ℤ)

/-- Finite, scale-independent local CSS check-incidence descriptor at a single lattice site $v$:
    - `q_code`: number of physical qubit slots per lattice site,
    - `r_0`: maximum $\ell_\infty$ check radius,
    - `m_max`: maximum number of $X$- or $Z$-checks anchored at a single site. -/
structure LocalCSSDescriptor (q_code r_0 m_max : ℕ) where
  activeSlot : Fin q_code → Bool
  numXChecks : Fin (m_max + 1)
  numZChecks : Fin (m_max + 1)
  xCheckMask : Fin m_max → LocalNeighborhoodIdx r_0 → Fin q_code → Bool
  zCheckMask : Fin m_max → LocalNeighborhoodIdx r_0 → Fin q_code → Bool

/-! ## 2. Global Check Chains and `ValidDescriptorField` -/

/-- Global bitstring `BoxSlot3D L q_code → ZMod 2` of the $j$-th $X$-check anchored at $v \in \mathrm{Box3D}\ L$. -/
def descriptorCheckXChain {L q_code r_0 m_max : ℕ}
    (ω : Box3D L → LocalCSSDescriptor q_code r_0 m_max)
    (v : Box3D L) (idx : Fin m_max) : BoxSlot3D L q_code → ZMod 2 :=
  fun ⟨w, s⟩ =>
    if idx.val < (ω v).numXChecks.val ∧
       ∃ nb : LocalNeighborhoodIdx r_0,
         InOpenBox v (neighborhoodOffset r_0 nb) ∧
         shiftOpenBox v (neighborhoodOffset r_0 nb) = w ∧
         (ω v).xCheckMask idx nb s = true
    then 1 else 0

/-- Global bitstring `BoxSlot3D L q_code → ZMod 2` of the $j$-th $Z$-check anchored at $v \in \mathrm{Box3D}\ L$. -/
def descriptorCheckZChain {L q_code r_0 m_max : ℕ}
    (ω : Box3D L → LocalCSSDescriptor q_code r_0 m_max)
    (v : Box3D L) (idx : Fin m_max) : BoxSlot3D L q_code → ZMod 2 :=
  fun ⟨w, s⟩ =>
    if idx.val < (ω v).numZChecks.val ∧
       ∃ nb : LocalNeighborhoodIdx r_0,
         InOpenBox v (neighborhoodOffset r_0 nb) ∧
         shiftOpenBox v (neighborhoodOffset r_0 nb) = w ∧
         (ω v).zCheckMask idx nb s = true
    then 1 else 0

/-- Global bitstring `BoxSlot3D L q_code → ZMod 2` of a single qubit slot `(v, s)`. -/
def singleSlotChain {L q_code : ℕ} (v : Box3D L) (s : Fin q_code) :
    BoxSlot3D L q_code → ZMod 2 :=
  fun p => if p = (v, s) then 1 else 0

/-- A descriptor field $\omega : \mathrm{Box3D}\ L \to \mathrm{LocalCSSDescriptor}\ q_{\mathrm{code}}\ r_0\ m_{\max}$
    is globally valid on the open box `Box3D L` if:
    1. All active check masks fit inside `Box3D L` without wrapping around boundaries;
    2. All active checks touch only active qubit slots (`activeSlot s = true`);
    3. Every active $X$-check chain and active $Z$-check chain have even symplectic overlap. -/
def ValidDescriptorField {L q_code r_0 m_max : ℕ}
    (ω : Box3D L → LocalCSSDescriptor q_code r_0 m_max) : Prop :=
  (∀ (v : Box3D L) (idx : Fin m_max) (nb : LocalNeighborhoodIdx r_0) (s : Fin q_code),
    idx.val < (ω v).numXChecks.val → (ω v).xCheckMask idx nb s = true →
      InOpenBox v (neighborhoodOffset r_0 nb) ∧
      (ω (shiftOpenBox v (neighborhoodOffset r_0 nb))).activeSlot s = true) ∧
  (∀ (v : Box3D L) (idx : Fin m_max) (nb : LocalNeighborhoodIdx r_0) (s : Fin q_code),
    idx.val < (ω v).numZChecks.val → (ω v).zCheckMask idx nb s = true →
      InOpenBox v (neighborhoodOffset r_0 nb) ∧
      (ω (shiftOpenBox v (neighborhoodOffset r_0 nb))).activeSlot s = true) ∧
  (∀ (vX vZ : Box3D L) (idxX idxZ : Fin m_max),
    (∑ p : BoxSlot3D L q_code,
      descriptorCheckXChain ω vX idxX p * descriptorCheckZChain ω vZ idxZ p) = 0)

/-- Alias for an $\mathbb{F}_2$ 1-chain `Q → ZMod 2`. -/
abbrev F2Chain (Q : Type) : Type := Q → ZMod 2

/-- Subgroup/set of $X$-stabilizer chains generated by active $X$-checks of `ω`. -/
def descriptorStabilizerX {L q_code r_0 m_max : ℕ}
    (ω : Box3D L → LocalCSSDescriptor q_code r_0 m_max) :
    Set (F2Chain (BoxSlot3D L q_code)) :=
  {s | ∃ c2 : Box3D L × Fin m_max → ZMod 2,
    s = fun p => ∑ mX : Box3D L × Fin m_max,
      descriptorCheckXChain ω mX.1 mX.2 p * c2 mX}

/-! ## 3. Static CSS Hamiltonian Check Lift -/

/-- Index type of elementary checks in the static CSS Hamiltonian lifted from $\omega$:
    - `Sum.inl (v, s)`: single-qubit $Z$-pin projector on an inactive slot `(ω v).activeSlot s = false`,
    - `Sum.inr (Sum.inl (v, idx))`: $X$-check `(v, idx)` of $\omega$,
    - `Sum.inr (Sum.inr (v, idx))`: $Z$-check `(v, idx)` of $\omega$. -/
abbrev StaticCSSCheckIdx (L q_code m_max : ℕ) : Type :=
  (Box3D L × Fin q_code) ⊕ (Box3D L × Fin m_max) ⊕ (Box3D L × Fin m_max)

/-- Elementary check projector $Q_i$ on `ManyBodyHilbertSpace (UniformSite3D L (CodeSlotConfig q_code))`
    for `i : StaticCSSCheckIdx L q_code m_max`. -/
def staticCSSCheckProj {L q_code r_0 m_max : ℕ}
    (ω : Box3D L → LocalCSSDescriptor q_code r_0 m_max) :
    StaticCSSCheckIdx L q_code m_max →
      (ManyBodyHilbertSpace (UniformSite3D L (CodeSlotConfig q_code)) →L[ℂ]
        ManyBodyHilbertSpace (UniformSite3D L (CodeSlotConfig q_code)))
  | Sum.inl (v, s) =>
      if (ω v).activeSlot s = false then weylCheckProjZ (singleSlotChain v s) else 0
  | Sum.inr (Sum.inl (v, idx)) =>
      if idx.val < (ω v).numXChecks.val then weylCheckProjX (descriptorCheckXChain ω v idx) else 0
  | Sum.inr (Sum.inr (v, idx)) =>
      if idx.val < (ω v).numZChecks.val then weylCheckProjZ (descriptorCheckZChain ω v idx) else 0

/-- Spatial support $\mathrm{supp}(Q_i) \subseteq \mathrm{Box3D}\ L$ of `staticCSSCheckProj ω i`. -/
def staticCSSCheckSupport {L q_code r_0 m_max : ℕ}
    (ω : Box3D L → LocalCSSDescriptor q_code r_0 m_max) :
    StaticCSSCheckIdx L q_code m_max → Finset (Box3D L)
  | Sum.inl (v, _) => {v}
  | Sum.inr (Sum.inl (v, _)) => boxBall v r_0
  | Sum.inr (Sum.inr (v, _)) => boxBall v r_0

end
