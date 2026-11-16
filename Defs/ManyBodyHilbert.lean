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
import Mathlib.Analysis.CStarAlgebra.Projection
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Normed.Operator.ContinuousLinearMap

/-!
# Finite-Dimensional Lattice Many-Body Hilbert Spaces, Cylinder Extensions, and Partial Traces

Constructs the finite-dimensional complex lattice Hilbert space `ManyBodyHilbertSpace Site` over `BoxD D L`, regional configuration spaces (`LocalHilbertSpace`), spatial operator support predicates (`IsSupportedOn`), conditional expectations (`condExp`), and partial traces (`partialTrace`).

## References

* Part I, Section 3.1 (`subsec:rca-trinity`), Definition 3.2 (`def:tqo`), Section 5.4 (`subsec:safe-decoded-observables`), Definition 5.6 (`def:safe-decoded-observables`)
* Part II, Section 2 (`subsec:setup`), Definition 2.1 (`def:bdl-lattice`)
-/

noncomputable section

open scoped Classical InnerProduct ComplexConjugate BigOperators
open ContinuousLinearMap

/-!
## 1. Many-Body Configurations and Hilbert Spaces on `BoxD D L`
-/

/-- Global many-body basis configurations $\sigma \in \prod_{x \in \mathrm{BoxD}\ D\ L} \mathrm{Site}(x)$. -/
abbrev ManyBodyConfig {D L : ℕ} (Site : BoxD D L → Type) : Type :=
  ∀ x : BoxD D L, Site x

/-- Local basis configurations on a subset $A \subseteq \mathrm{BoxD}\ D\ L$. -/
abbrev LocalConfig {D L : ℕ} (Site : BoxD D L → Type) (A : Finset (BoxD D L)) : Type :=
  ∀ x : A, Site x.1

/-- The global many-body Hilbert space $\mathcal{H} = \bigotimes_{x \in \Lambda_L} \mathcal{H}_x$,
    realized as the complex Hilbert space `EuclideanSpace ℂ (ManyBodyConfig Site)`. -/
abbrev ManyBodyHilbertSpace {D L : ℕ} (Site : BoxD D L → Type) : Type :=
  EuclideanSpace ℂ (ManyBodyConfig Site)

/-- The local subsystem Hilbert space $\mathcal{H}_A = \bigotimes_{x \in A} \mathcal{H}_x$
    associated to a lattice region $A \subseteq \mathrm{BoxD}\ D\ L$. -/
abbrev LocalHilbertSpace {D L : ℕ} (Site : BoxD D L → Type) (A : Finset (BoxD D L)) : Type :=
  EuclideanSpace ℂ (LocalConfig Site A)

/-- Uniform site configuration type family on `Box3D L` with identical local basis `Site0`. -/
abbrev UniformSite3D (L : ℕ) (Site0 : Type) : Box3D L → Type :=
  fun _ => Site0

/-!
## 2. Configuration Restriction, Splicing, Cylinder Embeddings, and Support
-/

/-- Restrict a global configuration $\sigma \in \prod_{x \in \Lambda_L} \mathrm{Site}(x)$ to $A \subseteq \Lambda_L$. -/
def restrictConfig {D L : ℕ} {Site : BoxD D L → Type}
    (A : Finset (BoxD D L)) (σ : ManyBodyConfig Site) : LocalConfig Site A :=
  fun x => σ x.1

/-- Splice a local configuration $\alpha$ on $A$ with a background configuration $\sigma$ on $A^c$. -/
def spliceConfig {D L : ℕ} {Site : BoxD D L → Type}
    (A : Finset (BoxD D L)) (α : LocalConfig Site A) (σ : ManyBodyConfig Site) :
    ManyBodyConfig Site :=
  fun x => if hx : x ∈ A then α ⟨x, hx⟩ else σ x

/-- Canonical tensor-product cylinder embedding $\mathcal{B}(\mathcal{H}_A) \to \mathcal{B}(\mathcal{H})$,
    mapping $O_{\mathrm{loc}} : \mathcal{H}_A \to_L[\mathbb{C}] \mathcal{H}_A$ to
    $O_{\mathrm{loc}} \otimes I_{A^c} : \mathcal{H} \to_L[\mathbb{C}] \mathcal{H}$. -/
def cylinderOp {D L : ℕ}
    (Site : BoxD D L → Type) [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    (A : Finset (BoxD D L))
    (O_loc : LocalHilbertSpace Site A →L[ℂ] LocalHilbertSpace Site A) :
    ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site :=
  LinearMap.toContinuousLinearMap
    { toFun := fun ψ => WithLp.toLp 2 (fun σ : ManyBodyConfig Site =>
        (O_loc (WithLp.toLp 2 (fun α : LocalConfig Site A => ψ.ofLp (spliceConfig A α σ)))).ofLp
          (restrictConfig A σ))
      map_add' := fun ψ₁ ψ₂ => by
        ext σ
        have h_slice :
            WithLp.toLp 2 (fun α : LocalConfig Site A => (ψ₁ + ψ₂).ofLp (spliceConfig A α σ)) =
            WithLp.toLp 2 (fun α : LocalConfig Site A => ψ₁.ofLp (spliceConfig A α σ)) +
            WithLp.toLp 2 (fun α : LocalConfig Site A => ψ₂.ofLp (spliceConfig A α σ)) := by
          ext α; rfl
        change (O_loc (WithLp.toLp 2 (fun α : LocalConfig Site A => (ψ₁ + ψ₂).ofLp (spliceConfig A α σ)))).ofLp (restrictConfig A σ) =
          (O_loc (WithLp.toLp 2 (fun α : LocalConfig Site A => ψ₁.ofLp (spliceConfig A α σ)))).ofLp (restrictConfig A σ) +
          (O_loc (WithLp.toLp 2 (fun α : LocalConfig Site A => ψ₂.ofLp (spliceConfig A α σ)))).ofLp (restrictConfig A σ)
        rw [h_slice, map_add]; rfl
      map_smul' := fun c ψ => by
        ext σ
        have h_slice :
            WithLp.toLp 2 (fun α : LocalConfig Site A => (c • ψ).ofLp (spliceConfig A α σ)) =
            c • WithLp.toLp 2 (fun α : LocalConfig Site A => ψ.ofLp (spliceConfig A α σ)) := by
          ext α; rfl
        change (O_loc (WithLp.toLp 2 (fun α : LocalConfig Site A => (c • ψ).ofLp (spliceConfig A α σ)))).ofLp (restrictConfig A σ) =
          c * (O_loc (WithLp.toLp 2 (fun α : LocalConfig Site A => ψ.ofLp (spliceConfig A α σ)))).ofLp (restrictConfig A σ)
        rw [h_slice, map_smul]; rfl }

/-- An operator $O \in \mathcal{B}(\mathcal{H})$ is supported on a region $A \subseteq \mathrm{BoxD}\ D\ L$
    if $O = O_{\mathrm{loc}} \otimes I_{A^c}$ for some local operator $O_{\mathrm{loc}} \in \mathcal{B}(\mathcal{H}_A)$. -/
def IsSupportedOn {D L : ℕ}
    (Site : BoxD D L → Type) [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    (A : Finset (BoxD D L))
    (O : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site) : Prop :=
  ∃ O_loc : LocalHilbertSpace Site A →L[ℂ] LocalHilbertSpace Site A,
    O = cylinderOp Site A O_loc

/-- Standard computational basis vector $|\sigma\rangle \in \mathcal{H}$ for a global configuration $\sigma$. -/
def basisVecGlobal {D L : ℕ}
    (Site : BoxD D L → Type) [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    (σ : ManyBodyConfig Site) : ManyBodyHilbertSpace Site :=
  WithLp.toLp 2 (fun τ => if τ = σ then 1 else 0)

/-- Combine a local configuration $\alpha$ on $A$ and a complement configuration $\gamma$ on $\Lambda_L \setminus A$. -/
def combineConfig {D L : ℕ} {Site : BoxD D L → Type}
    (A : Finset (BoxD D L))
    (α : LocalConfig Site A) (γ : LocalConfig Site (Finset.univ \ A)) :
    ManyBodyConfig Site :=
  fun x => if hx : x ∈ A then α ⟨x, hx⟩ else γ ⟨x, Finset.mem_sdiff.mpr ⟨Finset.mem_univ x, hx⟩⟩

/-!
## 3. Quantum Partial Trace, Haar Conditional Expectation `condExp`, and Trace / Commutators
-/

/-- Matrix element $\langle (\alpha, \gamma) | \rho | (\beta, \gamma) \rangle$ for the partial trace over $A^c$. -/
def partialTraceEntry {D L : ℕ}
    (Site : BoxD D L → Type) [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    (A : Finset (BoxD D L))
    (ρ : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site)
    (γ : LocalConfig Site (Finset.univ \ A))
    (α β : LocalConfig Site A) : ℂ :=
  (ρ (basisVecGlobal Site (combineConfig A β γ))).ofLp (combineConfig A α γ)

/-- The quantum partial trace $\mathrm{tr}_{A^c} : \mathcal{B}(\mathcal{H}) \to \mathcal{B}(\mathcal{H}_A)$
    tracing out the complement $A^c = \Lambda_L \setminus A$. -/
def partialTrace {D L : ℕ}
    (Site : BoxD D L → Type) [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    (A : Finset (BoxD D L))
    (ρ : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site) :
    LocalHilbertSpace Site A →L[ℂ] LocalHilbertSpace Site A :=
  LinearMap.toContinuousLinearMap
    { toFun := fun ψ_A => WithLp.toLp 2 (fun α : LocalConfig Site A =>
        ∑ γ : LocalConfig Site (Finset.univ \ A),
          ∑ β : LocalConfig Site A,
            partialTraceEntry Site A ρ γ α β * ψ_A.ofLp β)
      map_add' := fun ψ₁ ψ₂ => by
        ext α
        change (∑ γ : LocalConfig Site (Finset.univ \ A), ∑ β : LocalConfig Site A,
            partialTraceEntry Site A ρ γ α β * (ψ₁.ofLp β + ψ₂.ofLp β)) =
          (∑ γ : LocalConfig Site (Finset.univ \ A), ∑ β : LocalConfig Site A,
            partialTraceEntry Site A ρ γ α β * ψ₁.ofLp β) +
          (∑ γ : LocalConfig Site (Finset.univ \ A), ∑ β : LocalConfig Site A,
            partialTraceEntry Site A ρ γ α β * ψ₂.ofLp β)
        simp only [mul_add, Finset.sum_add_distrib]
      map_smul' := fun c ψ => by
        ext α
        change (∑ γ : LocalConfig Site (Finset.univ \ A), ∑ β : LocalConfig Site A,
            partialTraceEntry Site A ρ γ α β * (c * ψ.ofLp β)) =
          c * (∑ γ : LocalConfig Site (Finset.univ \ A), ∑ β : LocalConfig Site A,
            partialTraceEntry Site A ρ γ α β * ψ.ofLp β)
        simp only [Finset.mul_sum, mul_left_comm] }

/-- Normalized Haar partial-trace conditional expectation
    $\mathbb{E}_A : \mathcal{B}(\mathcal{H}) \to \mathcal{B}(\mathcal{H})$ onto cylinder operators supported on $A \subseteq \Lambda_L$:
    $$\mathbb{E}_A(O) := \frac{1}{|\mathrm{LocalConfig}(\Lambda_L \setminus A)|} \, \mathrm{cylinderOp}_A(\mathrm{tr}_{A^c}(O)).$$ -/
def condExp {D L : ℕ}
    (Site : BoxD D L → Type) [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    (A : Finset (BoxD D L))
    (O : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site) :
    ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site :=
  cylinderOp Site A (((Fintype.card (LocalConfig Site (Finset.univ \ A)) : ℂ)⁻¹) • partialTrace Site A O)

/-- Canonical real trace $\operatorname{Tr}(A) := \sum_{\psi} \operatorname{Re}\langle \psi, A \psi \rangle$
    on the finite-dimensional many-body Hilbert space $\mathcal{H}$. -/
def hilbertTrace {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    (A : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site) : ℝ :=
  ∑ ψ : ManyBodyConfig Site,
    RCLike.re (inner ℂ (basisVecGlobal Site ψ) (A (basisVecGlobal Site ψ)))

/-- Rank-one ket-bra operator $|\varphi\rangle\langle\varphi| : \psi \mapsto \langle \varphi, \psi \rangle \varphi$. -/
def rankOneKetBra {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (φ : H) : H →L[ℂ] H :=
  (innerSL ℂ φ).smulRight φ

/-- Operator commutator $[A, B] := A B - B A$. -/
def opCommutator {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (A B : H →L[ℂ] H) : H →L[ℂ] H :=
  A * B - B * A
