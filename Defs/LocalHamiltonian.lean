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

import Defs.ManyBodyHilbert
import Mathlib.Analysis.InnerProductSpace.Spectrum
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Frustration-Free Commuting-Projector Hamiltonians, TQO Conditions, and Quasi-Local Perturbations

Defines check-indexed (`IndexedCommutingProjectorHamiltonian`) and cube-indexed (`CommutingProjectorHamiltonian`) frustration-free commuting-projector Hamiltonians with local ground projectors (`localGroundProj`) and syndrome sector projectors (`syndromeProjector`). Formalizes operator topological quantum order (`SatisfiesTQO1`, `SatisfiesTQO2`, `SatisfiesLinearTQO2`, `SatisfiesSectorFilteredLinearTQO2`), quasi-local Hermitian perturbations (`QuasiLocalPerturbation`, `totalPerturbation`), and spectral eigenvalue ordering (`sortedEigenvalues`, `sortedEigenbasis`).

## References

* Part I, Section 3.1 (`subsec:rca-trinity`), Definition 3.2 (`def:tqo`), Section 5.4 (`subsec:safe-decoded-observables`), Definition 5.6 (`def:safe-decoded-observables`)
* Part I, Section 6.1 (`subsec:dsuper-banach`), Definition 6.1 (`def:banach-quasilocal`)
* Part II, Section 2 (`subsec:setup`), Definition 2.1 (`def:bdl-lattice`), Definition 2.3 (`def:perturbation-class`)
-/

noncomputable section

open scoped Classical InnerProduct ComplexConjugate BigOperators
open ContinuousLinearMap

/-!
## 1. Indexed Frustration-Free Commuting-Projector Hamiltonians on `BoxD D L`
-/

/-- A frustration-free commuting-projector Hamiltonian $H_0 = \sum_{i \in \iota} w_i Q_i$ on the open box
    `BoxD D L` indexed by an arbitrary finite check type `ι`.
    All operator-level stability and KMS lifetime modules operate on this general
    commuting-projector structure rather than restricting to CSS codes. -/
structure IndexedCommutingProjectorHamiltonian (D L : ℕ)
    (Site : BoxD D L → Type) [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    (ι : Type) [Fintype ι] [DecidableEq ι] where
  /-- Elementary check projectors $Q_i : \mathcal{H} \to_L[\mathbb{C}] \mathcal{H}$ for $i \in \iota$. -/
  checkProj : ι → (ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site)
  /-- Positive energy weights $w_i \ge 1$ for $i \in \iota$ ($w_i = 1$ for unweighted checks). -/
  weight : ι → ℝ
  /-- Spatial support $\mathrm{supp}(Q_i) \subseteq \mathrm{BoxD}\ D\ L$ of each check $i \in \iota$. -/
  support : ι → Finset (BoxD D L)
  /-- Each $Q_i$ is an orthogonal projection ($Q_i^2 = Q_i$ and $Q_i^\dagger = Q_i$). -/
  is_projector : ∀ i : ι, IsStarProjection (checkProj i)
  /-- Each $Q_i$ is supported on `support i`. -/
  is_supported : ∀ i : ι, IsSupportedOn Site (support i) (checkProj i)
  /-- The check projectors $\{Q_i\}_{i \in \iota}$ pairwise commute ($[Q_i, Q_j] = 0$). -/
  pairwise_commute : ∀ i j : ι, Commute (checkProj i) (checkProj j)
  /-- Every check weight satisfies $w_i \ge 1$. -/
  weight_ge_one : ∀ i : ι, 1 ≤ weight i
  /-- Frustration-freeness: the global ground-state projector $P_0 = \prod_{i \in \iota} (I - Q_i)$ is non-zero. -/
  frustration_free : (((Finset.univ : Finset ι).toList.map (fun i => 1 - checkProj i)).prod) ≠ 0

namespace IndexedCommutingProjectorHamiltonian

variable {D L : ℕ} {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
variable {ι : Type} [Fintype ι] [DecidableEq ι]
variable (sys : IndexedCommutingProjectorHamiltonian D L Site ι)

/-- Weighted unperturbed Hamiltonian $H_0 = \sum_{i \in \iota} w_i Q_i$. -/
def H0 : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site :=
  ∑ i : ι, (sys.weight i : ℂ) • sys.checkProj i

/-- Local ground projector $P_B = \prod_{i \in \iota,\, \mathrm{supp}(Q_i) \subseteq B} (I - Q_i)$ on $B \subseteq \Lambda_L$. -/
def localGroundProj (B : Finset (BoxD D L)) :
    ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site :=
  (((Finset.univ.filter (fun i : ι => sys.support i ⊆ B)).toList.map
    (fun i => 1 - sys.checkProj i)).prod)

/-- Global ground-space projector $P_0 = \prod_{i \in \iota} (I - Q_i)$ onto $\ker H_0$. -/
def groundProj : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site :=
  (((Finset.univ : Finset ι).toList.map (fun i => 1 - sys.checkProj i)).prod)

/-- Alias `sys.P0` for `sys.groundProj`. -/
abbrev P0 : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site :=
  sys.groundProj

/-- Unperturbed ground-state subspace $\ker H_0 \le \mathcal{H}$. -/
def groundSpace : Submodule ℂ (ManyBodyHilbertSpace Site) :=
  LinearMap.ker sys.H0.toLinearMap

/-- Unperturbed ground-state topological degeneracy $d_{\mathrm{gs}} = \dim_{\mathbb{C}}(\ker H_0)$. -/
def groundDegeneracy : ℕ :=
  Module.finrank ℂ sys.groundSpace

/-- Simultaneous check-syndrome eigenspace projector
    $\Pi_{\mathrm{syn}}(\sigma) = \prod_{i \in \iota} (\text{if }\sigma(i)\text{ then }Q_i\text{ else }(I - Q_i))$. -/
def syndromeProjector (σ : ι → Bool) :
    ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site :=
  (((Finset.univ : Finset ι).toList.map
    (fun i => if σ i then sys.checkProj i else 1 - sys.checkProj i)).prod)

/-- Simultaneous check-syndrome eigenvalue $E_{\mathrm{syn}}(\sigma) = \sum_{i : \sigma(i) = \mathrm{true}} w_i$. -/
def syndromeEnergy (σ : ι → Bool) : ℝ :=
  ∑ i ∈ Finset.univ.filter (fun i : ι => σ i = true), sys.weight i

/-- Geometric $(r_0, w_0)$-locality of `sys` on `BoxD D L`: every check is contained in an $\ell_\infty$-ball
    of radius $r_0$, and each site participates in at most $w_0$ checks. -/
def IsGeometricallyLocal (r_0 w_0 : ℕ) : Prop :=
  (∀ i : ι, ∃ v : BoxD D L, sys.support i ⊆ boxBall v r_0) ∧
  (∀ v : BoxD D L, (Finset.univ.filter (fun i : ι => v ∈ sys.support i)).card ≤ w_0)

end IndexedCommutingProjectorHamiltonian

/-!
## 2. Cube-Indexed Commuting-Projector Hamiltonians on `BoxD D L`
-/

/-- Local ground projector $P_B = \prod_{A \in \mathcal{S}(2),\, A \subseteq B} (I - Q_A)$ for a $2$-cube family. -/
def localGroundProjector {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    (Q : Finset (BoxD D L) → (ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site))
    (B : Finset (BoxD D L)) :
    ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site :=
  (((boxCubes D L 2).filter (fun A => A ⊆ B)).toList.map (fun A => 1 - Q A)).prod

/-- Global ground projector $P = \prod_{A \in \mathcal{S}(2)} (I - Q_A)$ for a $2$-cube family. -/
def globalGroundProjector {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    (Q : Finset (BoxD D L) → (ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site)) :
    ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site :=
  localGroundProjector Q Finset.univ

/-- Coarse-grained $2^D$-cube commuting-projector Hamiltonian $H_0 = \sum_{A \in \mathcal{S}(2)} Q_A$
    on the open box `BoxD D L` (used by the Bravyi–Hastings–Michalakis telescoping engine). -/
structure CommutingProjectorHamiltonian (D L : ℕ)
    (Site : BoxD D L → Type) [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)] where
  /-- Elementary interaction terms $Q_A$ indexed by $2$-cubes $A \in \mathcal{S}(2)$. -/
  Q : Finset (BoxD D L) → (ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site)
  /-- Each $Q_A$ for $A \in \mathcal{S}(2)$ is an orthogonal projector. -/
  is_projector : ∀ A ∈ boxCubes D L 2, IsStarProjection (Q A)
  /-- Each $Q_A$ for $A \in \mathcal{S}(2)$ is supported on the cube $A$. -/
  is_supported : ∀ A ∈ boxCubes D L 2, IsSupportedOn Site A (Q A)
  /-- The projectors $\{Q_A\}_{A \in \mathcal{S}(2)}$ pairwise commute. -/
  pairwise_commute : ∀ A ∈ boxCubes D L 2, ∀ B ∈ boxCubes D L 2, Commute (Q A) (Q B)
  /-- Frustration-freeness: `globalGroundProjector Q ≠ 0`. -/
  frustration_free : globalGroundProjector Q ≠ 0

namespace CommutingProjectorHamiltonian

variable {D L : ℕ} {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
variable (sys : CommutingProjectorHamiltonian D L Site)

/-- Unperturbed Hamiltonian $H_0 = \sum_{A \in \mathcal{S}(2)} Q_A$. -/
def H0 : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site :=
  ∑ A ∈ boxCubes D L 2, sys.Q A

/-- Global ground-state projector $P = P_\Lambda$ of $H_0$. -/
def P : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site :=
  globalGroundProjector sys.Q

/-- Local ground-state projector $P_B$ on a region $B \subseteq \mathrm{BoxD}\ D\ L$. -/
def localGroundProj (B : Finset (BoxD D L)) :
    ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site :=
  localGroundProjector sys.Q B

end CommutingProjectorHamiltonian

/-!
## 3. Topological Quantum Order Conditions: `SatisfiesTQO1`, `SatisfiesLinearTQO2`, and `SatisfiesSectorFilteredLinearTQO2`
-/

/-- **Condition TQO-1 (Local Indistinguishability)** for `IndexedCommutingProjectorHamiltonian`:
    For every scale $1 \le r \le L^*$, every cube $A = \mathrm{boxCube}(x_0, r)$, and every operator $O_A$
    supported on $A$, there exists a scalar $c \in \mathbb{C}$ such that $P_0 O_A P_0 = c P_0$. -/
def SatisfiesTQO1 {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (sys : IndexedCommutingProjectorHamiltonian D L Site ι) (L_star : ℕ) : Prop :=
  ∀ r : ℕ, 1 ≤ r → r ≤ L_star →
    ∀ x0 : BoxD D L,
      let A := boxCube x0 r
      ∀ O_A : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site,
        IsSupportedOn Site A O_A →
          ∃ c : ℂ, sys.P0 * O_A * sys.P0 = c • sys.P0

/-- **Condition TQO-2 (Consistency of Local and Global Ground Spaces)** for `IndexedCommutingProjectorHamiltonian`. -/
def SatisfiesTQO2 {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (sys : IndexedCommutingProjectorHamiltonian D L Site ι) (L_star : ℕ) (R : ℕ → ℕ) : Prop :=
  ∀ r : ℕ, 1 ≤ r → r ≤ L_star →
    ∀ x0 : BoxD D L,
      let A := boxCube x0 r
      let B := enclosingBoxCube x0 r (R r)
      LinearMap.ker (partialTrace Site A sys.P0).toLinearMap =
        LinearMap.ker (partialTrace Site A (sys.localGroundProj B)).toLinearMap ∧
      ∀ O_A : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site,
        IsSupportedOn Site A O_A → (O_A * sys.P0 = 0 ↔ O_A * sys.localGroundProj B = 0)

/-- **Condition Linear TQO-2** with linear expansion radius $R(r) = \lceil C r \rceil$. -/
def SatisfiesLinearTQO2 {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (sys : IndexedCommutingProjectorHamiltonian D L Site ι) (L_star : ℕ) (C : ℝ) : Prop :=
  SatisfiesTQO2 sys L_star (linearExpansionRadius C)

/-- **Sector-Filtered Linear TQO-2 (`SatisfiesSectorFilteredLinearTQO2`)**:
    Formulates TQO-1 and Linear TQO-2 relative to an orthogonal sector projector $\Pi_{\mathrm{sec}}$
    commuting with every check projector `sys.checkProj i` and containing the global ground space
    ($\mathrm{sys.P0} \cdot \Pi_{\mathrm{sec}} = \mathrm{sys.P0}$): for every cube $A = \mathrm{boxCube}(x_0, r)$
    of side $1 \le r \le L^*$ with dilated collar $B = \mathrm{enclosingBoxCube}(x_0, r, \lceil C r \rceil)$
    and every operator $O_A$ supported on $A$, $O_A P_0 = 0$ holds if and only if
    $O_A \Pi_{\mathrm{sec}} P_B = 0$. Setting $\Pi_{\mathrm{sec}} = 1$ recovers standard
    `SatisfiesTQO1` together with `SatisfiesLinearTQO2`. -/
def SatisfiesSectorFilteredLinearTQO2 {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (sys : IndexedCommutingProjectorHamiltonian D L Site ι)
    (Pi_sec : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site)
    (L_star : ℕ) (C : ℝ) : Prop :=
  IsStarProjection Pi_sec ∧
  (∀ i : ι, Commute (sys.checkProj i) Pi_sec) ∧
  sys.P0 * Pi_sec = sys.P0 ∧
  SatisfiesTQO1 sys L_star ∧
  ∀ r : ℕ, 1 ≤ r → r ≤ L_star →
    ∀ x0 : BoxD D L,
      let A := boxCube x0 r
      let B := enclosingBoxCube x0 r (linearExpansionRadius C r)
      ∀ O_A : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site,
        IsSupportedOn Site A O_A →
          (O_A * sys.P0 = 0 ↔ O_A * Pi_sec * sys.localGroundProj B = 0)

/-- Cube-indexed TQO-1 predicate on `CommutingProjectorHamiltonian`. -/
def CommutingProjectorHamiltonian.SatisfiesTQO1 {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    (sys : CommutingProjectorHamiltonian D L Site) (L_star : ℕ) : Prop :=
  ∀ r : ℕ, 1 ≤ r → r ≤ L_star →
    ∀ x0 : BoxD D L,
      let A := boxCube x0 r
      ∀ O_A : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site,
        IsSupportedOn Site A O_A →
          ∃ c : ℂ, sys.P * O_A * sys.P = c • sys.P

/-- Cube-indexed Linear TQO-2 predicate on `CommutingProjectorHamiltonian`. -/
def CommutingProjectorHamiltonian.SatisfiesLinearTQO2 {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    (sys : CommutingProjectorHamiltonian D L Site) (L_star : ℕ) (C : ℝ) : Prop :=
  ∀ r : ℕ, 1 ≤ r → r ≤ L_star →
    ∀ x0 : BoxD D L,
      let A := boxCube x0 r
      let B := enclosingBoxCube x0 r (linearExpansionRadius C r)
      LinearMap.ker (partialTrace Site A sys.P).toLinearMap =
        LinearMap.ker (partialTrace Site A (sys.localGroundProj B)).toLinearMap ∧
      ∀ O_A : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site,
        IsSupportedOn Site A O_A → (O_A * sys.P = 0 ↔ O_A * sys.localGroundProj B = 0)

/-!
## 4. Quasi-Local Perturbations $\mathcal{B}_f(\Lambda_L)$ and Finite-Dimensional Spectral Ordering
-/

/-- A quasi-local Hermitian perturbation $V = \sum_{r=1}^L \sum_{A \in \mathcal{S}(r)} V_{r,A}$
    on the open box `BoxD D L` decomposed by interaction scale $r$ and cube $A \in \mathcal{S}(r)$. -/
structure QuasiLocalPerturbation (D L : ℕ)
    (Site : BoxD D L → Type) [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)] where
  /-- Interaction term $V_{r,A}$ for scale $r \in \mathbb{N}$ and cube $A \subseteq \mathrm{BoxD}\ D\ L$. -/
  term : ℕ → Finset (BoxD D L) → (ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site)
  /-- Every local interaction term $V_{r,A}$ is self-adjoint (Hermitian). -/
  is_selfAdjoint : ∀ (r : ℕ) (A : Finset (BoxD D L)), IsSelfAdjoint (term r A)
  /-- Each term $V_{r,A}$ for $A \in \mathcal{S}(r)$ is supported on the cube $A$. -/
  is_supported : ∀ r ∈ Finset.Icc 1 L, ∀ A ∈ boxCubes D L r, IsSupportedOn Site A (term r A)

/-- Alias `LocalPerturbation` for `QuasiLocalPerturbation`. -/
abbrev LocalPerturbation (D L : ℕ)
    (Site : BoxD D L → Type) [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)] :=
  QuasiLocalPerturbation D L Site

namespace QuasiLocalPerturbation

variable {D L : ℕ} {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
variable (V : QuasiLocalPerturbation D L Site)

/-- Total perturbation operator $V_{\mathrm{tot}} = \sum_{r=1}^L \sum_{A \in \mathcal{S}(r)} V_{r,A}$. -/
def totalPerturbation : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site :=
  ∑ r ∈ Finset.Icc 1 L, ∑ A ∈ boxCubes D L r, V.term r A

/-- Norm decay bound $\|V_{r,A}\| \le J \, f(r)$ for all scales $1 \le r \le L$ and cubes $A \in \mathcal{S}(r)$. -/
def SatisfiesDecayBound (J : ℝ) (f : ℕ → ℝ) : Prop :=
  ∀ r ∈ Finset.Icc 1 L, ∀ A ∈ boxCubes D L r, ‖V.term r A‖ ≤ J * f r

end QuasiLocalPerturbation

/-- A finite sum of self-adjoint continuous linear operators on a complex Hilbert space is self-adjoint. -/
lemma isSelfAdjoint_finset_sum {α : Type*} {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [CompleteSpace E] (s : Finset α) (f : α → (E →L[ℂ] E))
    (hf : ∀ a ∈ s, IsSelfAdjoint (f a)) :
    IsSelfAdjoint (∑ a ∈ s, f a) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [IsSelfAdjoint.zero]
  | @insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact (hf a (Finset.mem_insert_self a s)).add
      (ih (fun b hb => hf b (Finset.mem_insert_of_mem hb)))

/-- A real scalar multiple of a self-adjoint operator is self-adjoint. -/
lemma isSelfAdjoint_real_smul {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [CompleteSpace E] (c : ℝ) {A : E →L[ℂ] E} (hA : IsSelfAdjoint A) :
    IsSelfAdjoint ((c : ℂ) • A) := by
  rw [isSelfAdjoint_iff, star_smul, RCLike.star_def, Complex.conj_ofReal, hA.star_eq]

/-- `sys.H0` of an `IndexedCommutingProjectorHamiltonian` is self-adjoint. -/
lemma IndexedCommutingProjectorHamiltonian.isSelfAdjoint_H0 {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (sys : IndexedCommutingProjectorHamiltonian D L Site ι) :
    IsSelfAdjoint sys.H0 := by
  unfold IndexedCommutingProjectorHamiltonian.H0
  apply isSelfAdjoint_finset_sum
  intro i _
  exact isSelfAdjoint_real_smul (sys.weight i) (sys.is_projector i).isSelfAdjoint

/-- `V.totalPerturbation` of a `QuasiLocalPerturbation` is self-adjoint. -/
lemma QuasiLocalPerturbation.isSelfAdjoint_totalPerturbation {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    (V : QuasiLocalPerturbation D L Site) :
    IsSelfAdjoint V.totalPerturbation := by
  unfold QuasiLocalPerturbation.totalPerturbation
  apply isSelfAdjoint_finset_sum
  intro r _
  apply isSelfAdjoint_finset_sum
  intro A _
  exact V.is_selfAdjoint r A

/-- Order-reversing involution of `Fin n` given by `Fin.rev`. -/
def finRevEquiv (n : ℕ) : Fin n ≃ Fin n where
  toFun := Fin.rev
  invFun := Fin.rev
  left_inv := Fin.rev_rev
  right_inv := Fin.rev_rev

/-- The real eigenvalues of a self-adjoint operator $H : \mathcal{H} \to_L[\mathbb{C}] \mathcal{H}$,
    ordered in increasing sequence $\mu_0 \le \mu_1 \le \dots \le \mu_{N-1}$. -/
def sortedEigenvalues {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    (H : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site)
    (hH : IsSelfAdjoint H) :
    Fin (Module.finrank ℂ (ManyBodyHilbertSpace Site)) → ℝ :=
  let hSymm : H.toLinearMap.IsSymmetric :=
    (LinearMap.isSymmetric_iff_isSelfAdjoint H.toLinearMap).mpr
      ((ContinuousLinearMap.isSelfAdjoint_toLinearMap_iff H).mpr hH)
  fun i => hSymm.eigenvalues rfl i.rev

/-- Orthonormal basis of eigenvectors of $H$ indexed in increasing order of `sortedEigenvalues H hH`. -/
def sortedEigenbasis {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    (H : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site)
    (hH : IsSelfAdjoint H) :
    OrthonormalBasis (Fin (Module.finrank ℂ (ManyBodyHilbertSpace Site))) ℂ
      (ManyBodyHilbertSpace Site) :=
  let hSymm : H.toLinearMap.IsSymmetric :=
    (LinearMap.isSymmetric_iff_isSelfAdjoint H.toLinearMap).mpr
      ((ContinuousLinearMap.isSelfAdjoint_toLinearMap_iff H).mpr hH)
  (hSymm.eigenvectorBasis rfl).reindex (finRevEquiv _)

/-- Canonical bijection between `ManyBodyConfig Site` and `Fin (Module.finrank ℂ (ManyBodyHilbertSpace Site))`. -/
def configFinEquiv {D L : ℕ}
    (Site : BoxD D L → Type) [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)] :
    ManyBodyConfig Site ≃ Fin (Module.finrank ℂ (ManyBodyHilbertSpace Site)) :=
  (EuclideanSpace.basisFun (ManyBodyConfig Site) ℂ).toBasis.indexEquiv
    (Module.finBasis ℂ (ManyBodyHilbertSpace Site))
