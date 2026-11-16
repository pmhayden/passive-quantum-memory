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

import Defs.LocalHamiltonian
import Mathlib.Analysis.Asymptotics.SuperpolynomialDecay
import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Order

/-!
# Superpolynomial Decay Class, Tail Profiles, and Local Lattice Hamiltonians

Defines the non-negative superpolynomial decay predicate `IsSuperpolynomialDecay` and the Bravyi–Hastings locally block-diagonalized tail profile `fTilde`. Packages Hermitian local lattice Hamiltonians (`LatticeHamiltonian`) on `BoxD D L` with total Hamiltonian `LatticeHamiltonian.totalHamiltonian`, the Hastings–Koma polynomial interaction constant (`LatticeHamiltonian.s1`), and interpolated Hamiltonians (`interpolatedHamiltonianOp`).

## References

* Part I, Section 6.1 (`subsec:dsuper-banach`), Definition 6.1 (`def:banach-quasilocal`), Lemma 6.2 (`lem:dsuper-closure`)
* Part II, Section 2 (`subsec:setup`), Definition 2.3 (`def:perturbation-class`), Lemma 2.4 (`lem:D-super-closure`)
-/

noncomputable section

open scoped Classical InnerProduct ComplexConjugate BigOperators
open Filter Topology Asymptotics ContinuousLinearMap

/-!
## 1. Superpolynomial Decay Class $\mathcal{D}_{\mathrm{super}}$ and Tail Envelopes
-/

/-- A profile $f : \mathbb{N} \to \mathbb{R}$ belongs to the non-negative superpolynomial decay class
    $\mathcal{D}_{\mathrm{super}}$ if $f(r) \ge 0$ for all $r \in \mathbb{N}$ and
    $\lim_{r \to \infty} r^n f(r) = 0$ for every $n \in \mathbb{N}$. -/
def IsSuperpolynomialDecay (f : ℕ → ℝ) : Prop :=
  (∀ r : ℕ, 0 ≤ f r) ∧ SuperpolynomialDecay atTop (fun r : ℕ => (r : ℝ)) f

/-- The effective locally block-diagonalized tail decay function $\tilde{f}(r)$ from Bravyi–Hastings (2011):
    $$\tilde{f}(r) := r \sum_{q > \frac{r - 3}{2C} - 3} f(q).$$ -/
def fTilde (C : ℝ) (f : ℕ → ℝ) (r : ℕ) : ℝ :=
  (r : ℝ) * ∑' q : ℕ, if (q : ℝ) > ((r : ℝ) - 3) / (2 * C) - 3 then f q else 0

/-!
## 2. Region Diameter and Hastings–Koma Local Lattice Hamiltonians on `BoxD D L`
-/

/-- $\ell_\infty$ diameter $\mathrm{diam}(Z) = \max_{x, y \in Z} \mathrm{boxDist}(x, y)$ of a region $Z \subseteq \mathrm{BoxD}\ D\ L$. -/
def regionDiam {D L : ℕ} (Z : Finset (BoxD D L)) : ℕ :=
  (Z ×ˢ Z).sup (fun p => boxDist p.1 p.2)

/-- A local lattice Hamiltonian $H = \sum_{Z \subseteq \Lambda_L} h_Z$ on the open box `BoxD D L`
    composed of Hermitian local interaction terms $h_Z$ supported on finite subsets $Z \subseteq \Lambda_L$
    (Hastings–Koma 2005, Equation (2.1)). -/
structure LatticeHamiltonian (D L : ℕ)
    (Site : BoxD D L → Type) [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)] where
  /-- Local interaction term $h_Z$ for each subset $Z \subseteq \mathrm{BoxD}\ D\ L$. -/
  h : Finset (BoxD D L) → (ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site)
  /-- Every interaction term $h_Z$ is Hermitian ($h_Z^\dagger = h_Z$). -/
  is_selfAdjoint : ∀ Z : Finset (BoxD D L), IsSelfAdjoint (h Z)
  /-- Every interaction term $h_Z$ is supported on $Z$. -/
  is_supported : ∀ Z : Finset (BoxD D L), IsSupportedOn Site Z (h Z)

namespace LatticeHamiltonian

variable {D L : ℕ} {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
variable (H : LatticeHamiltonian D L Site)

/-- The total Hamiltonian $H_{\Lambda_L} = \sum_{Z \subseteq \mathrm{BoxD}\ D\ L} h_Z$. -/
def totalHamiltonian : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site :=
  ∑ Z : Finset (BoxD D L), H.h Z

/-- `H.totalHamiltonian` is self-adjoint. -/
lemma isSelfAdjoint_totalHamiltonian : IsSelfAdjoint H.totalHamiltonian := by
  unfold totalHamiltonian
  exact isSelfAdjoint_finset_sum Finset.univ H.h (fun Z _ => H.is_selfAdjoint Z)

/-- The Hastings–Koma volume-weighted polynomial interaction constant $s_1(\eta)$ on `BoxD D L`:
    $$s_1(\eta) := \max_{x \in \Lambda_L} \sum_{Z \ni x} \|h_Z\| \, |Z| \, (1 + \mathrm{diam}(Z))^\eta.$$ -/
def s1 [NeZero D] [NeZero L] (η : ℝ) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty (fun x : BoxD D L =>
    ∑ Z ∈ Finset.univ.filter (fun Z : Finset (BoxD D L) => x ∈ Z),
      ‖H.h Z‖ * (Z.card : ℝ) * (1 + (regionDiam Z : ℝ)) ^ η)

end LatticeHamiltonian

/-- Interpolated Hamiltonian operator $H(s) = H_0 + s V_{\mathrm{tot}}$ at parameter $s \in \mathbb{R}$
    for an `IndexedCommutingProjectorHamiltonian` and a `QuasiLocalPerturbation`. -/
def interpolatedHamiltonianOp {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (sys : IndexedCommutingProjectorHamiltonian D L Site ι)
    (V : QuasiLocalPerturbation D L Site) (s : ℝ) :
    ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site :=
  sys.H0 + (s : ℂ) • V.totalPerturbation

/-- The sum of two self-adjoint continuous linear operators on a complex Hilbert space is self-adjoint. -/
lemma isSelfAdjoint_add_clm {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [CompleteSpace E] {A B : E →L[ℂ] E} (hA : IsSelfAdjoint A) (hB : IsSelfAdjoint B) :
    IsSelfAdjoint (A + B) :=
  hA.add hB
