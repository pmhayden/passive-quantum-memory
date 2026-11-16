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

import Defs.FlowAndFilter

/-!
# Bochner-Filtered Site Operators, Single-Cube Telescoping, and Dressed Energy Sandwiches

Defines open-box cube anchors (`anchorOfCube`, `anchorOfRegion`, `shiftDownOne`), single-cube TQO-2 telescoping approximations and shell differences (`singleCubeSupportC`, `localTelescopingApprox`, `singleCubeApproxM`, `indexedLocalTelescopingApprox`, `indexedSingleCubeApproxM`, `indexedSingleCubeDiffD`), and Bochner-filtered site operators (`IndexedCommutingProjectorHamiltonian.siteCheckOp`, `sitePerturbationOp`, `indexedFilteredSiteOp`). Formalizes low-energy band stability (`IndexedHasStableLowEnergyBand`), dressed check/Hamiltonian/ground projectors (`indexedDressedCheckOp`, `indexedDressedH0Op`, `indexedDressedGroundProj`), and the 3/4–5/4 dressed excitation energy sandwich (`SatisfiesDressedEnergySandwich`, `HasSectorFilteredQACStability`).

## References

* Part I, Section 6.3 (`subsec:qac-block-diag`), Proposition 6.4 (`prop:qac-block-diagonalization`)
* Part I, Section 7.1 (`subsec:single-cube-telescoping`), Lemma 7.1 (`lem:norm-transfer`), Proposition 7.2 (`prop:single-cube-telescoping`), Section 7.2 (`subsec:gap-bootstrap`), Theorem 7.3 (`thm:gap-bootstrap`)
* Part II, Section 5.2 (`subsec:low-temp-crossover`), Proposition 5.2 (`prop:bhm-relative-form-bound`)
* Bravyi and Hastings (2011)
-/

noncomputable section

open scoped Classical InnerProduct ComplexConjugate BigOperators
open Filter Topology Asymptotics ContinuousLinearMap MeasureTheory

/-!
## 1. Symbolic BHM Constants, Open-Box Cube Anchors, and Single-Cube Telescoping Operators
-/

/-- Symbolic side length $r_{\mathrm{elem}} = 2$ of elementary coarse-grained open-box cubes $\mathcal{S}(2)$. -/
abbrev bhmElementaryCubeSide : ℕ := 2

/-- Symbolic perturbed spectral gap lower bound $\Delta_{\mathrm{BHM}} = 1/2$ along $s \in [0, 1]$. -/
abbrev bhmPerturbedGap : ℝ := 1 / 2

/-- Symbolic bootstrap spectral gap target $\Delta_{\mathrm{boot}} = 3/4 > \Delta_{\mathrm{BHM}}$ on $s \in [0, 1]$. -/
abbrev bhmBootstrapGap : ℝ := 3 / 4

/-- Symbolic relative form-bound deviation $\varepsilon_{\mathrm{form}} = 1/4$ in the dressed energy sandwich. -/
abbrev bhmSandwichDeviation : ℝ := 1 / 4

/-- Symbolic lower coefficient $1 - \varepsilon_{\mathrm{form}} = 3/4$ of the dressed excitation energy sandwich. -/
abbrev bhmSandwichLower : ℝ := 3 / 4

/-- Symbolic upper coefficient $1 + \varepsilon_{\mathrm{form}} = 5/4$ of the dressed excitation energy sandwich. -/
abbrev bhmSandwichUpper : ℝ := 5 / 4

/-- Symbolic single-cube telescoping error factor $C_{\mathrm{tele}} = 3$ in $\|X' - M_k(u)\| \le 3\varepsilon_k$. -/
abbrev bhmTelescopingFactor : ℝ := 3

/-- Coordinatewise downward $1$-step shift $\max(0, u_i - 1)$ on the open box `BoxD D L`,
    used as the anchor of the $1$-collar `boxCube (shiftDownOne u) (k + bhmElementaryCubeSide)` around `boxCube u k`. -/
def shiftDownOne {D L : ℕ} (u : BoxD D L) : BoxD D L :=
  fun i => ⟨(u i).val - 1, Nat.sub_lt_of_lt (u i).isLt⟩

/-- Canonical anchor vertex $x_0 \in \mathrm{BoxD}\ D\ L$ chosen for a cube $A \in \mathrm{BoxCubes}\ D\ L\ r$
    so that $\mathrm{boxCube}(\mathrm{anchorOfCube}(r, A), r) = A$. -/
def anchorOfCube {D L : ℕ} [NeZero L] (r : ℕ) (A : Finset (BoxD D L)) : BoxD D L :=
  if hA : A ∈ boxCubes D L r then (Finset.mem_image.mp hA).choose else fun _ => ⟨0, NeZero.pos L⟩

/-- Canonical anchor vertex chosen for an arbitrary region $A \subseteq \mathrm{BoxD}\ D\ L$. -/
def anchorOfRegion {D L : ℕ} [NeZero L] (A : Finset (BoxD D L)) : BoxD D L :=
  if h : A.Nonempty then h.choose else fun _ => ⟨0, NeZero.pos L⟩

/-- Single-cube TQO-2 support cube $C_k(u) := \mathrm{enclosingBoxCube}(\mathrm{shiftDownOne}(u), k + 2, R_C(k + 2))$
    of the scale-$k$ local approximation $M_k(u)$ and difference $D_k(u)$ on `BoxD D L`. -/
def singleCubeSupportC {D L : ℕ} (C : ℝ) (u : BoxD D L) (k : ℕ) :
    Finset (BoxD D L) :=
  enclosingBoxCube (shiftDownOne u) (k + bhmElementaryCubeSide)
    (linearExpansionRadius C (k + bhmElementaryCubeSide))

/-- **Single-Cube Locally Block-Diagonal Approximation $M_k(u)$ (Bravyi–Hastings (2011), Section 4, Lemma 3; Part I, Section 7.1 (`subsec:single-cube-telescoping`), Equation (84) (`eq:centered-Xu-and-Mk`))**:
    For site $u \in \mathrm{BoxD}\ D\ L$ and scale $k$, projects the local conditional expectation
    $\mathbb{E}_{\mathrm{boxCube}(u, k)}(X_u')$ onto the excited complement of the TQO-2 cube $C_k(u)$:
    $$M_k(u) := (1 - P_{C_k(u)}) \, \mathbb{E}_{\mathrm{boxCube}(u, k)}(X_u') \, (1 - P_{C_k(u)}).$$ -/
def localTelescopingApprox {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    (sys : CommutingProjectorHamiltonian D L Site)
    (C : ℝ) (u : BoxD D L) (k : ℕ)
    (X_u' : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site) :
    ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site :=
  let C_k := singleCubeSupportC C u k
  (1 - sys.localGroundProj C_k) * condExp Site (boxCube u k) X_u' * (1 - sys.localGroundProj C_k)

/-- Single-cube locally block-diagonal approximation $M_k(u)$ with $M_0(u) := 0$ and
    $M_k(u) := \mathrm{localTelescopingApprox}\ \mathrm{sys}\ C\ u\ k\ X_u'$ for $k \ge 1$
    (Part I, Section 7.1 (`subsec:single-cube-telescoping`), Equation (84) (`eq:centered-Xu-and-Mk`)). -/
def singleCubeApproxM {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    (sys : CommutingProjectorHamiltonian D L Site)
    (C : ℝ) (u : BoxD D L) (k : ℕ)
    (X_u' : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site) :
    ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site :=
  if k = 0 then 0 else localTelescopingApprox sys C u k X_u'

/-- Single-cube locally block-diagonal approximation $M_k(u)$ for an `IndexedCommutingProjectorHamiltonian`. -/
def indexedLocalTelescopingApprox {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (sys : IndexedCommutingProjectorHamiltonian D L Site ι)
    (C : ℝ) (u : BoxD D L) (k : ℕ)
    (X_u' : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site) :
    ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site :=
  let C_k := singleCubeSupportC C u k
  (1 - sys.localGroundProj C_k) * condExp Site (boxCube u k) X_u' * (1 - sys.localGroundProj C_k)

/-- Single-cube approximation $M_k(u)$ ($M_0(u) = 0$) for an `IndexedCommutingProjectorHamiltonian`. -/
def indexedSingleCubeApproxM {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (sys : IndexedCommutingProjectorHamiltonian D L Site ι)
    (C : ℝ) (u : BoxD D L) (k : ℕ)
    (X_u' : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site) :
    ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site :=
  if k = 0 then 0 else indexedLocalTelescopingApprox sys C u k X_u'

/-- Single-cube telescoping difference $D_k(u) := M_k(u) - M_{k-1}(u)$ for an `IndexedCommutingProjectorHamiltonian`. -/
def indexedSingleCubeDiffD {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (sys : IndexedCommutingProjectorHamiltonian D L Site ι)
    (C : ℝ) (u : BoxD D L) (k : ℕ)
    (X_u' : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site) :
    ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site :=
  indexedSingleCubeApproxM sys C u k X_u' - indexedSingleCubeApproxM sys C u (k - 1) X_u'

/-!
## 2. Bochner-Filtered Site Operators $X_u$ (`indexedFilteredSiteOp`)
-/

/-- Site-anchored check sum $Q_{\mathrm{site}}(u) = \sum_{i \in \iota,\, \mathrm{anchor}(\mathrm{supp}(Q_i)) = u} w_i Q_i$
    for an `IndexedCommutingProjectorHamiltonian`. -/
def IndexedCommutingProjectorHamiltonian.siteCheckOp {D L : ℕ} [NeZero L]
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (sys : IndexedCommutingProjectorHamiltonian D L Site ι) (u : BoxD D L) :
    ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site :=
  ∑ i ∈ Finset.univ.filter (fun i : ι => anchorOfRegion (sys.support i) = u),
    (sys.weight i : ℂ) • sys.checkProj i

/-- Site-anchored perturbation sum $V_{\mathrm{site}}(u) = \sum_{q=1}^L \sum_{A \in \mathcal{S}(q),\, \mathrm{anchor}(A) = u} V_{q, A}$. -/
def sitePerturbationOp {D L : ℕ} [NeZero L]
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    (V : QuasiLocalPerturbation D L Site) (u : BoxD D L) :
    ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site :=
  ∑ q ∈ Finset.Icc 1 L,
    ∑ A ∈ (boxCubes D L q).filter (fun A => anchorOfCube q A = u), V.term q A

/-- **Bochner-Filtered Site Operator $X_u$ (`indexedFilteredSiteOp`)** for an `IndexedCommutingProjectorHamiltonian`. -/
def indexedFilteredSiteOp {D L : ℕ} [NeZero L]
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (sys : IndexedCommutingProjectorHamiltonian D L Site ι)
    (V : QuasiLocalPerturbation D L Site)
    (U : unitary (ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site))
    (w : ℝ → ℂ)
    (u : BoxD D L) :
    ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site :=
  let H' := U.1† * (sys.H0 + V.totalPerturbation) * U.1
  bochnerFilteredOp H' w (U.1† * sitePerturbationOp V u * U.1) +
    (bochnerFilteredOp H' w (U.1† * sys.siteCheckOp u * U.1) - sys.siteCheckOp u)

/-!
## 3. Low-Energy Band and Spectral Gap Stability (`IndexedHasStableLowEnergyBand`)
-/

/-- **Spectral Gap Stability and Ground-State Band Splitting (`IndexedHasStableLowEnergyBand`)**
    for an `IndexedCommutingProjectorHamiltonian`. -/
def IndexedHasStableLowEnergyBand {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (sys : IndexedCommutingProjectorHamiltonian D L Site ι)
    (V : QuasiLocalPerturbation D L Site)
    (Δ_gap δ_split : ℝ) : Prop :=
  let H := sys.H0 + V.totalPerturbation
  let d_gs := sys.groundDegeneracy
  ∃ (hH : IsSelfAdjoint H) (E_low : Submodule ℂ (ManyBodyHilbertSpace Site)) (E0 : ℝ),
    Module.finrank ℂ E_low = d_gs ∧
    (∀ ψ ∈ E_low, H ψ ∈ E_low) ∧
    (∀ ψ ∈ E_low,
      E0 * ‖ψ‖ ^ 2 ≤ RCLike.re (inner ℂ ψ (H ψ)) ∧
      RCLike.re (inner ℂ ψ (H ψ)) ≤ (E0 + δ_split) * ‖ψ‖ ^ 2) ∧
    (∀ ψ ∈ E_lowᗮ,
      (E0 + δ_split + Δ_gap) * ‖ψ‖ ^ 2 ≤ RCLike.re (inner ℂ ψ (H ψ))) ∧
    (∀ i j : Fin (Module.finrank ℂ (ManyBodyHilbertSpace Site)),
      i.1 < d_gs → j.1 < d_gs →
        |sortedEigenvalues H hH i - sortedEigenvalues H hH j| ≤ δ_split) ∧
    (∀ i j : Fin (Module.finrank ℂ (ManyBodyHilbertSpace Site)),
      i.1 < d_gs → d_gs ≤ j.1 →
        sortedEigenvalues H hH j - sortedEigenvalues H hH i ≥ Δ_gap)

/-!
## 4. Dressed Checks, Excitation Energy Sandwich, and Sector-Filtered QAC Stability
-/

/-- Dressed check projector $\widetilde{Q}_i := U Q_i U^\dagger$ for `IndexedCommutingProjectorHamiltonian`. -/
def indexedDressedCheckOp {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (sys : IndexedCommutingProjectorHamiltonian D L Site ι)
    (U : unitary (ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site))
    (i : ι) :
    ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site :=
  U.1 * sys.checkProj i * U.1†

/-- Dressed unperturbed Hamiltonian $\widetilde{H}_0 := U H_0 U^\dagger$ for `IndexedCommutingProjectorHamiltonian`. -/
def indexedDressedH0Op {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (sys : IndexedCommutingProjectorHamiltonian D L Site ι)
    (U : unitary (ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site)) :
    ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site :=
  U.1 * sys.H0 * U.1†

/-- Dressed ground-space projector $\widetilde{P}_0 := U P_0 U^\dagger$ for `IndexedCommutingProjectorHamiltonian`. -/
def indexedDressedGroundProj {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (sys : IndexedCommutingProjectorHamiltonian D L Site ι)
    (U : unitary (ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site)) :
    ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site :=
  U.1 * sys.P0 * U.1†

/-- **The $\frac{3}{4}$–$\frac{5}{4}$ Dressed Excitation Energy Sandwich (`SatisfiesDressedEnergySandwich`; Part I, Theorem 7.4 (`thm:zero-temp-dressed-memory`), Equation (95) (`eq:dressed-energy-sandwich`); Part II, Proposition 5.2 (`prop:bhm-relative-form-bound`), Equation (82) (`eq:bhm-relative-form-sandwich`))**:
    For every excited state $\phi \in \ker(\widetilde{P}_0)$, the shifted perturbed Hamiltonian
    $(H_0 + V_{\mathrm{tot}}) - c_{\mathrm{shift}} I$ is form-bounded above and below by the dressed
    unperturbed Hamiltonian $\widetilde{H}_0 = U H_0 U^\dagger$:
    $$\frac{3}{4}\langle \phi, \widetilde{H}_0 \phi \rangle - \frac{1}{2} \delta_{\mathrm{split}} \|\phi\|^2
      \le \langle \phi, ((H_0 + V_{\mathrm{tot}}) - c_{\mathrm{shift}} I)\phi \rangle
      \le \frac{5}{4}\langle \phi, \widetilde{H}_0 \phi \rangle + \frac{1}{2} \delta_{\mathrm{split}} \|\phi\|^2.$$ -/
def SatisfiesDressedEnergySandwich {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (sys : IndexedCommutingProjectorHamiltonian D L Site ι)
    (V : QuasiLocalPerturbation D L Site)
    (U : unitary (ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site))
    (c_shift δ_split : ℝ) : Prop :=
  let H := sys.H0 + V.totalPerturbation
  let P_tilde := indexedDressedGroundProj sys U
  let H0_tilde := indexedDressedH0Op sys U
  ∀ ϕ : ManyBodyHilbertSpace Site,
    P_tilde ϕ = 0 →
      bhmSandwichLower * RCLike.re (inner ℂ ϕ (H0_tilde ϕ)) -
          bhmPerturbedGap * δ_split * ‖ϕ‖ ^ 2 ≤
        RCLike.re (inner ℂ ϕ ((H - (c_shift : ℂ) • 1) ϕ)) ∧
      RCLike.re (inner ℂ ϕ ((H - (c_shift : ℂ) • 1) ϕ)) ≤
        bhmSandwichUpper * RCLike.re (inner ℂ ϕ (H0_tilde ϕ)) +
          bhmPerturbedGap * δ_split * ‖ϕ‖ ^ 2

/-- **Sector-Filtered QAC Stability Package (`HasSectorFilteredQACStability`)**:
    Combines `IndexedHasStableLowEnergyBand sys V bhmPerturbedGap δ_split` with the existence of a QAC
    unitary $U$ and ground-energy shift $c_{\mathrm{shift}}$ satisfying `SatisfiesDressedEnergySandwich`. -/
def HasSectorFilteredQACStability {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (sys : IndexedCommutingProjectorHamiltonian D L Site ι)
    (V : QuasiLocalPerturbation D L Site)
    (δ_split : ℝ) : Prop :=
  IndexedHasStableLowEnergyBand sys V bhmPerturbedGap δ_split ∧
  ∃ (U : unitary (ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site)) (c_shift : ℝ),
    Commute (U.1† * (sys.H0 + V.totalPerturbation) * U.1) sys.P0 ∧
    SatisfiesDressedEnergySandwich sys V U c_shift δ_split
