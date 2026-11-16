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

import Proofs.DirectWorldlineCluster.ScaleSplitAndDiagonalPeeling

/-!
# Native-Scale Worldline Jump Monomers, Polymers, and Ursell Cluster Footprints

Defines native-scale worldline jump monomers (`WorldlineJumpMonomer`), polymers (`WorldlineDysonPolymer`, `IsValidWorldlinePolymer`), ordered Dyson time simplices (`InOrderedDysonSimplex`), and Ursell clusters (`WorldlineUrsellCluster`, `IsValidWorldlineUrsellCluster`). Establishes RCA-1 spanning-surface collar containment (`worldline_polymer_rca1_spanning_surface_collar_containment`) and Ursell spanning-surface locality (`worldline_ursell_spanning_surface_collar_locality`).

## References

* Part II, Section 3.5 (`subsec:worldline-expansion`), Lemma 3.9 (`lem:worldline-factorization-time-reversal`)
* Part II, Section 3.5 (`subsec:worldline-expansion`), Proposition 3.10 (`prop:tube-local-ursell-erasure`)
-/

noncomputable section

open scoped Classical BigOperators InnerProduct ComplexConjugate
open Filter Topology Asymptotics ContinuousLinearMap KMSPinchedGibbs PerturbedThermalBarrier
open SpacetimeWorldlineKP

set_option linter.unusedVariables false
set_option maxRecDepth 200000
set_option maxHeartbeats 1600000

namespace DirectWorldlineCluster

local notation "SiteCSS[" L ", " q_code "]" => UniformSite3D L (CodeSlotConfig q_code)
local notation "ℋ_CSS[" L ", " q_code "]" => ManyBodyHilbertSpace (SiteCSS[L, q_code])
local notation "ℬ_CSS[" L ", " q_code "]" => ℋ_CSS[L, q_code] →L[ℂ] ℋ_CSS[L, q_code]
local notation "IdxCSS[" L ", " q_code ", " m_max "]" => StaticCSSCheckIdx L q_code m_max
local notation "SysCSS[" L ", " q_code ", " m_max "]" =>
  IndexedCommutingProjectorHamiltonian 3 L (SiteCSS[L, q_code]) (IdxCSS[L, q_code, m_max])

/-- Active scale-cube pairs `(r, A)` at cutoff `R_cut` (`1 ≤ r ≤ min R_cut L`, `A ∈ BoxCubes 3 L r`; Part II, Equation `eq:H-short-split-def`). -/
def worldlineScaleCubeFinset (L R_cut : ℕ) : Finset (ℕ × Finset (Box3D L)) :=
  (Finset.Icc 1 (min R_cut L)).biUnion (fun r => (boxCubes 3 L r).image (fun A => (r, A)))

/-- Off-diagonal Pauli jump monomer `ξ = ((r_ξ, A_ξ), (a_ξ, b_ξ))` (Part II, Equation `eq:local-pauli-jump-xi`). -/
abbrev WorldlineJumpMonomer (L q_code : ℕ) : Type :=
  (ℕ × Finset (Box3D L)) ×
    ((BoxSlot3D L q_code → ZMod 2) × (BoxSlot3D L q_code → ZMod 2))

/-- Weyl–Pauli jump operator `P_ξ = Z(a_ξ) X(b_ξ)` of a jump monomer `ξ`. -/
def worldlineJumpOp {L q_code : ℕ} (ξ : WorldlineJumpMonomer L q_code) : ℬ_CSS[L, q_code] :=
  weylPauliZ ξ.2.1 * weylPauliX ξ.2.2

/-- Normalized Hilbert–Schmidt Pauli expansion coefficient `v_ξ` (Part II, Equation `eq:local-pauli-jump-xi`). -/
def worldlineJumpAmplitude {L q_code m_max : ℕ}
    (sys : SysCSS[L, q_code, m_max]) (V : QuasiLocalPerturbation 3 L (SiteCSS[L, q_code]))
    (ξ : WorldlineJumpMonomer L q_code) : ℂ :=
  let A_op := (worldlineJumpOp ξ)† * pauliOffDiagonalTerm sys V ξ.1.1 ξ.1.2
  ((hilbertTrace A_op : ℂ) - Complex.I * (hilbertTrace (Complex.I • A_op) : ℂ)) /
    (Fintype.card (ManyBodyConfig (SiteCSS[L, q_code])) : ℂ)

/-- Continuous-time Mayer–Dyson worldline polymer `γ = (jumps, mayerCubes)` (Part II, Lemma 3.9 (`lem:worldline-factorization-time-reversal`)). -/
abbrev WorldlineDysonPolymer (L q_code : ℕ) : Type :=
  List (WorldlineJumpMonomer L q_code) × Finset (ℕ × Finset (Box3D L))

/-- Monomer scale-cube support `{(r_x, A_x) : x ∈ γ}` of a worldline polymer `γ`. -/
def worldlinePolymerMonomers {L q_code : ℕ} (γ : WorldlineDysonPolymer L q_code) :
    Finset (ℕ × Finset (Box3D L)) :=
  (γ.1.map Prod.fst).toFinset ∪ γ.2

/-- Native check collar support `C̄(γ) = ⋃_{(r, A) ∈ γ} C(A^+)` (Part II, Lemma 3.9 (`lem:worldline-factorization-time-reversal`)). -/
def worldlinePolymerNativeCollar {L q_code m_max : ℕ} [NeZero L]
    (sys : SysCSS[L, q_code, m_max]) (C_RCA : ℝ) (γ : WorldlineDysonPolymer L q_code) :
    Finset (IdxCSS[L, q_code, m_max]) :=
  nativeCollarSupport (fun p : ℕ × Finset (Box3D L) => rcaCollarChecks sys C_RCA p.1 p.2) (worldlinePolymerMonomers γ)

/-- Union of monomer cubes `⋃_{(r, A) ∈ worldlinePolymerMonomers γ} A` (Part II, Lemma 3.9(ii) (`lem:worldline-factorization-time-reversal`)). -/
def worldlinePolymerCubeUnion {L q_code : ℕ} (γ : WorldlineDysonPolymer L q_code) : Finset (Box3D L) :=
  (worldlinePolymerMonomers γ).biUnion Prod.snd

/-- Predicate that `worldlinePolymerCubeUnion γ` is contained in a lattice cube `boxCube x0 r` (Part II, Lemma 3.9(ii) (`lem:worldline-factorization-time-reversal`)). -/
def HasEnclosingPolymerBall {L q_code : ℕ} [NeZero L] (γ : WorldlineDysonPolymer L q_code) (r : ℕ) : Prop :=
  ∃ x0 : Box3D L, worldlinePolymerCubeUnion γ ⊆ boxCube x0 r

/-- Enclosing cube diameter `diam(B(γ))` of `worldlinePolymerCubeUnion γ` (Part II, Lemma 3.9(ii) (`lem:worldline-factorization-time-reversal`)). -/
def worldlinePolymerDiameter {L q_code : ℕ} [NeZero L] (γ : WorldlineDysonPolymer L q_code) : ℕ :=
  if h : ∃ r ≤ L, 1 ≤ r ∧ HasEnclosingPolymerBall γ r then Nat.find h else L

/-- Smallest enclosing lattice cube `B(γ) ⊆ Λ` containing `worldlinePolymerCubeUnion γ` (Part II, Lemma 3.9(ii) (`lem:worldline-factorization-time-reversal`)). -/
def worldlinePolymerBoundingBox {L q_code : ℕ} [NeZero L] (γ : WorldlineDysonPolymer L q_code) : Finset (Box3D L) :=
  if h : HasEnclosingPolymerBall γ (worldlinePolymerDiameter γ) then
    boxCube (Classical.choose h) (worldlinePolymerDiameter γ)
  else Finset.univ

/-- Enclosing-ball check collar `C(B(γ)^+)` (Part II, Lemma 3.9(ii) (`lem:worldline-factorization-time-reversal`)). -/
def worldlinePolymerBoundingBoxCollar {L q_code m_max : ℕ} [NeZero L]
    (sys : SysCSS[L, q_code, m_max]) (C_RCA : ℝ) (γ : WorldlineDysonPolymer L q_code) :
    Finset (IdxCSS[L, q_code, m_max]) :=
  rcaCollarChecks sys C_RCA (worldlinePolymerDiameter γ) (worldlinePolymerBoundingBox γ)

/-- Net loop X-bitstring `⨁_{j=1}^m a_{ξ_j}` of a worldline polymer `γ`. -/
def worldlinePolymerLoopX {L q_code : ℕ} (γ : WorldlineDysonPolymer L q_code) : BoxSlot3D L q_code → ZMod 2 :=
  (γ.1.map (fun ξ => ξ.2.1)).sum

/-- Net loop Z-bitstring `⨁_{j=1}^m b_{ξ_j}` of a worldline polymer `γ`. -/
def worldlinePolymerLoopZ {L q_code : ℕ} (γ : WorldlineDysonPolymer L q_code) : BoxSlot3D L q_code → ZMod 2 :=
  (γ.1.map (fun ξ => ξ.2.2)).sum

/-- Ordered product `P(γ) = P_{ξ_m} ⋯ P_{ξ_1}` of jump operators along a worldline polymer `γ`
    (Part II, Section 3.5 (`subsec:worldline-expansion`), Lemma 3.9 (`lem:worldline-factorization-time-reversal`)). -/
def worldlinePolymerLoopOp {L q_code : ℕ} (γ : WorldlineDysonPolymer L q_code) : ℬ_CSS[L, q_code] :=
  (γ.1.reverse.map worldlineJumpOp).prod

/-- Syndrome-shift jump block operator `B_{r,A}^{(δ)} = ∑_{σ ∈ V_valid} Π_{σ ⊕ δ} V_{r,A}^{off} Π_σ`
    (Part II, Proposition 3.4(iii) (`prop:pauli-diag-off`), Equation `eq:V-off-jump-decomp`). -/
def worldlineSyndromeShiftBlockOp {L q_code r_0 m_max : ℕ}
    (D_field : Box3D L → LocalCSSDescriptor q_code r_0 m_max)
    (sys : SysCSS[L, q_code, m_max]) (V : QuasiLocalPerturbation 3 L (SiteCSS[L, q_code]))
    (ξ : WorldlineJumpMonomer L q_code) : ℬ_CSS[L, q_code] :=
  let δ := staticCSSPauliFlip D_field ξ.2.1 ξ.2.2
  ∑ σ ∈ realizableSyndromes D_field,
    sys.syndromeProjector (syndromeXor δ σ) * pauliOffDiagonalTerm sys V ξ.1.1 ξ.1.2 * sys.syndromeProjector σ

/-- Ordered product of syndrome-shift jump block operators `∏_{j=m}^1 B_{r_j, A_j}^{(δ_j)}` along `γ`
    (Part II, Proposition 3.4(iii) (`prop:pauli-diag-off`), Equation `eq:V-off-jump-decomp`,
    and Section 3.5 (`subsec:worldline-expansion`), Equation `eq:local-pauli-jump-xi`). -/
def worldlinePolymerWeightedLoopOp {L q_code r_0 m_max : ℕ}
    (D_field : Box3D L → LocalCSSDescriptor q_code r_0 m_max)
    (sys : SysCSS[L, q_code, m_max]) (V : QuasiLocalPerturbation 3 L (SiteCSS[L, q_code]))
    (γ : WorldlineDysonPolymer L q_code) : ℬ_CSS[L, q_code] :=
  (γ.1.reverse.map (worldlineSyndromeShiftBlockOp D_field sys V)).prod

/-- A Weyl–Pauli bitstring pair `(a, b)` on `BoxSlot3D L q_code`. -/
abbrev PauliBitstringPair (L q_code : ℕ) : Type :=
  (BoxSlot3D L q_code → ZMod 2) × (BoxSlot3D L q_code → ZMod 2)

/-- Finite set of all syndrome-closed Weyl–Pauli bitstring pairs `(a, b)` (`X(a) Z(b)` commutes
    with all CSS check generators `S_u`, `staticCSSPauliFlip D_field a b = false`). -/
def syndromeClosedPauliFinset {L q_code r_0 m_max : ℕ}
    (D_field : Box3D L → LocalCSSDescriptor q_code r_0 m_max) :
    Finset (PauliBitstringPair L q_code) :=
  Finset.univ.filter (fun ν => staticCSSPauliFlip D_field ν.1 ν.2 = fun _ => false)

/-- Symplectic commutation character `(-1)^{⟨ν, μ⟩}` between two Weyl–Pauli bitstring pairs
    `ν, μ : PauliBitstringPair L q_code`. -/
def symplecticPauliSign {L q_code : ℕ}
    (ν μ : PauliBitstringPair L q_code) : ℝ :=
  if (Finset.univ.filter (fun q : BoxSlot3D L q_code =>
      ν.1 q * μ.2 q + ν.2 q * μ.1 q ≠ 0)).card % 2 = 1 then -1 else 1

/-- Native-scale worldline spanning-surface scale calibration
    (Part II, Definition 2.3 (`def:perturbation-class`), Proposition 3.4(iii) (`prop:pauli-diag-off`),
    and Proposition 3.10 (`prop:tube-local-ursell-erasure`)):
    `4 * (Nat.ceil C_RCA + 1) * (r_0 + 1) * R_cut ≤ L_star ∧ 1 + 4 * (r_0 : ℝ) ≤ C_RCA ∧ (Fintype.card (Box3D L) : ℝ) ≤ Real.exp (L_star : ℝ)`. -/
def SatisfiesWorldlineScaleCalibration (L L_star R_cut r_0 : ℕ) (C_RCA : ℝ) : Prop :=
  4 * (Nat.ceil C_RCA + 1) * (r_0 + 1) * R_cut ≤ L_star ∧
  1 + 4 * (r_0 : ℝ) ≤ C_RCA ∧
  (Fintype.card (Box3D L) : ℝ) ≤ Real.exp (L_star : ℝ)

/-- Native-collar overlap adjacency on scale-cube pairs `(r, A)`
    (Part II, Section 3.5 (`subsec:worldline-expansion`), Lemma 3.9 (`lem:worldline-factorization-time-reversal`)). -/
def ScaleCubeCollarOverlap {L q_code m_max : ℕ} [NeZero L]
    (sys : SysCSS[L, q_code, m_max]) (C_RCA : ℝ)
    (p q : ℕ × Finset (Box3D L)) : Prop :=
  p ≠ q ∧ ¬Disjoint (rcaCollarChecks sys C_RCA p.1 p.2) (rcaCollarChecks sys C_RCA q.1 q.2)

/-- Canonical Weyl–Pauli jump bitstring representative `(a_δ, b_δ)` supported on cube `A`
    for a local syndrome shift `δ : IdxCSS[L, q_code, m_max] → Bool`
    (Part II, Proposition 3.4(iii) (`prop:pauli-diag-off`), Equation `eq:V-off-jump-decomp`):
    groups off-diagonal Pauli terms on `A` by their syndrome shift `δ` on the incident checks
    `I(A) ⊆ C(A^+)`, ensuring at most `2 ^ |C(A^+)| ≤ 2 ^ kpCollarMaxCheckCard` canonical jump
    monomers per scale-cube `(r, A)` independently of `q_code`. -/
def canonicalJumpPauliRep {L q_code r_0 m_max : ℕ}
    (D_field : Box3D L → LocalCSSDescriptor q_code r_0 m_max)
    (A : Finset (Box3D L)) (δ : IdxCSS[L, q_code, m_max] → Bool) :
    (BoxSlot3D L q_code → ZMod 2) × (BoxSlot3D L q_code → ZMod 2) :=
  if h : ∃ p : (BoxSlot3D L q_code → ZMod 2) × (BoxSlot3D L q_code → ZMod 2),
      (∀ slot : BoxSlot3D L q_code, p.1 slot ≠ 0 ∨ p.2 slot ≠ 0 → slot.1 ∈ A) ∧
      staticCSSPauliFlip D_field p.1 p.2 = δ then
    Classical.choose h
  else (0, 0)

/-- Canonical Hermitian Weyl–Pauli operator `L_{(a,b)}` (`I` phase when `∑ p, a p * b p ≠ 0`;
    Part II, Lemma 3.9(i) (`lem:worldline-factorization-time-reversal`)). -/
def hermitianPauliZX {L q_code : ℕ}
    (a b : BoxSlot3D L q_code → ZMod 2) : ℬ_CSS[L, q_code] :=
  if (∑ p : BoxSlot3D L q_code, a p * b p) = 0 then
    weylPauliZ a * weylPauliX b
  else
    Complex.I • (weylPauliZ a * weylPauliX b)

/-- Spanning-surface syndrome parity sign `(-1)^{|α ∩ σ|}`
    (Part II, Lemma 3.9(ii) (`lem:worldline-factorization-time-reversal`), Equation `eq:P-gamma-spanning-surface`). -/
def spanningSurfaceSign {L q_code m_max : ℕ}
    (α : Finset (IdxCSS[L, q_code, m_max]))
    (σ : IdxCSS[L, q_code, m_max] → Bool) : ℝ :=
  if (α.filter (fun c => σ c = true)).card % 2 = 1 then -1 else 1

/-- Predicate stating that syndrome-closed Pauli representative `μ ∈ syndromeClosedPauliFinset D_field`
    and check subset `α ⊆ C` realize the stabilizer decomposition
    `P(γ) = ω_loop(γ) L_μ ∏_{u ∈ α} S_u` on all realizable syndrome sectors
    (Part II, Lemma 2.8(i)–(ii) (`lem:worldline-factorization-time-reversal`), Equation `eq:P-gamma-spanning-surface`).
    Both the real and imaginary trace components (`L_op` and `Complex.I • L_op`) are tracked with
    non-vanishing vacuum expectation so skew-Hermitian loops (`ω_loop(γ) = ±i`) and non-trivial
    logical cosets (`μ ≠ (0, 0)`) are never vacuously satisfied by `0 = 0`. -/
def IsSpanningCheckSurfaceForPolymer {L q_code r_0 m_max : ℕ}
    (D_field : Box3D L → LocalCSSDescriptor q_code r_0 m_max)
    (sys : SysCSS[L, q_code, m_max])
    (γ : WorldlineDysonPolymer L q_code)
    (μ : PauliBitstringPair L q_code) (α : Finset (IdxCSS[L, q_code, m_max])) : Prop :=
  let L_op := (hermitianPauliZX μ.1 μ.2)† * worldlinePolymerLoopOp γ
  (hilbertTrace (sys.P0 * L_op) ≠ 0 ∨ hilbertTrace (sys.P0 * (Complex.I • L_op)) ≠ 0) ∧
  ∀ σ ∈ realizableSyndromes D_field,
    hilbertTrace (sys.syndromeProjector σ * L_op) =
      spanningSurfaceSign α σ * hilbertTrace (sys.P0 * L_op) ∧
    hilbertTrace (sys.syndromeProjector σ * (Complex.I • L_op)) =
      spanningSurfaceSign α σ * hilbertTrace (sys.P0 * (Complex.I • L_op))

/-- Validity predicate for a connected worldline polymer `γ = (jumps, Θ)` at cutoff `R_cut`
    (Part II, Lemma 3.9 (`lem:worldline-factorization-time-reversal`) and
    Proposition 3.10 (`prop:tube-local-ursell-erasure`)):
    1. Every monomer scale-cube `(r, A)` belongs to `worldlineScaleCubeFinset L R_cut`.
    2. Every jump `ξ = ((r, A), (a, b)) ∈ γ.1` is supported on `A`, shifts the syndrome non-trivially,
       and uses the canonical Pauli representative `canonicalJumpPauliRep` of its syndrome shift on `A`.
    3. `2 ≤ γ.1.length` and the net loop Pauli operator is syndrome-closed (`staticCSSPauliFlip = false`).
    4. The monomer scale-cube set `worldlinePolymerMonomers γ` is connected under native-collar overlap. -/
def IsValidWorldlinePolymer {L q_code r_0 m_max : ℕ} [NeZero L]
    (D_field : Box3D L → LocalCSSDescriptor q_code r_0 m_max)
    (sys : SysCSS[L, q_code, m_max]) (C_RCA : ℝ) (R_cut : ℕ)
    (γ : WorldlineDysonPolymer L q_code) : Prop :=
  (∀ p ∈ worldlinePolymerMonomers γ, p ∈ worldlineScaleCubeFinset L R_cut) ∧
  (∀ ξ ∈ γ.1,
    (∀ slot : BoxSlot3D L q_code, ξ.2.1 slot ≠ 0 ∨ ξ.2.2 slot ≠ 0 → slot.1 ∈ ξ.1.2) ∧
    staticCSSPauliFlip D_field ξ.2.1 ξ.2.2 ≠ (fun _ => false) ∧
    ξ.2 = canonicalJumpPauliRep D_field ξ.1.2 (staticCSSPauliFlip D_field ξ.2.1 ξ.2.2)) ∧
  (2 ≤ γ.1.length ∧
    staticCSSPauliFlip D_field (worldlinePolymerLoopX γ) (worldlinePolymerLoopZ γ) =
      fun _ => false) ∧
  KPIsConnectedSubgraph (ScaleCubeCollarOverlap sys C_RCA) (worldlinePolymerMonomers γ)

local instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

/-- $Z$-type bitstring generator of a CSS check `c : IdxCSS[L, q_code, m_max]`. -/
def staticCSSCheckPauliZ {L q_code r_0 m_max : ℕ}
    (D_field : Box3D L → LocalCSSDescriptor q_code r_0 m_max) :
    IdxCSS[L, q_code, m_max] → BoxSlot3D L q_code → ZMod 2
  | Sum.inl (v, s) =>
    if (D_field v).activeSlot s = false then singleSlotChain v s else 0
  | Sum.inr (Sum.inl _) => 0
  | Sum.inr (Sum.inr (v, idx)) =>
    if idx.val < (D_field v).numZChecks.val then descriptorCheckZChain D_field v idx else 0

/-- $X$-type bitstring generator of a CSS check `c : IdxCSS[L, q_code, m_max]`. -/
def staticCSSCheckPauliX {L q_code r_0 m_max : ℕ}
    (D_field : Box3D L → LocalCSSDescriptor q_code r_0 m_max) :
    IdxCSS[L, q_code, m_max] → BoxSlot3D L q_code → ZMod 2
  | Sum.inl _ => 0
  | Sum.inr (Sum.inl (v, idx)) =>
    if idx.val < (D_field v).numXChecks.val then descriptorCheckXChain D_field v idx else 0
  | Sum.inr (Sum.inr _) => 0

/-- $\mathbb{F}_2$-linear subspace of stabilizer Pauli bitstring pairs generated by all CSS check
    generators `(staticCSSCheckPauliZ D_field c, staticCSSCheckPauliX D_field c)`
    (Part II, Proposition 2.4(i)–(ii) (`prop:pauli-diag-off`)). -/
def stabilizerPauliSubmodule {L q_code r_0 m_max : ℕ}
    (D_field : Box3D L → LocalCSSDescriptor q_code r_0 m_max) :
    Submodule (ZMod 2) (PauliBitstringPair L q_code) :=
  Submodule.span (ZMod 2) (Set.range (fun c : IdxCSS[L, q_code, m_max] =>
    (staticCSSCheckPauliZ D_field c, staticCSSCheckPauliX D_field c)))

/-- Canonical $\mathbb{F}_2$-linear bare logical coset projection
    `bareLogicalProjection D_field : PauliBitstringPair L q_code →ₗ[ZMod 2] PauliBitstringPair L q_code`
    onto the chosen complementary subspace `Classical.choose (stabilizerPauliSubmodule D_field).exists_isCompl`
    along `stabilizerPauliSubmodule D_field`
    (Part II, Lemma 2.8(i)–(ii) (`lem:worldline-factorization-time-reversal`)). -/
def bareLogicalProjection {L q_code r_0 m_max : ℕ}
    (D_field : Box3D L → LocalCSSDescriptor q_code r_0 m_max) :
    PauliBitstringPair L q_code →ₗ[ZMod 2] PauliBitstringPair L q_code :=
  let S := stabilizerPauliSubmodule D_field
  let Q := Classical.choose S.exists_isCompl
  have hQ : IsCompl Q S := (Classical.choose_spec S.exists_isCompl).symm
  Q.subtype.comp (Submodule.projectionOnto Q S hQ)

/-- Canonical logical coset Pauli representative `μ(γ) ∈ syndromeClosedPauliFinset D_field`
    of a worldline polymer `γ` (Part II, Lemma 3.9(ii) (`lem:worldline-factorization-time-reversal`)). -/
def worldlinePolymerLogicalCoset {L q_code r_0 m_max : ℕ} [NeZero L]
    (D_field : Box3D L → LocalCSSDescriptor q_code r_0 m_max)
    (_sys : SysCSS[L, q_code, m_max]) (_C_RCA : ℝ)
    (γ : WorldlineDysonPolymer L q_code) : PauliBitstringPair L q_code :=
  bareLogicalProjection D_field (worldlinePolymerLoopX γ, worldlinePolymerLoopZ γ)

/-- Canonical `RCA_1` spanning check surface `α(γ)` of a worldline polymer `γ`
    (Part II, Lemma 3.9(ii) (`lem:worldline-factorization-time-reversal`), Equation `eq:P-gamma-spanning-surface`):
    selects a local spanning check surface `α ⊆ worldlinePolymerBoundingBoxCollar sys C_RCA γ` (`C(B(γ)^+)`)
    with trivial logical coset `μ = (0, 0)` whenever one exists (`diam(B(γ)) ≤ L^*`), else selects a
    global spanning check surface `α ⊆ C` with logical coset representative
    `μ = worldlinePolymerLogicalCoset D_field sys C_RCA γ` whenever one exists
    (`diam(B(γ)) > L^*`), and `∅` otherwise. -/
def worldlinePolymerSpanningSurface {L q_code r_0 m_max : ℕ} [NeZero L]
    (D_field : Box3D L → LocalCSSDescriptor q_code r_0 m_max)
    (sys : SysCSS[L, q_code, m_max]) (C_RCA : ℝ)
    (γ : WorldlineDysonPolymer L q_code) : Finset (IdxCSS[L, q_code, m_max]) :=
  if h_loc : ∃ α : Finset (IdxCSS[L, q_code, m_max]),
      α ⊆ worldlinePolymerBoundingBoxCollar sys C_RCA γ ∧
      IsSpanningCheckSurfaceForPolymer D_field sys γ (0, 0) α then
    Classical.choose h_loc
  else if h_glob : ∃ α : Finset (IdxCSS[L, q_code, m_max]),
      IsSpanningCheckSurfaceForPolymer D_field sys γ
        (worldlinePolymerLogicalCoset D_field sys C_RCA γ) α then
    Classical.choose h_glob
  else ∅

/-- Canonical realizable syndrome extension `σ_rep ∈ realizableSyndromes D_field` of a local collar
    syndrome configuration `σ₀` on a check subset `S`: selects a realizable syndrome agreeing with
    `σ₀` on `S` whenever one exists, and `fun _ => false` otherwise. -/
def canonicalCollarRealizableSyndrome {L q_code r_0 m_max : ℕ}
    (D_field : Box3D L → LocalCSSDescriptor q_code r_0 m_max)
    (S : Finset (IdxCSS[L, q_code, m_max]))
    (σ₀ : IdxCSS[L, q_code, m_max] → Bool) : IdxCSS[L, q_code, m_max] → Bool :=
  if h : ∃ σ ∈ realizableSyndromes D_field, ∀ c ∈ S, σ c = σ₀ c then
    Classical.choose h
  else
    fun _ => false

/-- Normalized sector trace amplitude of the ordered product of weighted jump
    operators along `γ` (Part II, Lemma 2.8(i)–(ii) (`lem:worldline-factorization-time-reversal`)), evaluated on the
    canonical realizable syndrome representative `σ_rep` of the native collar configuration
    `σ₀ = σ|_{C̄(γ)}` after factoring out `(-1)^{|α(γ) ∩ σ_rep|}`. -/
def worldlinePolymerLoopAmplitude {L q_code r_0 m_max : ℕ} [NeZero L]
    (D_field : Box3D L → LocalCSSDescriptor q_code r_0 m_max)
    (sys : SysCSS[L, q_code, m_max]) (C_RCA : ℝ)
    (V : QuasiLocalPerturbation 3 L (SiteCSS[L, q_code]))
    (γ : WorldlineDysonPolymer L q_code)
    (σ₀ : IdxCSS[L, q_code, m_max] → Bool) : ℝ :=
  let σ_rep := canonicalCollarRealizableSyndrome D_field
    (worldlinePolymerNativeCollar sys C_RCA γ) σ₀
  let μ := worldlinePolymerLogicalCoset D_field sys C_RCA γ
  let B_prod := (hermitianPauliZX μ.1 μ.2)† * worldlinePolymerWeightedLoopOp D_field sys V γ
  spanningSurfaceSign (worldlinePolymerSpanningSurface D_field sys C_RCA γ) σ_rep *
    hilbertTrace (sys.syndromeProjector σ_rep * B_prod) /
    hilbertTrace (sys.syndromeProjector σ_rep)

/-- Restriction of a syndrome `σ` to a check subset `S`, setting checks outside `S` to `false`. -/
def restrictSyndromeToCollar {L q_code m_max : ℕ}
    (S : Finset (IdxCSS[L, q_code, m_max]))
    (σ : IdxCSS[L, q_code, m_max] → Bool) : IdxCSS[L, q_code, m_max] → Bool :=
  fun c => if c ∈ S then σ c else false

/-- Intermediate syndrome trajectory `σ(τ, t)` at Euclidean time `t ∈ [0, β]` along jump times `τ`
    (Part II, Section 3.5 (`subsec:worldline-expansion`), Lemma 3.9 (`lem:worldline-factorization-time-reversal`)). -/
def worldlineTrajectorySyndrome {L q_code r_0 m_max : ℕ}
    (D_field : Box3D L → LocalCSSDescriptor q_code r_0 m_max)
    (jumps : List (WorldlineJumpMonomer L q_code))
    (σ₀ : IdxCSS[L, q_code, m_max] → Bool)
    (τ : Fin jumps.length → ℝ) (t : ℝ) : IdxCSS[L, q_code, m_max] → Bool :=
  ((List.finRange jumps.length).filter (fun j => decide (τ j ≤ t))).foldr
    (fun j acc => syndromeXor (staticCSSPauliFlip D_field (jumps.get j).2.1 (jumps.get j).2.2) acc)
    σ₀

/-- Relative bare `H_0` Euclidean action `∫_0^β (E_0(σ(τ, t)) - E_0(σ₀)) dt` along trajectory `τ`. -/
def worldlineBareAction {L q_code r_0 m_max : ℕ}
    (D_field : Box3D L → LocalCSSDescriptor q_code r_0 m_max)
    (sys : SysCSS[L, q_code, m_max])
    (jumps : List (WorldlineJumpMonomer L q_code))
    (σ₀ : IdxCSS[L, q_code, m_max] → Bool)
    (β : ℝ) (τ : Fin jumps.length → ℝ) : ℝ :=
  ∫ t in Set.Icc 0 β,
    (sys.syndromeEnergy (worldlineTrajectorySyndrome D_field jumps σ₀ τ t) -
      sys.syndromeEnergy σ₀)

/-- Mayer bond factor `η_ϑ(σ(·); σ₀) = exp(-∫_0^β (d_ϑ(σ(τ, t)) - d_ϑ(σ₀)) dt) - 1`
    for an active diagonal collar cube `ϑ = (r', B)`
    (Part II, Section 3.5 (`subsec:worldline-expansion`), Equation `eq:mayer-factor-eta-def`). -/
def worldlineMayerBondFactor {L q_code r_0 m_max : ℕ}
    (D_field : Box3D L → LocalCSSDescriptor q_code r_0 m_max)
    (jumps : List (WorldlineJumpMonomer L q_code))
    (d_loc : ℕ → Finset (Box3D L) → (IdxCSS[L, q_code, m_max] → Bool) → ℝ)
    (σ₀ : IdxCSS[L, q_code, m_max] → Bool)
    (β : ℝ) (ϑ : ℕ × Finset (Box3D L)) (τ : Fin jumps.length → ℝ) : ℝ :=
  Real.exp (-∫ t in Set.Icc 0 β,
    (d_loc ϑ.1 ϑ.2 (worldlineTrajectorySyndrome D_field jumps σ₀ τ t) -
      d_loc ϑ.1 ϑ.2 σ₀)) - 1

/-- Ordered Dyson time simplex `0 ≤ τ_1 < ⋯ < τ_m ≤ β` (Part II, Section 3.5 (`subsec:worldline-expansion`)). -/
def InOrderedDysonSimplex {m : ℕ} (β : ℝ) (τ : Fin m → ℝ) : Prop :=
  (∀ j : Fin m, 0 ≤ τ j ∧ τ j ≤ β) ∧ StrictMono τ

/-- Intrinsic local Mayer–Dyson simplex integral weight `w_micro(γ; σ|_{C̄(γ)})` of a worldline polymer `γ`
    (Part II, Lemma 3.9 (`lem:worldline-factorization-time-reversal`)). Evaluated on
    `σ₀ = restrictSyndromeToCollar (worldlinePolymerNativeCollar sys C_RCA γ) σ`
    since all jump syndrome shifts and Mayer collar cubes of `γ` are supported inside `C̄(γ)`. -/
def worldlinePolymerMicroWeight {L q_code r_0 m_max : ℕ} [NeZero L]
    (D_field : Box3D L → LocalCSSDescriptor q_code r_0 m_max)
    (sys : SysCSS[L, q_code, m_max]) (C_RCA β : ℝ)
    (V : QuasiLocalPerturbation 3 L (SiteCSS[L, q_code]))
    (d_loc : ℕ → Finset (Box3D L) → (IdxCSS[L, q_code, m_max] → Bool) → ℝ)
    (γ : WorldlineDysonPolymer L q_code)
    (σ₀ : IdxCSS[L, q_code, m_max] → Bool) : ℝ :=
  ((-1 : ℝ) ^ γ.1.length) * worldlinePolymerLoopAmplitude D_field sys C_RCA V γ σ₀ *
    ∫ τ : Fin γ.1.length → ℝ,
      if InOrderedDysonSimplex β τ then
        Real.exp (-worldlineBareAction D_field sys γ.1 σ₀ β τ) *
          ∏ ϑ ∈ γ.2, worldlineMayerBondFactor D_field γ.1 d_loc σ₀ β ϑ τ
      else 0

/-- Factored character-twisted worldline polymer weight
    `w_ν(γ; σ) = (-1)^{⟨ν, μ(γ)⟩} (-1)^{|α(γ) ∩ σ|} w_micro(γ; σ|_{C̄(γ)})`
    (Part II, Lemma 3.9(ii) (`lem:worldline-factorization-time-reversal`), Equation `eq:P-gamma-spanning-surface`,
    and Proposition 3.10 (`prop:tube-local-ursell-erasure`), Equation `eq:ursell-partition-sigma`). -/
def worldlinePolymerWeight {L q_code r_0 m_max : ℕ} [NeZero L]
    (D_field : Box3D L → LocalCSSDescriptor q_code r_0 m_max)
    (sys : SysCSS[L, q_code, m_max]) (C_RCA β : ℝ)
    (V : QuasiLocalPerturbation 3 L (SiteCSS[L, q_code]))
    (d_loc : ℕ → Finset (Box3D L) → (IdxCSS[L, q_code, m_max] → Bool) → ℝ)
    (ν : PauliBitstringPair L q_code) (γ : WorldlineDysonPolymer L q_code)
    (σ : IdxCSS[L, q_code, m_max] → Bool) : ℝ :=
  symplecticPauliSign ν (worldlinePolymerLogicalCoset D_field sys C_RCA γ) *
    spanningSurfaceSign (worldlinePolymerSpanningSurface D_field sys C_RCA γ) σ *
    worldlinePolymerMicroWeight D_field sys C_RCA β V d_loc γ
      (restrictSyndromeToCollar (worldlinePolymerNativeCollar sys C_RCA γ) σ)

/-- An Ursell cluster `K = [γ_1, ..., γ_p]` of worldline polymers
    (Part II, Proposition 3.10 (`prop:tube-local-ursell-erasure`)). -/
abbrev WorldlineUrsellCluster (L q_code : ℕ) : Type :=
  List (WorldlineDysonPolymer L q_code)

/-- Combined monomer scale-cube support `⋃_{γ ∈ K} worldlinePolymerMonomers γ` of an Ursell cluster `K`. -/
def worldlineClusterMonomers {L q_code : ℕ} (K : WorldlineUrsellCluster L q_code) :
    Finset (ℕ × Finset (Box3D L)) :=
  K.foldr (fun γ acc => worldlinePolymerMonomers γ ∪ acc) ∅

/-- Combined `RCA_1` spanning check surface `α(K) = ⋃_{γ ∈ K} α(γ)` of an Ursell cluster `K`. -/
def worldlineClusterSpanningSurface {L q_code r_0 m_max : ℕ} [NeZero L]
    (D_field : Box3D L → LocalCSSDescriptor q_code r_0 m_max)
    (sys : SysCSS[L, q_code, m_max]) (C_RCA : ℝ)
    (K : WorldlineUrsellCluster L q_code) : Finset (IdxCSS[L, q_code, m_max]) :=
  K.foldr (fun γ acc => worldlinePolymerSpanningSurface D_field sys C_RCA γ ∪ acc) ∅

/-- Polymer incompatibility adjacency on cluster indices `Fin K.length` under native-collar overlap
    `C̄(γ_a) ∩ C̄(γ_b) ≠ ∅` (Part II, Proposition 3.10 (`prop:tube-local-ursell-erasure`)). -/
def PolymerClusterOverlap {L q_code m_max : ℕ} [NeZero L]
    (sys : SysCSS[L, q_code, m_max]) (C_RCA : ℝ)
    (K : WorldlineUrsellCluster L q_code)
    (a b : Fin K.length) : Prop :=
  a ≠ b ∧ ¬Disjoint (worldlinePolymerNativeCollar sys C_RCA (K.get a))
    (worldlinePolymerNativeCollar sys C_RCA (K.get b))

/-- Classical connected-graph Ursell coefficient `ϕ^T(K)` on the polymer incompatibility graph of `K`
    (Part II, Proposition 3.10 (`prop:tube-local-ursell-erasure`), Equation `eq:ursell-partition-sigma`):
    `(1 / p!) * ∑_{G ⊆ E(K) connected spanning} (-1)^{|G|}`. -/
def ursellConnectedGraphCoeff {L q_code m_max : ℕ} [NeZero L]
    (sys : SysCSS[L, q_code, m_max]) (C_RCA : ℝ)
    (K : WorldlineUrsellCluster L q_code) : ℝ :=
  let E_compat : Finset (Fin K.length × Fin K.length) :=
    Finset.univ.filter (fun e => e.1 < e.2 ∧ PolymerClusterOverlap sys C_RCA K e.1 e.2)
  ((Nat.factorial K.length : ℝ)⁻¹) *
    ∑ G ∈ E_compat.powerset.filter (fun G =>
        KPIsConnectedSubgraph (fun a b => (a, b) ∈ G ∨ (b, a) ∈ G) Finset.univ),
      ((-1 : ℝ) ^ G.card)

/-- Validity predicate for a connected Ursell cluster `K` of worldline polymers at cutoff `R_cut`. -/
def IsValidWorldlineUrsellCluster {L q_code r_0 m_max : ℕ} [NeZero L]
    (D_field : Box3D L → LocalCSSDescriptor q_code r_0 m_max)
    (sys : SysCSS[L, q_code, m_max]) (C_RCA : ℝ) (R_cut : ℕ)
    (K : WorldlineUrsellCluster L q_code) : Prop :=
  K ≠ [] ∧
  (∀ γ ∈ K, IsValidWorldlinePolymer D_field sys C_RCA R_cut γ) ∧
  KPIsConnectedSubgraph (PolymerClusterOverlap sys C_RCA K) Finset.univ

/-- Microscopic Ursell cluster weight `Φ_ν^T(K; σ) = ϕ^T(K) ∏_{γ ∈ K} w_ν(γ; σ)`
    (Part II, Proposition 3.10 (`prop:tube-local-ursell-erasure`), Equation `eq:ursell-partition-sigma`). -/
def worldlineClusterUrsellWeight {L q_code r_0 m_max : ℕ} [NeZero L]
    (D_field : Box3D L → LocalCSSDescriptor q_code r_0 m_max)
    (sys : SysCSS[L, q_code, m_max]) (C_RCA β : ℝ)
    (V : QuasiLocalPerturbation 3 L (SiteCSS[L, q_code]))
    (d_loc : ℕ → Finset (Box3D L) → (IdxCSS[L, q_code, m_max] → Bool) → ℝ)
    (ν : PauliBitstringPair L q_code) (K : WorldlineUrsellCluster L q_code)
    (σ : IdxCSS[L, q_code, m_max] → Bool) : ℝ :=
  ursellConnectedGraphCoeff sys C_RCA K *
    (K.map (fun γ => worldlinePolymerWeight D_field sys C_RCA β V d_loc ν γ σ)).prod

/-- Spatial footprint index `(M, α)` of resummed Ursell clusters, consisting of the monomer scale-cube
    support `M ⊆ worldlineScaleCubeFinset L R_cut` and canonical spanning surface `α ⊆ C`. -/
abbrev WorldlineUrsellFootprint (L q_code m_max : ℕ) : Type :=
  Finset (ℕ × Finset (Box3D L)) × Finset (IdxCSS[L, q_code, m_max])

/-- Finite index set of nonempty monomer-and-spanning-surface footprints `(M, α)` at cutoff `R_cut`. -/
def worldlineUrsellIndexFinset (L q_code m_max R_cut : ℕ) :
    Finset (WorldlineUrsellFootprint L q_code m_max) :=
  ((worldlineScaleCubeFinset L R_cut).powerset.filter Finset.Nonempty) ×ˢ
    (Finset.univ : Finset (IdxCSS[L, q_code, m_max])).powerset

/-- **Full Spanning Check Support $\overline{\mathcal{C}}^{\mathrm{span}}(\mathcal{K}) := \overline{\mathcal{C}}(\mathcal{K}) \cup \alpha(\mathcal{K})$
(`worldlineUrsellSpanningSupport`, Part II, Lemma 3.9(ii) (`lem:worldline-factorization-time-reversal`),
Equation `eq:C-bar-span-def`, and Proposition 3.10(i) (`prop:tube-local-ursell-erasure`))**:
Union of the native monomer collar check support $\overline{\mathcal{C}}(M) = \bigcup_{(r, A) \in M} \mathcal{C}(A^+)$
and the $\mathrm{RCA}_1$ spanning check surface $\alpha$. -/
def worldlineUrsellSpanningSupport
    {L q_code m_max : ℕ} [NeZero L]
    (sys : SysCSS[L, q_code, m_max]) (C_RCA : ℝ)
    (γ : WorldlineUrsellFootprint L q_code m_max) : Finset (IdxCSS[L, q_code, m_max]) :=
  nativeCollarSupport (fun p : ℕ × Finset (Box3D L) => rcaCollarChecks sys C_RCA p.1 p.2)
    γ.1 ∪ γ.2

/-- Concrete footprint-resummed character-twisted Ursell cluster weight
    `Φ_ν^T(M, α; σ) = ∑'_{K : monomers(K) = M, α(K) = α} Φ_ν^T(K; σ)`
    (Part II, Proposition 3.10 (`prop:tube-local-ursell-erasure`), Equation `eq:ursell-partition-sigma`). -/
def worldlineUrsellPhi
    {L q_code r_0 m_max : ℕ} [NeZero L]
    (D_field : Box3D L → LocalCSSDescriptor q_code r_0 m_max)
    (sys : SysCSS[L, q_code, m_max]) (C_RCA : ℝ) (R_cut : ℕ) (β : ℝ)
    (V : QuasiLocalPerturbation 3 L (SiteCSS[L, q_code]))
    (d_loc : ℕ → Finset (Box3D L) → (IdxCSS[L, q_code, m_max] → Bool) → ℝ)
    (ν : PauliBitstringPair L q_code)
    (γ : WorldlineUrsellFootprint L q_code m_max)
    (σ : IdxCSS[L, q_code, m_max] → Bool) : ℝ :=
  ∑' K : WorldlineUrsellCluster L q_code,
    if IsValidWorldlineUrsellCluster D_field sys C_RCA R_cut K ∧
        worldlineClusterMonomers K = γ.1 ∧
        worldlineClusterSpanningSurface D_field sys C_RCA K = γ.2 then
      worldlineClusterUrsellWeight D_field sys C_RCA β V d_loc ν K σ
    else 0

private lemma worldlinePolymerMonomers_subset_worldlineClusterMonomers
    {L q_code : ℕ} {K : WorldlineUrsellCluster L q_code} {γ : WorldlineDysonPolymer L q_code}
    (hγ : γ ∈ K) :
    worldlinePolymerMonomers γ ⊆ worldlineClusterMonomers K := by
  induction K with
  | nil => cases hγ
  | cons hd tl ih =>
    rcases List.mem_cons.mp hγ with rfl | h_tl
    · exact Finset.subset_union_left
    · exact Finset.Subset.trans (ih h_tl) Finset.subset_union_right

private lemma worldlinePolymerSpanningSurface_subset_worldlineClusterSpanningSurface
    {L q_code r_0 m_max : ℕ} [NeZero L]
    (D_field : Box3D L → LocalCSSDescriptor q_code r_0 m_max)
    (sys : SysCSS[L, q_code, m_max]) (C_RCA : ℝ)
    {K : WorldlineUrsellCluster L q_code} {γ : WorldlineDysonPolymer L q_code}
    (hγ : γ ∈ K) :
    worldlinePolymerSpanningSurface D_field sys C_RCA γ ⊆
      worldlineClusterSpanningSurface D_field sys C_RCA K := by
  induction K with
  | nil => cases hγ
  | cons hd tl ih =>
    rcases List.mem_cons.mp hγ with rfl | h_tl
    · exact Finset.subset_union_left
    · exact Finset.Subset.trans (ih h_tl) Finset.subset_union_right

/-- **Spanning-Surface and Native-Collar Locality of Worldline Ursell Weights
(`worldline_ursell_spanning_surface_collar_locality`, Part II, Lemma 3.9(ii) (`lem:worldline-factorization-time-reversal`) and Proposition 3.10(i) (`prop:tube-local-ursell-erasure`))**:
For every footprint $\gamma = (M, \alpha)$ and every syndrome-closed Pauli pair $\nu$,
$\Phi_\nu^{\mathrm{T}}(M, \alpha; \sigma)$ depends on $\sigma$ solely through its restriction to
$\overline{\mathcal{C}}^{\mathrm{span}}(M, \alpha) = \overline{\mathcal{C}}(M) \cup \alpha$. -/
theorem worldline_ursell_spanning_surface_collar_locality
    {L q_code r_0 m_max : ℕ} [NeZero L]
    (D_field : Box3D L → LocalCSSDescriptor q_code r_0 m_max)
    (sys : SysCSS[L, q_code, m_max]) (C_RCA : ℝ) (R_cut : ℕ) (β : ℝ)
    (V : QuasiLocalPerturbation 3 L (SiteCSS[L, q_code]))
    (d_loc : ℕ → Finset (Box3D L) → (IdxCSS[L, q_code, m_max] → Bool) → ℝ)
    (ν : PauliBitstringPair L q_code)
    (γ : WorldlineUrsellFootprint L q_code m_max)
    {σ₁ σ₂ : IdxCSS[L, q_code, m_max] → Bool}
    (h_agree : ∀ c ∈ worldlineUrsellSpanningSupport sys C_RCA γ, σ₁ c = σ₂ c) :
    worldlineUrsellPhi D_field sys C_RCA R_cut β V d_loc ν γ σ₁ =
      worldlineUrsellPhi D_field sys C_RCA R_cut β V d_loc ν γ σ₂ := by
  unfold worldlineUrsellPhi
  apply tsum_congr
  intro K
  split_ifs with hK
  · rcases hK with ⟨_h_valid, h_mon, h_surf⟩
    unfold worldlineClusterUrsellWeight
    apply congrArg (ursellConnectedGraphCoeff sys C_RCA K * ·)
    apply congrArg List.prod
    refine List.map_congr_left fun γ_p hγ_p => ?_
    unfold worldlinePolymerWeight
    have h_surf_sub : worldlinePolymerSpanningSurface D_field sys C_RCA γ_p ⊆
        worldlineUrsellSpanningSupport sys C_RCA γ := by
      intro c hc
      apply Finset.mem_union_right
      rw [← h_surf]
      exact worldlinePolymerSpanningSurface_subset_worldlineClusterSpanningSurface
        D_field sys C_RCA hγ_p hc
    have h_col_sub : worldlinePolymerNativeCollar sys C_RCA γ_p ⊆
        worldlineUrsellSpanningSupport sys C_RCA γ := by
      intro c hc
      apply Finset.mem_union_left
      rw [← h_mon]
      unfold worldlinePolymerNativeCollar at hc
      unfold nativeCollarSupport at hc ⊢
      rcases Finset.mem_biUnion.mp hc with ⟨p, hp, hc_p⟩
      exact Finset.mem_biUnion.mpr
        ⟨p, worldlinePolymerMonomers_subset_worldlineClusterMonomers hγ_p hp, hc_p⟩
    have h_sign_eq : spanningSurfaceSign (worldlinePolymerSpanningSurface D_field sys C_RCA γ_p) σ₁ =
        spanningSurfaceSign (worldlinePolymerSpanningSurface D_field sys C_RCA γ_p) σ₂ := by
      unfold spanningSurfaceSign
      have h_filt : (worldlinePolymerSpanningSurface D_field sys C_RCA γ_p).filter (fun c => σ₁ c = true) =
          (worldlinePolymerSpanningSurface D_field sys C_RCA γ_p).filter (fun c => σ₂ c = true) :=
        Finset.filter_congr fun c hc => by rw [h_agree c (h_surf_sub hc)]
      rw [h_filt]
    have h_rest_eq : restrictSyndromeToCollar (worldlinePolymerNativeCollar sys C_RCA γ_p) σ₁ =
        restrictSyndromeToCollar (worldlinePolymerNativeCollar sys C_RCA γ_p) σ₂ := by
      ext c; unfold restrictSyndromeToCollar
      split_ifs with hc
      · exact h_agree c (h_col_sub hc)
      · rfl
    rw [h_sign_eq, h_rest_eq]
  · rfl

lemma weylPauliX_mul_weylPauliZ_eq_signScalar_smul {L q_code : ℕ}
    (a b : BoxSlot3D L q_code → ZMod 2) :
    weylPauliX b * weylPauliZ a =
      signScalar (∑ p : BoxSlot3D L q_code, a p * b p) • (weylPauliZ a * weylPauliX b) := by
  rcases _root_.zmod2_eq_zero_or_one (∑ p : BoxSlot3D L q_code, a p * b p) with h0 | h1
  · rw [h0, signScalar_zero, one_smul]
    exact (weylPauliX_comm_weylPauliZ_of_symplectic_zero a b h0).eq
  · rw [h1]
    change weylPauliX b * weylPauliZ a = (-1 : ℂ) • (weylPauliZ a * weylPauliX b)
    rw [neg_one_smul ℂ (weylPauliZ a * weylPauliX b)]
    exact weylPauliX_anticomm_weylPauliZ_of_symplectic_one a b h1

lemma weylPauliZX_mul_weylPauliZX {L q_code : ℕ}
    (a₁ b₁ a₂ b₂ : BoxSlot3D L q_code → ZMod 2) :
    (weylPauliZ a₁ * weylPauliX b₁) * (weylPauliZ a₂ * weylPauliX b₂) =
      signScalar (∑ p : BoxSlot3D L q_code, a₂ p * b₁ p) •
        (weylPauliZ (a₁ + a₂) * weylPauliX (b₁ + b₂)) := by
  calc (weylPauliZ a₁ * weylPauliX b₁) * (weylPauliZ a₂ * weylPauliX b₂)
    _ = weylPauliZ a₁ * (weylPauliX b₁ * weylPauliZ a₂) * weylPauliX b₂ := by simp only [mul_assoc]
    _ = signScalar (∑ p : BoxSlot3D L q_code, a₂ p * b₁ p) •
          ((weylPauliZ a₁ * weylPauliZ a₂) * (weylPauliX b₁ * weylPauliX b₂)) := by
      rw [weylPauliX_mul_weylPauliZ_eq_signScalar_smul a₂ b₁, clm_mul_smul, clm_smul_mul]
      simp only [mul_assoc]
    _ = signScalar (∑ p : BoxSlot3D L q_code, a₂ p * b₁ p) •
          (weylPauliZ (a₁ + a₂) * weylPauliX (b₁ + b₂)) := by
      rw [← weylPauliZ_add, ← weylPauliX_add]

lemma weylPauliZX_comm_signScalar {L q_code : ℕ}
    (a₁ b₁ a₂ b₂ : BoxSlot3D L q_code → ZMod 2) :
    (weylPauliZ a₁ * weylPauliX b₁) * (weylPauliZ a₂ * weylPauliX b₂) =
      signScalar (∑ p : BoxSlot3D L q_code, (a₂ p * b₁ p + a₁ p * b₂ p)) •
        ((weylPauliZ a₂ * weylPauliX b₂) * (weylPauliZ a₁ * weylPauliX b₁)) := by
  rw [weylPauliZX_mul_weylPauliZX a₁ b₁ a₂ b₂, weylPauliZX_mul_weylPauliZX a₂ b₂ a₁ b₁,
    add_comm a₂ a₁, add_comm b₂ b₁, smul_smul, ← signScalar_add, Finset.sum_add_distrib]
  have h_cancel : ∀ x y : ZMod 2, x + y + y = x := by decide
  rw [h_cancel]

def worldlineJumpOpZX {L q_code : ℕ} (ξ : WorldlineJumpMonomer L q_code) : ℬ_CSS[L, q_code] :=
  weylPauliZ ξ.2.1 * weylPauliX ξ.2.2

def worldlinePolymerLoopOpZX {L q_code : ℕ} (γ : WorldlineDysonPolymer L q_code) : ℬ_CSS[L, q_code] :=
  (γ.1.reverse.map worldlineJumpOpZX).prod

lemma list_prod_map_worldlineJumpOpZX_eq_signScalar_smul {L q_code : ℕ}
    (l : List (WorldlineJumpMonomer L q_code)) :
    ∃ s : ZMod 2,
      (l.map worldlineJumpOpZX).prod =
        signScalar s •
          (weylPauliZ (l.map (fun ξ => ξ.2.1)).sum *
            weylPauliX (l.map (fun ξ => ξ.2.2)).sum) := by
  induction l with
  | nil =>
    refine ⟨0, ?_⟩
    simp [signScalar_zero, weylPauliZ_zero, weylPauliX_zero]
  | cons hd tl ih =>
    rcases ih with ⟨s_tl, h_tl⟩
    refine ⟨s_tl + ∑ p : BoxSlot3D L q_code, (tl.map (fun ξ => ξ.2.1)).sum p * hd.2.2 p, ?_⟩
    simp only [List.map_cons, List.prod_cons, List.sum_cons, worldlineJumpOpZX]
    rw [h_tl, clm_mul_smul, weylPauliZX_mul_weylPauliZX, smul_smul, ← signScalar_add]

private lemma isSupportedOn_weylPauliZ_of_supp {L q_code : ℕ}
    (A : Finset (Box3D L)) (a : BoxSlot3D L q_code → ZMod 2)
    (ha : ∀ p : BoxSlot3D L q_code, a p ≠ 0 → p.1 ∈ A) :
    IsSupportedOn (SiteCSS[L, q_code]) A (weylPauliZ a) := by
  let phaseA (α : LocalConfig (SiteCSS[L, q_code]) A) : ℂ :=
    pauliPhase (fun p : ↥A × Fin q_code => a (p.1.1, p.2))
      (fun p : ↥A × Fin q_code => boolToZMod2 (α p.1 p.2))
  refine ⟨LinearMap.toContinuousLinearMap
    { toFun := fun ψ_A => WithLp.toLp 2 (fun α => phaseA α * ψ_A.ofLp α)
      map_add' := fun ψ₁ ψ₂ => by
        ext α; change phaseA α * (ψ₁.ofLp α + ψ₂.ofLp α) =
          phaseA α * ψ₁.ofLp α + phaseA α * ψ₂.ofLp α; ring
      map_smul' := fun c ψ => by
        ext α; change phaseA α * (c * ψ.ofLp α) = c * (phaseA α * ψ.ofLp α); ring }, ?_⟩
  ext ψ σ; change pauliPhase a (codeConfigBits σ) * ψ.ofLp σ =
    phaseA (restrictConfig A σ) * ψ.ofLp (spliceConfig A (restrictConfig A σ) σ)
  rw [_root_.spliceConfig_restrictConfig]; congr 1; dsimp [pauliPhase, phaseA]
  have h_sum : (∑ p : BoxSlot3D L q_code, a p * codeConfigBits σ p) =
      ∑ p : ↥A × Fin q_code, a (p.1.1, p.2) * boolToZMod2 (restrictConfig A σ p.1 p.2) := by
    rw [Fintype.sum_prod_type, Fintype.sum_prod_type, ← Finset.sum_subset (Finset.subset_univ A)]
    · rw [← Finset.sum_attach A]; refine Finset.sum_congr rfl fun vA _ => Finset.sum_congr rfl fun s _ => ?_
      simp [codeConfigBits, restrictConfig]
    · intro v _ hv; refine Finset.sum_eq_zero fun s _ => ?_
      have h0 : a (v, s) = 0 := by_contra fun hne => hv (ha (v, s) hne)
      simp [h0]
  rw [h_sum]

private lemma isSupportedOn_weylPauliX_of_supp {L q_code : ℕ}
    (A : Finset (Box3D L)) (b : BoxSlot3D L q_code → ZMod 2)
    (hb : ∀ p : BoxSlot3D L q_code, b p ≠ 0 → p.1 ∈ A) :
    IsSupportedOn (SiteCSS[L, q_code]) A (weylPauliX b) := by
  let flipSub : LocalConfig (SiteCSS[L, q_code]) A → LocalConfig (SiteCSS[L, q_code]) A :=
    fun α vA s => xor (α vA s) (zmod2ToBool (b (vA.1, s)))
  refine ⟨LinearMap.toContinuousLinearMap
    { toFun := fun ψ_A => WithLp.toLp 2 (fun α => ψ_A.ofLp (flipSub α))
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }, ?_⟩
  ext ψ σ; change ψ.ofLp (flipCodeConfig b σ) =
    ψ.ofLp (spliceConfig A (flipSub (restrictConfig A σ)) σ)
  refine congrArg ψ.ofLp (funext fun v => funext fun s => ?_)
  dsimp [flipCodeConfig, spliceConfig, flipSub, restrictConfig]
  by_cases hv : v ∈ A
  · simp [hv, zmod2ToBool]
  · have h0 : b (v, s) = 0 := by_contra fun hne => hv (hb (v, s) hne)
    simp [hv, h0, zmod2ToBool]

lemma hermitianPauliZX_isSelfAdjoint_and_sq_eq_one {L q_code : ℕ}
    (a b : BoxSlot3D L q_code → ZMod 2) :
    IsSelfAdjoint (hermitianPauliZX a b) ∧
    hermitianPauliZX a b * hermitianPauliZX a b = 1 := by
  have hZ_sa := weylPauliZ_isSelfAdjoint a
  have hX_sa := weylPauliX_isSelfAdjoint b
  have hZ_sq := weylPauliZ_sq_eq_one a
  have hX_sq := weylPauliX_sq_eq_one b
  refine ⟨?_, ?_⟩
  · dsimp [hermitianPauliZX]
    rcases _root_.zmod2_eq_zero_or_one (∑ p : BoxSlot3D L q_code, a p * b p) with h0 | h1
    · rw [if_pos h0, isSelfAdjoint_iff, star_mul, hX_sa.star_eq, hZ_sa.star_eq,
        (weylPauliX_comm_weylPauliZ_of_symplectic_zero a b h0).eq]
    · rw [if_neg (by rw [h1]; decide), isSelfAdjoint_iff, star_smul, Complex.star_def,
        Complex.conj_I, star_mul, hX_sa.star_eq, hZ_sa.star_eq,
        weylPauliX_anticomm_weylPauliZ_of_symplectic_one a b h1, smul_neg, neg_smul, neg_neg]
  · dsimp [hermitianPauliZX]
    rcases _root_.zmod2_eq_zero_or_one (∑ p : BoxSlot3D L q_code, a p * b p) with h0 | h1
    · rw [if_pos h0]
      calc (weylPauliZ a * weylPauliX b) * (weylPauliZ a * weylPauliX b)
        _ = weylPauliZ a * (weylPauliX b * weylPauliZ a) * weylPauliX b := by simp only [mul_assoc]
        _ = (weylPauliZ a * weylPauliZ a) * (weylPauliX b * weylPauliX b) := by
          rw [(weylPauliX_comm_weylPauliZ_of_symplectic_zero a b h0).eq]; simp only [mul_assoc]
        _ = 1 := by rw [hZ_sq, hX_sq, mul_one]
    · rw [if_neg (by rw [h1]; decide), clm_smul_mul, clm_mul_smul, smul_smul, Complex.I_mul_I]
      have h_sq : (weylPauliZ a * weylPauliX b) * (weylPauliZ a * weylPauliX b) =
          signScalar (∑ p, a p * b p) • (1 : ℬ_CSS[L, q_code]) := by
        calc (weylPauliZ a * weylPauliX b) * (weylPauliZ a * weylPauliX b)
          _ = weylPauliZ a * (weylPauliX b * weylPauliZ a) * weylPauliX b := by simp only [mul_assoc]
          _ = signScalar (∑ p, a p * b p) •
                ((weylPauliZ a * weylPauliZ a) * (weylPauliX b * weylPauliX b)) := by
            rw [weylPauliX_mul_weylPauliZ_eq_signScalar_smul a b, clm_mul_smul, clm_smul_mul]
            simp only [mul_assoc]
          _ = signScalar (∑ p, a p * b p) • (1 : ℬ_CSS[L, q_code]) := by
            rw [hZ_sq, hX_sq, mul_one]
      have h_neg_mul : (-1 : ℂ) * signScalar (∑ p, a p * b p) = 1 := by
        rw [h1]; simp [signScalar]
      rw [h_sq, smul_smul, h_neg_mul, one_smul]

lemma hermitianPauliZX_props {L q_code r_0 m_max : ℕ}
    (D_field : Box3D L → LocalCSSDescriptor q_code r_0 m_max)
    (sys : SysCSS[L, q_code, m_max])
    (h_sys_checks : ∀ idx, sys.checkProj idx = staticCSSCheckProj D_field idx ∧
      sys.support idx = staticCSSCheckSupport D_field idx ∧ sys.weight idx = 1)
    (A : Finset (Box3D L))
    (a b : BoxSlot3D L q_code → ZMod 2)
    (h_supp : ∀ p : BoxSlot3D L q_code, a p ≠ 0 ∨ b p ≠ 0 → p.1 ∈ A)
    (h_closed : staticCSSPauliFlip D_field a b = fun _ => false) :
    let W := hermitianPauliZX a b
    IsSelfAdjoint W ∧
    W * W = 1 ∧
    IsSupportedOn (SiteCSS[L, q_code]) A W ∧
    (∀ idx, Commute W (sys.checkProj idx)) ∧
    (∀ x y : BoxSlot3D L q_code → ZMod 2,
      W * (weylPauliZ x * weylPauliX y) =
        signScalar (∑ p : BoxSlot3D L q_code, (x p * b p + a p * y p)) •
          ((weylPauliZ x * weylPauliX y) * W)) := by
  intro W
  rcases hermitianPauliZX_isSelfAdjoint_and_sq_eq_one a b with ⟨hW_sa, hW_sq⟩
  have hU_comm : ∀ idx, Commute (weylPauliZ a * weylPauliX b) (sys.checkProj idx) := fun idx => by
    rw [commute_iff_eq, (h_sys_checks idx).1]
    have h_flip := weylPauliZX_mul_staticCSSCheckProj D_field a b idx
    have h_f0 : staticCSSPauliFlip D_field a b idx = false := congr_fun h_closed idx
    rwa [h_f0, if_neg Bool.false_ne_true] at h_flip
  have hU_supp : IsSupportedOn (SiteCSS[L, q_code]) A (weylPauliZ a * weylPauliX b) :=
    _root_.isSupportedOn_mul A
      (isSupportedOn_weylPauliZ_of_supp A a fun p hp => h_supp p (Or.inl hp))
      (isSupportedOn_weylPauliX_of_supp A b fun p hp => h_supp p (Or.inr hp))
  refine ⟨hW_sa, hW_sq, ?_, ?_, ?_⟩
  · dsimp [W, hermitianPauliZX]
    split_ifs
    · exact hU_supp
    · rcases hU_supp with ⟨f_A, hf_A⟩
      refine ⟨Complex.I • f_A, ?_⟩
      rw [hf_A]
      ext ψ σ
      rfl
  · intro idx
    dsimp [W, hermitianPauliZX]
    split_ifs
    · exact hU_comm idx
    · exact (hU_comm idx).smul_left Complex.I
  · intro x y
    dsimp [W, hermitianPauliZX]
    split_ifs
    · exact weylPauliZX_comm_signScalar a b x y
    · rw [clm_smul_mul, weylPauliZX_comm_signScalar a b x y, clm_mul_smul, smul_comm]

private lemma exists_subset_sum_zmod2_of_ker_subset
    {V ι_chk : Type*} [AddZeroClass V] [DecidableEq ι_chk]
    (C_collar : Finset ι_chk)
    (f : ι_chk → V → ZMod 2)
    (hf_add : ∀ c v w, f c (v + w) = f c v + f c w)
    (φ : V → ZMod 2)
    (hφ_add : ∀ v w, φ (v + w) = φ v + φ w)
    (h_ker : ∀ v : V, (∀ c ∈ C_collar, f c v = 0) → φ v = 0) :
    ∃ α ⊆ C_collar, ∀ v : V, φ v = ∑ c ∈ α, f c v := by
  induction C_collar using Finset.induction_on generalizing φ with
  | empty =>
    refine ⟨∅, Finset.Subset.refl ∅, fun v => ?_⟩
    rw [Finset.sum_empty]
    exact h_ker v (fun c hc => False.elim (Finset.notMem_empty c hc))
  | @insert c₀ s hc₀ ih =>
    by_cases h_s : ∀ v : V, (∀ c ∈ s, f c v = 0) → φ v = 0
    · rcases ih φ hφ_add h_s with ⟨α, hα_sub, hα_eq⟩
      exact ⟨α, Finset.Subset.trans hα_sub (Finset.subset_insert c₀ s), hα_eq⟩
    · push_neg at h_s
      rcases h_s with ⟨v₀, hv₀_s, hv₀_φ⟩
      have hφ_v₀ : φ v₀ = 1 := (_root_.zmod2_eq_zero_or_one (φ v₀)).resolve_left hv₀_φ
      have hfc₀_v₀_ne : f c₀ v₀ ≠ 0 := fun h0 => hv₀_φ (h_ker v₀ fun c hc => by
        rcases Finset.mem_insert.mp hc with rfl | hcs
        · exact h0
        · exact hv₀_s c hcs)
      have hfc₀_v₀ : f c₀ v₀ = 1 := (_root_.zmod2_eq_zero_or_one (f c₀ v₀)).resolve_left hfc₀_v₀_ne
      let φ' : V → ZMod 2 := fun v => φ v + f c₀ v
      have hφ'_add : ∀ v w, φ' (v + w) = φ' v + φ' w := fun v w => by
        dsimp [φ']; rw [hφ_add, hf_add]; ring
      have hφ'_ker : ∀ v : V, (∀ c ∈ s, f c v = 0) → φ' v = 0 := fun v hv_s => by
        dsimp [φ']
        rcases _root_.zmod2_eq_zero_or_one (f c₀ v) with h0 | h1
        · have h_all : ∀ c ∈ insert c₀ s, f c v = 0 := fun c hc => by
            rcases Finset.mem_insert.mp hc with rfl | hcs
            · exact h0
            · exact hv_s c hcs
          rw [h_ker v h_all, h0, add_zero]
        · have h_all : ∀ c ∈ insert c₀ s, f c (v + v₀) = 0 := fun c hc => by
            rw [hf_add]
            rcases Finset.mem_insert.mp hc with rfl | hcs
            · rw [h1, hfc₀_v₀]; decide
            · rw [hv_s c hcs, hv₀_s c hcs, add_zero]
          have h_sum_zero := h_ker (v + v₀) h_all
          rw [hφ_add, hφ_v₀] at h_sum_zero
          rw [h1, h_sum_zero]
      rcases ih φ' hφ'_add hφ'_ker with ⟨α, hα_sub, hα_eq⟩
      refine ⟨insert c₀ α, Finset.insert_subset_insert c₀ hα_sub, fun v => ?_⟩
      have hc₀_not_α : c₀ ∉ α := fun h_in => hc₀ (hα_sub h_in)
      rw [Finset.sum_insert hc₀_not_α, ← hα_eq v]
      dsimp [φ']
      have h_cancel : ∀ x y : ZMod 2, y + (x + y) = x := by decide
      exact (h_cancel (φ v) (f c₀ v)).symm

private lemma signScalar_sum_boolToZMod2_eq_spanningSurfaceSign {L q_code m_max : ℕ}
    (α : Finset (IdxCSS[L, q_code, m_max]))
    (σ : IdxCSS[L, q_code, m_max] → Bool) :
    signScalar (∑ c ∈ α, boolToZMod2 (σ c)) =
      ((spanningSurfaceSign α σ : ℝ) : ℂ) := by
  induction α using Finset.induction_on with
  | empty =>
    simp [spanningSurfaceSign, signScalar_zero]
  | @insert c₀ s hc₀ ih =>
    rw [Finset.sum_insert hc₀, signScalar_add, ih]
    unfold spanningSurfaceSign
    rw [Finset.filter_insert]
    cases hσ : σ c₀
    · simp [boolToZMod2, signScalar_zero]
    · have hc₀_filt : c₀ ∉ s.filter (fun c => σ c = true) :=
        fun h => hc₀ (Finset.mem_filter.mp h).1
      rw [if_pos rfl, Finset.card_insert_of_notMem hc₀_filt]
      change (-1 : ℂ) * ((if (s.filter (fun c => σ c = true)).card % 2 = 1 then (-1 : ℝ) else 1 : ℝ) : ℂ) =
        ((if ((s.filter (fun c => σ c = true)).card + 1) % 2 = 1 then (-1 : ℝ) else 1 : ℝ) : ℂ)
      by_cases h_mod : (s.filter (fun c => σ c = true)).card % 2 = 1
      · have h_mod' : ((s.filter (fun c => σ c = true)).card + 1) % 2 = 0 := by omega
        rw [if_pos h_mod, if_neg (by omega)]; norm_num
      · have h_mod' : ((s.filter (fun c => σ c = true)).card + 1) % 2 = 1 := by omega
        rw [if_neg h_mod, if_pos h_mod']; norm_num

lemma hilbertTrace_pos_of_isStarProjection_ne_zero {D L : ℕ} {Site : BoxD D L → Type}
    [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    {P : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site}
    (hP : IsStarProjection P) (hP_ne : P ≠ 0) :
    0 < hilbertTrace P := by
  have h_ex : ∃ ω : ManyBodyConfig Site, P (basisVecGlobal Site ω) ≠ 0 := by
    by_contra! h_all
    apply hP_ne
    ext φ y
    have h_sum : φ = ∑ τ : ManyBodyConfig Site, (φ.ofLp τ) • basisVecGlobal Site τ := by
      ext σ; simp [basisVecGlobal, WithLp.ofLp_sum]
    conv_lhs => rw [h_sum]
    rw [map_sum]
    simp [h_all]
  rcases h_ex with ⟨ω₀, hω₀⟩
  have h_tr_eq : hilbertTrace P = ∑ ω : ManyBodyConfig Site, ‖P (basisVecGlobal Site ω)‖ ^ 2 := by
    unfold hilbertTrace
    exact Finset.sum_congr rfl fun ω _ => isStarProjection_re_inner_eq_norm_sq hP (basisVecGlobal Site ω)
  rw [h_tr_eq]
  exact lt_of_lt_of_le (sq_pos_of_ne_zero (norm_ne_zero_iff.mpr hω₀))
    (Finset.single_le_sum (fun ω _ => sq_nonneg ‖P (basisVecGlobal Site ω)‖) (Finset.mem_univ ω₀))

lemma hilbertTrace_complex_smul_syndromeProjector {D L : ℕ} {Site : BoxD D L → Type}
    [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)] {ι : Type} [Fintype ι] [DecidableEq ι]
    (sys : IndexedCommutingProjectorHamiltonian D L Site ι) (z : ℂ) (σ : ι → Bool) :
    hilbertTrace (z • sys.syndromeProjector σ) = z.re * hilbertTrace (sys.syndromeProjector σ) := by
  have hP := (_root_.syndrome_resolution_indexed sys).2.1 σ
  unfold hilbertTrace
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun ω _ => ?_
  have h_im : (inner ℂ (basisVecGlobal Site ω) (sys.syndromeProjector σ (basisVecGlobal Site ω))).im = 0 := by
    have h_sa := ContinuousLinearMap.isSelfAdjoint_iff'.mp hP.2
    have h_in := ContinuousLinearMap.adjoint_inner_right (sys.syndromeProjector σ)
      (basisVecGlobal Site ω) (basisVecGlobal Site ω)
    rw [h_sa] at h_in
    have h_conj : starRingEnd ℂ (inner ℂ (sys.syndromeProjector σ (basisVecGlobal Site ω)) (basisVecGlobal Site ω)) =
        inner ℂ (basisVecGlobal Site ω) (sys.syndromeProjector σ (basisVecGlobal Site ω)) :=
      inner_conj_symm _ _
    rw [← h_in] at h_conj
    have h_im0 := congr_arg Complex.im h_conj
    rw [Complex.conj_im] at h_im0
    linarith
  rw [ContinuousLinearMap.smul_apply, inner_smul_right]
  change (z * inner ℂ (basisVecGlobal Site ω) (sys.syndromeProjector σ (basisVecGlobal Site ω))).re =
    z.re * (inner ℂ (basisVecGlobal Site ω) (sys.syndromeProjector σ (basisVecGlobal Site ω))).re
  rw [Complex.mul_re, h_im, mul_zero, sub_zero]

lemma sys_P0_ne_zero_of_validDescriptorField {L q_code r_0 m_max : ℕ} [NeZero L]
    (D_field : Box3D L → LocalCSSDescriptor q_code r_0 m_max)
    (h_valid : ValidDescriptorField D_field)
    (sys : SysCSS[L, q_code, m_max])
    (h_sys_checks : ∀ idx, sys.checkProj idx = staticCSSCheckProj D_field idx ∧
      sys.support idx = staticCSSCheckSupport D_field idx ∧ sys.weight idx = 1) :
    sys.P0 ≠ 0 := by
  intro hP0
  have h_res := _root_.syndrome_resolution_indexed sys
  have h_tr0 : hilbertTrace sys.P0 = 0 := by unfold hilbertTrace; simp [hP0]
  have h_all_zero : ∀ σ, sys.syndromeProjector σ = 0 := fun σ => by
    by_contra h_ne
    have h_pos := hilbertTrace_pos_of_isStarProjection_ne_zero (h_res.2.1 σ) h_ne
    have h_eq := (hilbertTrace_syndromeProjector_eq_P0_of_ne_zero D_field h_valid sys h_sys_checks σ h_ne).2
    linarith
  have h_one_zero : (1 : ℬ_CSS[L, q_code]) = 0 := by
    rw [← h_res.2.2.2.1]
    exact Finset.sum_eq_zero fun σ _ => h_all_zero σ
  let ω₀ : ManyBodyConfig (SiteCSS[L, q_code]) := fun _ _ => false
  have h_app := congr_arg (fun T : ℬ_CSS[L, q_code] => (T (basisVecGlobal (SiteCSS[L, q_code]) ω₀)).ofLp ω₀) h_one_zero
  simp [basisVecGlobal] at h_app

/-- The $\mathbb{F}_2$ syndrome bit `boolToZMod2 (staticCSSPauliFlip D_field p.1 p.2 c)` equals the
symplectic inner product of `p = (p.1, p.2)` with `(staticCSSCheckPauliZ D_field c, staticCSSCheckPauliX D_field c)`. -/
lemma boolToZMod2_staticCSSPauliFlip_eq_sum_checkPauli
    {L q_code r_0 m_max : ℕ}
    (D_field : Box3D L → LocalCSSDescriptor q_code r_0 m_max)
    (p : PauliBitstringPair L q_code) (c : IdxCSS[L, q_code, m_max]) :
    boolToZMod2 (staticCSSPauliFlip D_field p.1 p.2 c) =
      ∑ slot : BoxSlot3D L q_code,
        (p.1 slot * staticCSSCheckPauliX D_field c slot +
          staticCSSCheckPauliZ D_field c slot * p.2 slot) := by
  have h_dec : ∀ x : ZMod 2, boolToZMod2 (decide (x ≠ 0)) = x := fun x => by
    rcases _root_.zmod2_eq_zero_or_one x with rfl | rfl <;> rfl
  rcases c with ⟨v, s⟩ | ⟨v, idx⟩ | ⟨v, idx⟩
  · dsimp [staticCSSPauliFlip, staticCSSCheckPauliZ, staticCSSCheckPauliX]
    by_cases h_inact : (D_field v).activeSlot s = false
    · rw [h_inact]
      change boolToZMod2 (true && decide ((∑ slot, singleSlotChain v s slot * p.2 slot) ≠ 0)) =
        ∑ slot, (p.1 slot * 0 + (if false = false then singleSlotChain v s else 0) slot * p.2 slot)
      rw [Bool.true_and, h_dec]; refine Finset.sum_congr rfl fun slot _ => ?_; rw [if_pos rfl]; ring
    · rw [Bool.eq_true_of_not_eq_false h_inact]
      change boolToZMod2 (false && decide ((∑ slot, singleSlotChain v s slot * p.2 slot) ≠ 0)) =
        ∑ slot, (p.1 slot * 0 + (if true = false then singleSlotChain v s else 0) slot * p.2 slot)
      simp [boolToZMod2]
  · dsimp [staticCSSPauliFlip, staticCSSCheckPauliZ, staticCSSCheckPauliX]
    by_cases h_lt : idx.val < (D_field v).numXChecks.val
    · rw [decide_eq_true h_lt, Bool.true_and, h_dec]
      refine Finset.sum_congr rfl fun slot _ => ?_; rw [if_pos h_lt]; ring
    · rw [decide_eq_false h_lt, Bool.false_and]; simp [h_lt, boolToZMod2]
  · dsimp [staticCSSPauliFlip, staticCSSCheckPauliZ, staticCSSCheckPauliX]
    by_cases h_lt : idx.val < (D_field v).numZChecks.val
    · rw [decide_eq_true h_lt, Bool.true_and, h_dec]
      refine Finset.sum_congr rfl fun slot _ => ?_; rw [if_pos h_lt]; ring
    · rw [decide_eq_false h_lt, Bool.false_and]; simp [h_lt, boolToZMod2]

lemma bareLogicalProjection_eq_zero_of_mem_stabilizerPauliSubmodule
    {L q_code r_0 m_max : ℕ}
    (D_field : Box3D L → LocalCSSDescriptor q_code r_0 m_max)
    {p : PauliBitstringPair L q_code} (hp : p ∈ stabilizerPauliSubmodule D_field) :
    bareLogicalProjection D_field p = (0, 0) := by
  unfold bareLogicalProjection
  dsimp only [LinearMap.comp_apply, Submodule.coe_subtype]
  have hp' : (⟨p, hp⟩ : stabilizerPauliSubmodule D_field).1 = p := rfl
  rw [← hp', Submodule.projectionOnto_apply_right]
  rfl

lemma exists_finset_sum_add_bareLogicalProjection
    {L q_code r_0 m_max : ℕ}
    (D_field : Box3D L → LocalCSSDescriptor q_code r_0 m_max)
    (p : PauliBitstringPair L q_code) :
    ∃ α : Finset (IdxCSS[L, q_code, m_max]),
      bareLogicalProjection D_field p + p =
        ∑ c ∈ α, (staticCSSCheckPauliZ D_field c, staticCSSCheckPauliX D_field c) := by
  let S := stabilizerPauliSubmodule D_field
  let Q := Classical.choose S.exists_isCompl
  have hQ : IsCompl Q S := (Classical.choose_spec S.exists_isCompl).symm
  have h_mem : bareLogicalProjection D_field p + p ∈ S := by
    have h_eq : bareLogicalProjection D_field p + p = p - bareLogicalProjection D_field p := by
      have h_z2 : ∀ x y : ZMod 2, y + x = x - y := by decide
      ext slot <;> exact h_z2 _ _
    rw [h_eq, ← Submodule.ker_projectionOnto hQ, LinearMap.mem_ker, map_sub]
    unfold bareLogicalProjection
    dsimp only [LinearMap.comp_apply, Submodule.coe_subtype]
    rw [Submodule.projectionOnto_apply_left hQ, sub_self]
  let g : IdxCSS[L, q_code, m_max] → PauliBitstringPair L q_code :=
    fun c => (staticCSSCheckPauliZ D_field c, staticCSSCheckPauliX D_field c)
  have h_self : ∀ x : PauliBitstringPair L q_code, x + x = 0 := fun x => by
    have h_z2 : ∀ a : ZMod 2, a + a = 0 := by decide
    ext slot <;> exact h_z2 _
  refine Submodule.span_induction (p := fun q _ => ∃ α : Finset (IdxCSS[L, q_code, m_max]),
      q = ∑ c ∈ α, g c) ?_ ⟨∅, Finset.sum_empty.symm⟩ ?_ ?_ h_mem
  · rintro _ ⟨c, rfl⟩; exact ⟨{c}, (Finset.sum_singleton g c).symm⟩
  · rintro _ _ hm₁ hm₂ ⟨α₁, rfl⟩ ⟨α₂, rfl⟩
    clear hm₁ hm₂
    induction α₁ using Finset.induction_on with
    | empty => exact ⟨α₂, by simp⟩
    | @insert c s hc ih =>
      rcases ih with ⟨β, hβ⟩
      rw [Finset.sum_insert hc, add_assoc, hβ]
      by_cases hcβ : c ∈ β
      · refine ⟨β.erase c, ?_⟩
        rw [← Finset.add_sum_erase _ _ hcβ, ← add_assoc, h_self (g c), zero_add]
      · exact ⟨insert c β, (Finset.sum_insert hcβ).symm⟩
  · rintro r _ _ ⟨α, rfl⟩
    rcases _root_.zmod2_eq_zero_or_one r with rfl | rfl
    · exact ⟨∅, by simp⟩
    · exact ⟨α, by simp⟩

lemma hermitianPauliZX_syndrome_eigenvalue_and_collar_surface
    {L q_code r_0 m_max L_star r : ℕ} [NeZero L]
    {C_RCA : ℝ}
    (D_field : Box3D L → LocalCSSDescriptor q_code r_0 m_max)
    (h_valid : ValidDescriptorField D_field)
    (sys : SysCSS[L, q_code, m_max])
    (h_sys_checks : ∀ idx, sys.checkProj idx = staticCSSCheckProj D_field idx ∧
      sys.support idx = staticCSSCheckSupport D_field idx ∧ sys.weight idx = 1)
    (h_tqo1 : SatisfiesTQO1 sys L_star)
    (h_tqo2 : SatisfiesSectorFilteredLinearTQO2 sys 1 L_star C_RCA)
    (hr1 : 1 ≤ r) (hr_Lstar : r ≤ L_star) (x0 : Box3D L)
    (a b : BoxSlot3D L q_code → ZMod 2)
    (h_supp : ∀ slot : BoxSlot3D L q_code, a slot ≠ 0 ∨ b slot ≠ 0 → slot.1 ∈ boxCube x0 r)
    (h_closed : staticCSSPauliFlip D_field a b = fun _ => false) :
    ∃ (α : Finset (IdxCSS[L, q_code, m_max])) (c₀ : ℝ),
      α ⊆ rcaCollarChecks sys C_RCA r (boxCube x0 r) ∧
      (a, b) ∈ stabilizerPauliSubmodule D_field ∧
      c₀ ≠ 0 ∧
      ∀ σ ∈ realizableSyndromes D_field,
        sys.syndromeProjector σ * hermitianPauliZX a b =
          ((spanningSurfaceSign α σ * c₀ : ℝ) : ℂ) • sys.syndromeProjector σ := by
  let A := boxCube x0 r
  let W := hermitianPauliZX a b
  rcases hermitianPauliZX_props D_field sys h_sys_checks A a b h_supp h_closed with
    ⟨hW_sa, hW_sq, hW_supp, hW_comm_chk, hW_comm_pauli⟩
  have h_res := _root_.syndrome_resolution_indexed sys
  have hW_comm_syn : ∀ σ, Commute W (sys.syndromeProjector σ) :=
    (indexed_check_commuting_perturbation_commutes_with_syndromeProjector sys W hW_comm_chk).1
  have hW_comm_P0 : Commute W sys.P0 := by rw [← h_res.1]; exact hW_comm_syn (fun _ => false)
  have hA_mem : A ∈ boxCubes 3 L r := Finset.mem_image_of_mem _ (Finset.mem_univ x0)
  have hW_supp_anchor : IsSupportedOn (SiteCSS[L, q_code]) (boxCube (anchorOfCube r A) r) W := by
    rw [boxCube_anchorOfCube hA_mem]; exact hW_supp
  rcases exists_indexed_sector_sandwich_of_tqo_bhm sys h_tqo2 hr1 hr_Lstar
      (anchorOfCube r A) W hW_sa hW_supp_anchor hW_comm_P0 with ⟨c₀, _, _, hc₀_ann⟩
  rw [mul_one] at hc₀_ann
  have hW_clean : ∀ σ : IdxCSS[L, q_code, m_max] → Bool,
      (∀ idx ∈ rcaCollarChecks sys C_RCA r A, σ idx = false) →
      W * sys.syndromeProjector σ = ((c₀ : ℝ) : ℂ) • sys.syndromeProjector σ := by
    intro σ h_clean
    have hP_clean : sys.localGroundProj (rcaCollarCube C_RCA r A) * sys.syndromeProjector σ = sys.syndromeProjector σ :=
      (perturbed_P_loc_mul_syndromeProjector_of_clean_region sys fun c hc =>
        h_clean c (Finset.mem_filter.mpr ⟨Finset.mem_univ c, hc⟩)).1
    have h_diff_zero : (W - ((c₀ : ℝ) : ℂ) • 1) * sys.syndromeProjector σ = 0 := by
      rw [← hP_clean, ← mul_assoc]
      change (W - ((c₀ : ℝ) : ℂ) • 1) *
        sys.localGroundProj (enclosingBoxCube (anchorOfCube r A) r (linearExpansionRadius C_RCA r)) *
        sys.syndromeProjector σ = 0
      rw [hc₀_ann, zero_mul]
    rw [sub_mul, clm_smul_mul, one_mul, sub_eq_zero] at h_diff_zero
    exact h_diff_zero
  have hW_P0 : W * sys.P0 = ((c₀ : ℝ) : ℂ) • sys.P0 := by
    rw [← h_res.1]; exact hW_clean (fun _ => false) (fun _ _ => rfl)
  have hc₀_ne : c₀ ≠ 0 := by
    intro hc₀_zero
    have hW_P0_zero : W * sys.P0 = 0 := by rw [hW_P0, hc₀_zero]; ext ψ; simp
    have hP0_zero : sys.P0 = 0 := by
      calc sys.P0 = (W * W) * sys.P0 := by rw [hW_sq, one_mul]
        _ = W * (W * sys.P0) := by rw [mul_assoc]
        _ = 0 := by rw [hW_P0_zero, mul_zero]
    exact sys_P0_ne_zero_of_validDescriptorField D_field h_valid sys h_sys_checks hP0_zero
  have hU_inter : ∀ x y : BoxSlot3D L q_code → ZMod 2,
      (weylPauliZ x * weylPauliX y) * sys.P0 =
        sys.syndromeProjector (staticCSSPauliFlip D_field x y) * (weylPauliZ x * weylPauliX y) := by
    intro x y
    have h_flip : ∀ idx, (weylPauliZ x * weylPauliX y) * sys.checkProj idx =
        (if staticCSSPauliFlip D_field x y idx then 1 - sys.checkProj idx else sys.checkProj idx) *
          (weylPauliZ x * weylPauliX y) := fun idx => by
      rw [(h_sys_checks idx).1]; exact weylPauliZX_mul_staticCSSCheckProj D_field x y idx
    have h_int := intertwine_syndromeProjector_of_checkFlip sys h_flip (fun _ => false)
    have h_xor : (fun i => xor false (staticCSSPauliFlip D_field x y i)) =
        staticCSSPauliFlip D_field x y := by ext i; simp
    rw [h_res.1, h_xor] at h_int; exact h_int
  have hU_inv_right : ∀ x y : BoxSlot3D L q_code → ZMod 2,
      (weylPauliZ x * weylPauliX y) * (weylPauliX y * weylPauliZ x) = 1 := fun x y => by
    calc (weylPauliZ x * weylPauliX y) * (weylPauliX y * weylPauliZ x)
      _ = weylPauliZ x * (weylPauliX y * weylPauliX y) * weylPauliZ x := by simp only [mul_assoc]
      _ = 1 := by rw [weylPauliX_sq_eq_one y, mul_one, weylPauliZ_sq_eq_one x]
  have hU_inv_left : ∀ x y : BoxSlot3D L q_code → ZMod 2,
      (weylPauliX y * weylPauliZ x) * (weylPauliZ x * weylPauliX y) = 1 := fun x y => by
    calc (weylPauliX y * weylPauliZ x) * (weylPauliZ x * weylPauliX y)
      _ = weylPauliX y * (weylPauliZ x * weylPauliZ x) * weylPauliX y := by simp only [mul_assoc]
      _ = 1 := by rw [weylPauliZ_sq_eq_one x, mul_one, weylPauliX_sq_eq_one y]
  have hW_flip : ∀ x y : BoxSlot3D L q_code → ZMod 2,
      W * sys.syndromeProjector (staticCSSPauliFlip D_field x y) =
        (signScalar (∑ p, (x p * b p + a p * y p)) * ((c₀ : ℝ) : ℂ)) •
          sys.syndromeProjector (staticCSSPauliFlip D_field x y) := fun x y => by
    calc W * sys.syndromeProjector (staticCSSPauliFlip D_field x y)
      _ = W * (sys.syndromeProjector (staticCSSPauliFlip D_field x y) *
            ((weylPauliZ x * weylPauliX y) * (weylPauliX y * weylPauliZ x))) := by
        rw [hU_inv_right x y, mul_one]
      _ = (W * (weylPauliZ x * weylPauliX y)) * sys.P0 * (weylPauliX y * weylPauliZ x) := by
        rw [← mul_assoc (sys.syndromeProjector _), ← hU_inter x y]; simp only [mul_assoc]
      _ = (signScalar (∑ p, (x p * b p + a p * y p)) * ((c₀ : ℝ) : ℂ)) •
            (((weylPauliZ x * weylPauliX y) * sys.P0) * (weylPauliX y * weylPauliZ x)) := by
        rw [hW_comm_pauli x y, clm_smul_mul, clm_smul_mul, mul_assoc (weylPauliZ x * weylPauliX y) W sys.P0,
          hW_P0, clm_mul_smul, clm_smul_mul, smul_smul]
      _ = (signScalar (∑ p, (x p * b p + a p * y p)) * ((c₀ : ℝ) : ℂ)) •
            sys.syndromeProjector (staticCSSPauliFlip D_field x y) := by
        rw [hU_inter x y, mul_assoc, hU_inv_right x y, mul_one]
  let f_chk : IdxCSS[L, q_code, m_max] → PauliBitstringPair L q_code → ZMod 2 :=
    fun c p => boolToZMod2 (staticCSSPauliFlip D_field p.1 p.2 c)
  let φ_pair : PauliBitstringPair L q_code → ZMod 2 :=
    fun p => ∑ slot, (p.1 slot * b slot + a slot * p.2 slot)
  have hf_add : ∀ c v w, f_chk c (v + w) = f_chk c v + f_chk c w := fun c v w => by
    dsimp [f_chk]
    have h_add := congr_fun (staticCSSPauliFlip_add D_field v.1 w.1 v.2 w.2) c
    change boolToZMod2 (staticCSSPauliFlip D_field (v.1 + w.1) (v.2 + w.2) c) = _
    rw [h_add]; dsimp [syndromeXor, boolToZMod2]
    cases staticCSSPauliFlip D_field v.1 v.2 c <;>
      cases staticCSSPauliFlip D_field w.1 w.2 c <;> decide
  have hφ_add : ∀ v w, φ_pair (v + w) = φ_pair v + φ_pair w := fun v w => by
    dsimp [φ_pair]; rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun slot _ => ?_
    change (v.1 slot + w.1 slot) * b slot + a slot * (v.2 slot + w.2 slot) = _; ring
  have h_ker : ∀ p : PauliBitstringPair L q_code,
      (∀ c ∈ rcaCollarChecks sys C_RCA r A, f_chk c p = 0) → φ_pair p = 0 := by
    intro p hp_ker
    have h_clean : ∀ c ∈ rcaCollarChecks sys C_RCA r A,
        staticCSSPauliFlip D_field p.1 p.2 c = false := fun c hc => by
      have h0 := hp_ker c hc; dsimp [f_chk, boolToZMod2] at h0
      cases h_flip : staticCSSPauliFlip D_field p.1 p.2 c
      · rfl
      · rw [h_flip] at h0; revert h0; decide
    have h_eq_smul := (hW_clean (staticCSSPauliFlip D_field p.1 p.2) h_clean).symm.trans (hW_flip p.1 p.2)
    have h_conj : ((c₀ : ℝ) : ℂ) • sys.P0 =
        (signScalar (φ_pair p) * ((c₀ : ℝ) : ℂ)) • sys.P0 := by
      calc ((c₀ : ℝ) : ℂ) • sys.P0
        _ = (weylPauliX p.2 * weylPauliZ p.1) *
              ((((c₀ : ℝ) : ℂ) • sys.syndromeProjector (staticCSSPauliFlip D_field p.1 p.2)) *
                (weylPauliZ p.1 * weylPauliX p.2)) := by
          rw [clm_smul_mul, ← hU_inter p.1 p.2, clm_mul_smul, ← mul_assoc, hU_inv_left p.1 p.2, one_mul]
        _ = (weylPauliX p.2 * weylPauliZ p.1) *
              (((signScalar (φ_pair p) * ((c₀ : ℝ) : ℂ)) •
                sys.syndromeProjector (staticCSSPauliFlip D_field p.1 p.2)) *
                (weylPauliZ p.1 * weylPauliX p.2)) := by rw [← h_eq_smul]
        _ = (signScalar (φ_pair p) * ((c₀ : ℝ) : ℂ)) • sys.P0 := by
          rw [clm_smul_mul, ← hU_inter p.1 p.2, clm_mul_smul, ← mul_assoc, hU_inv_left p.1 p.2, one_mul]
    rcases _root_.zmod2_eq_zero_or_one (φ_pair p) with h0 | h1
    · exact h0
    · exfalso
      rw [h1] at h_conj
      change ((c₀ : ℝ) : ℂ) • sys.P0 = ((-1 : ℂ) * ((c₀ : ℝ) : ℂ)) • sys.P0 at h_conj
      have h_tr_eq := congr_arg hilbertTrace h_conj
      rw [← h_res.1, hilbertTrace_complex_smul_syndromeProjector,
        hilbertTrace_complex_smul_syndromeProjector, h_res.1] at h_tr_eq
      simp only [Complex.ofReal_re, Complex.mul_re, Complex.neg_re, Complex.one_re,
        Complex.neg_im, Complex.one_im, Complex.ofReal_im, mul_zero, sub_zero] at h_tr_eq
      have hP0_tr_pos : 0 < hilbertTrace sys.P0 := by
        rw [← h_res.1]
        exact hilbertTrace_pos_of_isStarProjection_ne_zero (h_res.2.1 (fun _ => false))
          (by rw [h_res.1]; exact sys_P0_ne_zero_of_validDescriptorField D_field h_valid sys h_sys_checks)
      exact hc₀_ne (by nlinarith)
  rcases exists_subset_sum_zmod2_of_ker_subset (rcaCollarChecks sys C_RCA r A)
      f_chk hf_add φ_pair hφ_add h_ker with ⟨α, hα_sub, hα_eq⟩
  have hab_eq_sum : (a, b) = ∑ c ∈ α, (staticCSSCheckPauliZ D_field c, staticCSSCheckPauliX D_field c) := by
    ext slot
    · have h1 := hα_eq (0, Pi.single slot 1)
      dsimp [φ_pair, f_chk] at h1
      simp only [ zero_mul, zero_add, mul_ite, Pi.single_apply, mul_one, mul_zero,
        Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte] at h1
      change a slot = (∑ c ∈ α, (staticCSSCheckPauliZ D_field c, staticCSSCheckPauliX D_field c)).1 slot
      rw [h1, Prod.fst_sum, Finset.sum_apply]
      refine Finset.sum_congr rfl fun c _ => ?_
      have h_flip := boolToZMod2_staticCSSPauliFlip_eq_sum_checkPauli D_field (0, Pi.single slot (1 : ZMod 2)) c
      (try dsimp only at h_flip ⊢)
      rw [h_flip]
      simp only [Pi.zero_apply, zero_mul, zero_add, Pi.single_apply, mul_ite, mul_one, mul_zero,
        Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
    · have h2 := hα_eq (Pi.single slot 1, 0)
      dsimp [φ_pair, f_chk] at h2
      simp only [ mul_zero, add_zero, Pi.single_apply, ite_mul, one_mul, zero_mul,
        Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte] at h2
      change b slot = (∑ c ∈ α, (staticCSSCheckPauliZ D_field c, staticCSSCheckPauliX D_field c)).2 slot
      rw [h2, Prod.snd_sum, Finset.sum_apply]
      refine Finset.sum_congr rfl fun c _ => ?_
      have h_flip := boolToZMod2_staticCSSPauliFlip_eq_sum_checkPauli D_field (Pi.single slot (1 : ZMod 2), 0) c
      (try dsimp only at h_flip ⊢)
      rw [h_flip]
      simp only [Pi.zero_apply, mul_zero, add_zero, Pi.single_apply, ite_mul, one_mul, zero_mul,
        Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
  have hab_mem : (a, b) ∈ stabilizerPauliSubmodule D_field := by
    rw [hab_eq_sum]
    exact Submodule.sum_mem _ fun c _ => Submodule.subset_span ⟨c, rfl⟩
  refine ⟨α, c₀, hα_sub, hab_mem, hc₀_ne, fun σ hσ => ?_⟩
  rcases (Finset.mem_filter.mp hσ).2 with ⟨x, y, rfl⟩
  rw [← (hW_comm_syn (staticCSSPauliFlip D_field x y)).eq, hW_flip x y]
  have h_sign : signScalar (∑ p, (x p * b p + a p * y p)) =
      ((spanningSurfaceSign α (staticCSSPauliFlip D_field x y) : ℝ) : ℂ) := by
    change signScalar (φ_pair (x, y)) = _
    rw [hα_eq (x, y), signScalar_sum_boolToZMod2_eq_spanningSurfaceSign]
  rw [h_sign, ← Complex.ofReal_mul]

private lemma list_sum_apply_ne_zero_exists_mem {α β : Type*} [AddCommMonoid β]
    {l : List (α → β)} {x : α} (h : l.sum x ≠ 0) :
    ∃ f ∈ l, f x ≠ 0 := by
  induction l with
  | nil => simp at h
  | cons hd tl ih =>
    rw [List.sum_cons, Pi.add_apply] at h
    by_cases h_hd : hd x = 0
    · rw [h_hd, zero_add] at h
      rcases ih h with ⟨f, hf, hfx⟩
      exact ⟨f, List.mem_cons_of_mem hd hf, hfx⟩
    · exact ⟨hd, List.mem_cons_self, h_hd⟩

private lemma worldlinePolymerLoop_supp_subset_cubeUnion
    {L q_code r_0 m_max R_cut : ℕ} [NeZero L]
    {C_RCA : ℝ}
    (D_field : Box3D L → LocalCSSDescriptor q_code r_0 m_max)
    (sys : SysCSS[L, q_code, m_max])
    (γ : WorldlineDysonPolymer L q_code)
    (hγ_valid : IsValidWorldlinePolymer D_field sys C_RCA R_cut γ)
    (slot : BoxSlot3D L q_code)
    (h_ne : worldlinePolymerLoopX γ slot ≠ 0 ∨ worldlinePolymerLoopZ γ slot ≠ 0) :
    slot.1 ∈ worldlinePolymerCubeUnion γ := by
  have h_ex_ξ : ∃ ξ ∈ γ.1, ξ.2.1 slot ≠ 0 ∨ ξ.2.2 slot ≠ 0 := by
    rcases h_ne with hX | hZ
    · rcases list_sum_apply_ne_zero_exists_mem hX with ⟨f, hf, hfx⟩
      rcases List.mem_map.mp hf with ⟨ξ, hξ, rfl⟩
      exact ⟨ξ, hξ, Or.inl hfx⟩
    · rcases list_sum_apply_ne_zero_exists_mem hZ with ⟨f, hf, hfx⟩
      rcases List.mem_map.mp hf with ⟨ξ, hξ, rfl⟩
      exact ⟨ξ, hξ, Or.inr hfx⟩
  rcases h_ex_ξ with ⟨ξ, hξ, hξ_slot⟩
  have h_in_A := (hγ_valid.2.1 ξ hξ).1 slot hξ_slot
  have h_mon : ξ.1 ∈ worldlinePolymerMonomers γ :=
    Finset.mem_union_left _ (List.mem_toFinset.mpr (List.mem_map_of_mem hξ))
  exact Finset.mem_biUnion.mpr ⟨ξ.1, h_mon, h_in_A⟩

/-- **Spanning-Surface Collar Containment for Bounded-Diameter Worldline Polymers**
    (`worldline_polymer_rca1_spanning_surface_collar_containment`;
    Part II, Lemma 3.9(ii) (`lem:worldline-factorization-time-reversal`), Equation `eq:P-gamma-spanning-surface`):
    For every valid worldline polymer $\gamma$ whose monomer cubes are contained in a lattice
    cube `boxCube x0 L_star` ($\mathrm{diam}(B(\gamma)) \le L^*$), Relative Cone Acyclicity
    ($\mathrm{RCA}_1$) guarantees that the loop Pauli operator $P(\gamma)$ has trivial bare
    logical coset $\mu(\gamma) = (0, 0)$ and canonical spanning check surface
    $\alpha(\gamma) \subseteq \mathcal{C}(B(\gamma)^+)$ satisfying `IsSpanningCheckSurfaceForPolymer`. -/
theorem worldline_polymer_rca1_spanning_surface_collar_containment
    {L q_code r_0 m_max w_0 L_star R_cut : ℕ} [NeZero L]
    {C_RCA : ℝ}
    (D_field : Box3D L → LocalCSSDescriptor q_code r_0 m_max) (h_valid : ValidDescriptorField D_field)
    (sys : SysCSS[L, q_code, m_max])
    (h_sys_checks : ∀ idx, sys.checkProj idx = staticCSSCheckProj D_field idx ∧
      sys.support idx = staticCSSCheckSupport D_field idx ∧ sys.weight idx = 1)
    (_h_geom : sys.IsGeometricallyLocal r_0 w_0)
    (h_tqo1 : SatisfiesTQO1 sys L_star) (h_tqo2 : SatisfiesSectorFilteredLinearTQO2 sys 1 L_star C_RCA)
    (hR_cut : 1 ≤ R_cut) (hR_le : R_cut ≤ L_star) (_hC_RCA : 0 ≤ C_RCA)
    (_h_cal : SatisfiesWorldlineScaleCalibration L L_star R_cut r_0 C_RCA)
    (γ : WorldlineDysonPolymer L q_code)
    (hγ_valid : IsValidWorldlinePolymer D_field sys C_RCA R_cut γ)
    (h_ball : ∃ x0 : Box3D L, ∀ p ∈ worldlinePolymerMonomers γ, ∀ v ∈ p.2, v ∈ boxCube x0 L_star) :
    worldlinePolymerSpanningSurface D_field sys C_RCA γ ⊆ worldlinePolymerBoundingBoxCollar sys C_RCA γ ∧
    worldlinePolymerLogicalCoset D_field sys C_RCA γ = (0, 0) ∧
    IsSpanningCheckSurfaceForPolymer D_field sys γ (0, 0)
      (worldlinePolymerSpanningSurface D_field sys C_RCA γ) := by
  rcases h_ball with ⟨x0_in, hx0_in⟩
  let r_cap := min L_star L
  have hr_cap_1 : 1 ≤ r_cap := le_min (le_trans hR_cut hR_le) (NeZero.pos L)
  have hr_cap_L : r_cap ≤ L := Nat.min_le_right L_star L
  have hr_cap_Lstar : r_cap ≤ L_star := Nat.min_le_left L_star L
  have h_enc_cap : HasEnclosingPolymerBall γ r_cap := by
    refine ⟨x0_in, fun v hv => ?_⟩
    rcases Finset.mem_biUnion.mp hv with ⟨p, hp, hvp⟩
    have hv_Lstar := hx0_in p hp v hvp
    rw [boxCube, Finset.mem_filter] at hv_Lstar ⊢
    refine ⟨Finset.mem_univ v, fun i => ⟨(hv_Lstar.2 i).1, ?_⟩⟩
    have h1 := (hv_Lstar.2 i).2
    have h2 := (v i).isLt
    omega
  have h_ex_diam : ∃ r ≤ L, 1 ≤ r ∧ HasEnclosingPolymerBall γ r :=
    ⟨r_cap, hr_cap_L, hr_cap_1, h_enc_cap⟩
  let r_diam := worldlinePolymerDiameter γ
  have hr_diam_eq : r_diam = Nat.find h_ex_diam := dif_pos h_ex_diam
  have hr_diam_spec := Nat.find_spec h_ex_diam
  have hr_diam_1 : 1 ≤ r_diam := by rw [hr_diam_eq]; exact hr_diam_spec.2.1
  have hr_diam_cap : r_diam ≤ r_cap := by
    rw [hr_diam_eq]
    exact Nat.find_min' h_ex_diam ⟨hr_cap_L, hr_cap_1, h_enc_cap⟩
  have hr_diam_Lstar : r_diam ≤ L_star := le_trans hr_diam_cap hr_cap_Lstar
  have h_enc_diam : HasEnclosingPolymerBall γ r_diam := by
    rw [hr_diam_eq]; exact hr_diam_spec.2.2
  let x0_diam := Classical.choose h_enc_diam
  have hx0_diam_sub : worldlinePolymerCubeUnion γ ⊆ boxCube x0_diam r_diam :=
    Classical.choose_spec h_enc_diam
  have h_bbox_eq : worldlinePolymerBoundingBox γ = boxCube x0_diam r_diam :=
    dif_pos h_enc_diam
  have h_collar_eq : worldlinePolymerBoundingBoxCollar sys C_RCA γ =
      rcaCollarChecks sys C_RCA r_diam (boxCube x0_diam r_diam) := by
    unfold worldlinePolymerBoundingBoxCollar
    rw [h_bbox_eq]
  let a := worldlinePolymerLoopX γ
  let b := worldlinePolymerLoopZ γ
  have h_ab_supp : ∀ slot : BoxSlot3D L q_code,
      a slot ≠ 0 ∨ b slot ≠ 0 → slot.1 ∈ boxCube x0_diam r_diam := fun slot h_ne =>
    hx0_diam_sub (worldlinePolymerLoop_supp_subset_cubeUnion D_field sys γ hγ_valid slot h_ne)
  have h_ab_closed : staticCSSPauliFlip D_field a b = fun _ => false := hγ_valid.2.2.1.2
  rcases hermitianPauliZX_syndrome_eigenvalue_and_collar_surface D_field h_valid sys h_sys_checks
      h_tqo1 h_tqo2 hr_diam_1 hr_diam_Lstar x0_diam a b h_ab_supp h_ab_closed with
    ⟨α, c₀, hα_sub, hab_mem, hc₀_ne, hα_eig⟩
  have h_loc_ex : ∃ α' : Finset (IdxCSS[L, q_code, m_max]),
      α' ⊆ worldlinePolymerBoundingBoxCollar sys C_RCA γ ∧
      IsSpanningCheckSurfaceForPolymer D_field sys γ (0, 0) α' := by
    refine ⟨α, by rw [h_collar_eq]; exact hα_sub, ?_⟩
    unfold IsSpanningCheckSurfaceForPolymer; (try dsimp only)
    have h_zero_adj : (hermitianPauliZX (0 : BoxSlot3D L q_code → ZMod 2)
        (0 : BoxSlot3D L q_code → ZMod 2))† = 1 := by
      unfold hermitianPauliZX
      rw [if_pos (by simp), weylPauliZ_zero, weylPauliX_zero, mul_one,
        ← ContinuousLinearMap.star_eq_adjoint, star_one]
    rw [h_zero_adj, one_mul]
    rcases list_prod_map_worldlineJumpOpZX_eq_signScalar_smul γ.1.reverse with ⟨s_loop, hs_loop⟩
    have h_sum_X : (γ.1.reverse.map (fun ξ => ξ.2.1)).sum = a := by
      dsimp [a, worldlinePolymerLoopX]; rw [List.map_reverse, List.sum_reverse]
    have h_sum_Z : (γ.1.reverse.map (fun ξ => ξ.2.2)).sum = b := by
      dsimp [b, worldlinePolymerLoopZ]; rw [List.map_reverse, List.sum_reverse]
    rw [h_sum_X, h_sum_Z] at hs_loop
    have h_loop_eq : ∃ z : ℂ, (z.re ≠ 0 ∨ (Complex.I * z).re ≠ 0) ∧
        worldlinePolymerLoopOp γ = z • hermitianPauliZX a b := by
      change ∃ z : ℂ, (z.re ≠ 0 ∨ (Complex.I * z).re ≠ 0) ∧
        worldlinePolymerLoopOpZX γ = z • hermitianPauliZX a b
      unfold worldlinePolymerLoopOpZX; rw [hs_loop]; unfold hermitianPauliZX
      have hs_re : (signScalar s_loop).re ≠ 0 := by
        rcases _root_.zmod2_eq_zero_or_one s_loop with h0 | h1 <;> [rw [h0]; rw [h1]] <;> simp [signScalar]
      split_ifs with h_symp
      · exact ⟨signScalar s_loop, Or.inl hs_re, rfl⟩
      · refine ⟨-Complex.I * signScalar s_loop, Or.inr ?_, ?_⟩
        · have h_mul_I : Complex.I * (-Complex.I * signScalar s_loop) = signScalar s_loop := by
            calc Complex.I * (-Complex.I * signScalar s_loop)
              _ = -(Complex.I * Complex.I) * signScalar s_loop := by ring
              _ = signScalar s_loop := by rw [Complex.I_mul_I, neg_neg, one_mul]
          rw [h_mul_I]; exact hs_re
        · rw [smul_smul]; congr 1
          calc signScalar s_loop
            _ = (-(Complex.I * Complex.I)) * signScalar s_loop := by rw [Complex.I_mul_I, neg_neg, one_mul]
            _ = (-Complex.I * signScalar s_loop) * Complex.I := by ring
    rcases h_loop_eq with ⟨z, hz_ne, hz_op⟩
    have h_res := _root_.syndrome_resolution_indexed sys
    have hP0_mem : (fun _ : IdxCSS[L, q_code, m_max] => false) ∈ realizableSyndromes D_field := by
      rw [realizableSyndromes, Finset.mem_filter]; refine ⟨Finset.mem_univ _, 0, 0, ?_⟩
      ext idx; rcases idx with ⟨v, s⟩ | ⟨v, i⟩ | ⟨v, i⟩ <;> simp [staticCSSPauliFlip]
    have h_sign_P0 : spanningSurfaceSign α (fun _ => false) = 1 := by unfold spanningSurfaceSign; simp
    have h_tr_w : ∀ (w : ℂ) (σ : IdxCSS[L, q_code, m_max] → Bool),
        σ ∈ realizableSyndromes D_field →
        hilbertTrace (sys.syndromeProjector σ * (w • worldlinePolymerLoopOp γ)) =
          (w * z).re * spanningSurfaceSign α σ * c₀ * hilbertTrace sys.P0 := by
      intro w σ hσ
      rw [hz_op, smul_smul, clm_mul_smul, hα_eig σ hσ, smul_smul, hilbertTrace_complex_smul_syndromeProjector]
      rcases (Finset.mem_filter.mp hσ).2 with ⟨x, y, rfl⟩
      rw [hilbertTrace_syndromeProjector_staticCSSPauliFlip_eq_P0 D_field h_valid sys h_sys_checks x y]
      simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]; ring
    have h_tr_P0 : ∀ w : ℂ, hilbertTrace (sys.P0 * (w • worldlinePolymerLoopOp γ)) =
        (w * z).re * c₀ * hilbertTrace sys.P0 := by
      intro w; rw [← h_res.1, h_tr_w w (fun _ => false) hP0_mem, h_sign_P0, h_res.1]; ring
    have hP0_tr_pos : 0 < hilbertTrace sys.P0 := by
      rw [← h_res.1]
      exact hilbertTrace_pos_of_isStarProjection_ne_zero (h_res.2.1 (fun _ => false))
        (by rw [h_res.1]; exact sys_P0_ne_zero_of_validDescriptorField D_field h_valid sys h_sys_checks)
    refine ⟨?_, fun σ hσ => ⟨?_, ?_⟩⟩
    · rcases hz_ne with hz1 | hzI
      · left; have h1 := h_tr_P0 1; rw [one_smul, one_mul] at h1; rw [h1]
        exact mul_ne_zero (mul_ne_zero hz1 hc₀_ne) (ne_of_gt hP0_tr_pos)
      · right; rw [h_tr_P0 Complex.I]
        exact mul_ne_zero (mul_ne_zero hzI hc₀_ne) (ne_of_gt hP0_tr_pos)
    · have h1 := h_tr_w 1 σ hσ; have h0 := h_tr_P0 1
      rw [one_smul, one_mul] at h1 h0; rw [h1, h0]; ring
    · rw [h_tr_w Complex.I σ hσ, h_tr_P0 Complex.I]; ring
  have h_surf_eq : worldlinePolymerSpanningSurface D_field sys C_RCA γ =
      Classical.choose h_loc_ex := dif_pos h_loc_ex
  have h_coset_eq : worldlinePolymerLogicalCoset D_field sys C_RCA γ = (0, 0) :=
    bareLogicalProjection_eq_zero_of_mem_stabilizerPauliSubmodule D_field hab_mem
  rw [h_surf_eq, h_coset_eq]
  exact ⟨(Classical.choose_spec h_loc_ex).1, rfl, (Classical.choose_spec h_loc_ex).2⟩

lemma spanningSurfaceSign_abs {L q_code m_max : ℕ}
    (α : Finset (IdxCSS[L, q_code, m_max]))
    (σ : IdxCSS[L, q_code, m_max] → Bool) :
    |spanningSurfaceSign α σ| = 1 := by
  unfold spanningSurfaceSign
  split_ifs <;> simp

lemma symplecticPauliSign_abs {L q_code : ℕ}
    (ν μ : PauliBitstringPair L q_code) :
    |symplecticPauliSign ν μ| = 1 := by
  unfold symplecticPauliSign
  split_ifs <;> simp

lemma worldlinePolymerWeight_abs {L q_code r_0 m_max : ℕ} [NeZero L]
    (D_field : Box3D L → LocalCSSDescriptor q_code r_0 m_max)
    (sys : SysCSS[L, q_code, m_max]) (C_RCA β : ℝ)
    (V : QuasiLocalPerturbation 3 L (SiteCSS[L, q_code]))
    (d_loc : ℕ → Finset (Box3D L) → (IdxCSS[L, q_code, m_max] → Bool) → ℝ)
    (ν : PauliBitstringPair L q_code) (γ : WorldlineDysonPolymer L q_code)
    (σ : IdxCSS[L, q_code, m_max] → Bool) :
    |worldlinePolymerWeight D_field sys C_RCA β V d_loc ν γ σ| =
      |worldlinePolymerMicroWeight D_field sys C_RCA β V d_loc γ
        (restrictSyndromeToCollar (worldlinePolymerNativeCollar sys C_RCA γ) σ)| := by
  unfold worldlinePolymerWeight
  rw [abs_mul, abs_mul, symplecticPauliSign_abs, spanningSurfaceSign_abs, one_mul, one_mul]

lemma worldlinePolymerMicroWeight_abs {L q_code r_0 m_max : ℕ} [NeZero L]
    (D_field : Box3D L → LocalCSSDescriptor q_code r_0 m_max)
    (sys : SysCSS[L, q_code, m_max]) (C_RCA β : ℝ)
    (V : QuasiLocalPerturbation 3 L (SiteCSS[L, q_code]))
    (d_loc : ℕ → Finset (Box3D L) → (IdxCSS[L, q_code, m_max] → Bool) → ℝ)
    (γ : WorldlineDysonPolymer L q_code)
    (σ₀ : IdxCSS[L, q_code, m_max] → Bool) :
    |worldlinePolymerMicroWeight D_field sys C_RCA β V d_loc γ σ₀| =
      |worldlinePolymerLoopAmplitude D_field sys C_RCA V γ σ₀| *
        |∫ τ : Fin γ.1.length → ℝ,
          if InOrderedDysonSimplex β τ then
            Real.exp (-worldlineBareAction D_field sys γ.1 σ₀ β τ) *
              ∏ ϑ ∈ γ.2, worldlineMayerBondFactor D_field γ.1 d_loc σ₀ β ϑ τ
          else 0| := by
  unfold worldlinePolymerMicroWeight
  rw [abs_mul, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul]

lemma pauliOffDiagonalTerm_eq_zero_of_term_zero {L q_code m_max : ℕ}
    (sys : SysCSS[L, q_code, m_max])
    (V : QuasiLocalPerturbation 3 L (SiteCSS[L, q_code]))
    (r : ℕ) (A : Finset (Box3D L))
    (h_zero : V.term r A = 0) :
    pauliOffDiagonalTerm sys V r A = 0 := by
  unfold pauliOffDiagonalTerm syndromePinchOp
  rw [h_zero]
  simp

lemma worldlineSyndromeShiftBlockOp_eq_zero_of_term_zero {L q_code r_0 m_max : ℕ}
    (D_field : Box3D L → LocalCSSDescriptor q_code r_0 m_max)
    (sys : SysCSS[L, q_code, m_max])
    (V : QuasiLocalPerturbation 3 L (SiteCSS[L, q_code]))
    (ξ : WorldlineJumpMonomer L q_code)
    (h_zero : V.term ξ.1.1 ξ.1.2 = 0) :
    worldlineSyndromeShiftBlockOp D_field sys V ξ = 0 := by
  unfold worldlineSyndromeShiftBlockOp
  rw [pauliOffDiagonalTerm_eq_zero_of_term_zero sys V ξ.1.1 ξ.1.2 h_zero]
  simp

lemma worldlinePolymerWeightedLoopOp_eq_zero_of_nonempty_zero {L q_code r_0 m_max : ℕ}
    (D_field : Box3D L → LocalCSSDescriptor q_code r_0 m_max)
    (sys : SysCSS[L, q_code, m_max])
    (V : QuasiLocalPerturbation 3 L (SiteCSS[L, q_code]))
    (γ : WorldlineDysonPolymer L q_code)
    (h_ne : γ.1 ≠ [])
    (h_zero : ∀ ξ ∈ γ.1, V.term ξ.1.1 ξ.1.2 = 0) :
    worldlinePolymerWeightedLoopOp D_field sys V γ = 0 := by
  unfold worldlinePolymerWeightedLoopOp
  have h_rev_ne : γ.1.reverse ≠ [] := by simp [h_ne]
  rcases List.exists_cons_of_ne_nil h_rev_ne with ⟨ξ₀, l, h_eq⟩
  have hξ₀_mem : ξ₀ ∈ γ.1 := by
    have : ξ₀ ∈ γ.1.reverse := by rw [h_eq]; exact List.mem_cons_self
    exact List.mem_reverse.mp this
  rw [h_eq, List.map_cons, List.prod_cons,
    worldlineSyndromeShiftBlockOp_eq_zero_of_term_zero D_field sys V ξ₀ (h_zero ξ₀ hξ₀_mem),
    zero_mul]

lemma worldlinePolymerLoopAmplitude_eq_zero_of_weightedLoopOp_zero
    {L q_code r_0 m_max : ℕ} [NeZero L]
    (D_field : Box3D L → LocalCSSDescriptor q_code r_0 m_max)
    (sys : SysCSS[L, q_code, m_max]) (C_RCA : ℝ)
    (V : QuasiLocalPerturbation 3 L (SiteCSS[L, q_code]))
    (γ : WorldlineDysonPolymer L q_code)
    (σ₀ : IdxCSS[L, q_code, m_max] → Bool)
    (h_zero : worldlinePolymerWeightedLoopOp D_field sys V γ = 0) :
    worldlinePolymerLoopAmplitude D_field sys C_RCA V γ σ₀ = 0 := by
  unfold worldlinePolymerLoopAmplitude hilbertTrace
  (try dsimp only)
  rw [h_zero, mul_zero]
  simp

lemma worldlinePolymerWeight_eq_zero_of_valid_and_J_zero
    {L q_code r_0 m_max R_cut : ℕ} [NeZero L]
    (D_field : Box3D L → LocalCSSDescriptor q_code r_0 m_max)
    (sys : SysCSS[L, q_code, m_max]) (C_RCA β : ℝ)
    (V : QuasiLocalPerturbation 3 L (SiteCSS[L, q_code])) (f : ℕ → ℝ)
    (hV_zero : ∀ r ∈ Finset.Icc 1 (min R_cut L), ∀ A ∈ boxCubes 3 L r, ‖V.term r A‖ ≤ 0 * f r)
    (d_loc : ℕ → Finset (Box3D L) → (IdxCSS[L, q_code, m_max] → Bool) → ℝ)
    (ν : PauliBitstringPair L q_code) (γ : WorldlineDysonPolymer L q_code)
    (hγ : IsValidWorldlinePolymer D_field sys C_RCA R_cut γ)
    (σ : IdxCSS[L, q_code, m_max] → Bool) :
    worldlinePolymerWeight D_field sys C_RCA β V d_loc ν γ σ = 0 := by
  have h_ne : γ.1 ≠ [] := by
    intro h_nil
    have h_len := hγ.2.2.1
    rw [h_nil, List.length_nil] at h_len
    omega
  have h_terms_zero : ∀ ξ ∈ γ.1, V.term ξ.1.1 ξ.1.2 = 0 := by
    intro ξ hξ
    have hp_mem : ξ.1 ∈ worldlinePolymerMonomers γ := by
      unfold worldlinePolymerMonomers
      exact Finset.mem_union_left _ (List.mem_toFinset.mpr (List.mem_map_of_mem hξ))
    have hp_scale := hγ.1 ξ.1 hp_mem
    unfold worldlineScaleCubeFinset at hp_scale
    rw [Finset.mem_biUnion] at hp_scale
    rcases hp_scale with ⟨r, hr, hA⟩
    rw [Finset.mem_image] at hA
    rcases hA with ⟨A, hA_mem, h_pair⟩
    have hr_eq : r = ξ.1.1 := congrArg Prod.fst h_pair
    have hA_eq : A = ξ.1.2 := congrArg Prod.snd h_pair
    subst hr_eq hA_eq
    have h_norm := hV_zero ξ.1.1 hr ξ.1.2 hA_mem
    rw [zero_mul] at h_norm
    exact norm_le_zero_iff.mp h_norm
  have h_wloop :=
    worldlinePolymerWeightedLoopOp_eq_zero_of_nonempty_zero D_field sys V γ h_ne h_terms_zero
  have h_amp :=
    worldlinePolymerLoopAmplitude_eq_zero_of_weightedLoopOp_zero D_field sys C_RCA V γ
      (restrictSyndromeToCollar (worldlinePolymerNativeCollar sys C_RCA γ) σ) h_wloop
  unfold worldlinePolymerWeight worldlinePolymerMicroWeight
  rw [h_amp, mul_zero, zero_mul, mul_zero]

lemma worldlineUrsellPhi_eq_zero_of_J_zero
    {L q_code r_0 m_max R_cut : ℕ} [NeZero L]
    (D_field : Box3D L → LocalCSSDescriptor q_code r_0 m_max)
    (sys : SysCSS[L, q_code, m_max]) (C_RCA β : ℝ)
    (V : QuasiLocalPerturbation 3 L (SiteCSS[L, q_code])) (f : ℕ → ℝ)
    (hV_zero : ∀ r ∈ Finset.Icc 1 (min R_cut L), ∀ A ∈ boxCubes 3 L r, ‖V.term r A‖ ≤ 0 * f r)
    (d_loc : ℕ → Finset (Box3D L) → (IdxCSS[L, q_code, m_max] → Bool) → ℝ)
    (ν : PauliBitstringPair L q_code)
    (fp : WorldlineUrsellFootprint L q_code m_max)
    (σ : IdxCSS[L, q_code, m_max] → Bool) :
    worldlineUrsellPhi D_field sys C_RCA R_cut β V d_loc ν fp σ = 0 := by
  unfold worldlineUrsellPhi
  convert tsum_zero with K
  split_ifs with hK
  · rcases hK with ⟨hK_valid, _⟩
    rcases List.exists_cons_of_ne_nil hK_valid.1 with ⟨γ₀, K_tail, hK_eq⟩
    have hγ₀ : IsValidWorldlinePolymer D_field sys C_RCA R_cut γ₀ :=
      hK_valid.2.1 γ₀ (by rw [hK_eq]; exact List.mem_cons_self)
    unfold worldlineClusterUrsellWeight
    rw [hK_eq, List.map_cons, List.prod_cons,
      worldlinePolymerWeight_eq_zero_of_valid_and_J_zero D_field sys C_RCA β V f hV_zero d_loc ν γ₀ hγ₀ σ,
      zero_mul, mul_zero]
  · rfl

lemma norm_sq_eq_sum_syndromeProjector_norm_sq_local {L q_code m_max : ℕ}
    (sys : SysCSS[L, q_code, m_max]) (φ : ℋ_CSS[L, q_code]) :
    ‖φ‖ ^ 2 = ∑ σ : IdxCSS[L, q_code, m_max] → Bool, ‖sys.syndromeProjector σ φ‖ ^ 2 := by
  have h_one : perturbedSyndromeDiagOp sys 1 = 1 :=
    perturbed_syndromeDiagOp_eq_self_of_commute sys (fun σ => Commute.one_left _)
  have h_re := perturbed_re_inner_syndromeDiagOp_eq_sum sys 1 φ
  rw [h_one] at h_re
  simp only [ContinuousLinearMap.one_apply, inner_self_eq_norm_sq] at h_re
  exact h_re

lemma syndromePinchOp_norm_le_local {L q_code m_max : ℕ}
    (sys : SysCSS[L, q_code, m_max]) (M : ℬ_CSS[L, q_code]) :
    ‖syndromePinchOp sys M‖ ≤ ‖M‖ := by
  refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg M) fun ψ => ?_
  have h_res := PerturbedThermalBarrier.syndrome_resolution_indexed sys
  have h_sq : ‖syndromePinchOp sys M ψ‖ ^ 2 ≤ (‖M‖ * ‖ψ‖) ^ 2 := by
    rw [norm_sq_eq_sum_syndromeProjector_norm_sq_local sys (syndromePinchOp sys M ψ),
      mul_pow, norm_sq_eq_sum_syndromeProjector_norm_sq_local sys ψ, Finset.mul_sum]
    refine Finset.sum_le_sum fun σ _ => ?_
    have h_act : sys.syndromeProjector σ (syndromePinchOp sys M ψ) =
        sys.syndromeProjector σ (M (sys.syndromeProjector σ ψ)) := by
      change (sys.syndromeProjector σ * perturbedSyndromeDiagOp sys M) ψ = _
      rw [(perturbed_syndromeDiagOp_mul_syndromeProjector sys M σ).2.1]
      rfl
    rw [h_act]
    have h_proj := isStarProjection_norm_sq_apply_le_bhm (h_res.2.1 σ) (M (sys.syndromeProjector σ ψ))
    have h_op := pow_le_pow_left₀ (norm_nonneg _) (M.le_opNorm (sys.syndromeProjector σ ψ)) 2
    linarith [mul_pow ‖M‖ ‖sys.syndromeProjector σ ψ‖ 2]
  exact nonneg_le_nonneg_of_sq_le_sq (mul_nonneg (norm_nonneg M) (norm_nonneg ψ)) (by linarith)

lemma pauliOffDiagonalTerm_norm_le_two_mul_norm {L q_code m_max : ℕ}
    (sys : SysCSS[L, q_code, m_max])
    (V : QuasiLocalPerturbation 3 L (SiteCSS[L, q_code]))
    (r : ℕ) (A : Finset (Box3D L)) :
    ‖pauliOffDiagonalTerm sys V r A‖ ≤ 2 * ‖V.term r A‖ := by
  unfold pauliOffDiagonalTerm
  have h1 := norm_sub_le (V.term r A) (syndromePinchOp sys (V.term r A))
  have h2 := syndromePinchOp_norm_le_local sys (V.term r A)
  linarith

lemma worldlineSyndromeShiftBlockOp_norm_le {L q_code r_0 m_max : ℕ}
    (D_field : Box3D L → LocalCSSDescriptor q_code r_0 m_max)
    (sys : SysCSS[L, q_code, m_max])
    (V : QuasiLocalPerturbation 3 L (SiteCSS[L, q_code]))
    (ξ : WorldlineJumpMonomer L q_code) :
    ‖worldlineSyndromeShiftBlockOp D_field sys V ξ‖ ≤ ‖pauliOffDiagonalTerm sys V ξ.1.1 ξ.1.2‖ := by
  let M := pauliOffDiagonalTerm sys V ξ.1.1 ξ.1.2
  let δ := staticCSSPauliFlip D_field ξ.2.1 ξ.2.2
  let B := worldlineSyndromeShiftBlockOp D_field sys V ξ
  refine ContinuousLinearMap.opNorm_le_bound B (norm_nonneg M) fun ψ => ?_
  have h_res := PerturbedThermalBarrier.syndrome_resolution_indexed sys
  have h_sq : ‖B ψ‖ ^ 2 ≤ (‖M‖ * ‖ψ‖) ^ 2 := by
    rw [norm_sq_eq_sum_syndromeProjector_norm_sq_local sys (B ψ),
      mul_pow, norm_sq_eq_sum_syndromeProjector_norm_sq_local sys ψ]
    have h_proj_B : ∀ τ : IdxCSS[L, q_code, m_max] → Bool,
        ‖sys.syndromeProjector τ (B ψ)‖ ^ 2 ≤
          ‖M‖ ^ 2 * ‖sys.syndromeProjector (syndromeXor δ τ) ψ‖ ^ 2 := by
      intro τ
      have h_orth : sys.syndromeProjector τ * B =
          if syndromeXor δ τ ∈ realizableSyndromes D_field then
            sys.syndromeProjector τ * M * sys.syndromeProjector (syndromeXor δ τ)
          else 0 := by
        dsimp [B, worldlineSyndromeShiftBlockOp]
        rw [Finset.mul_sum]
        have h_term : ∀ σ ∈ realizableSyndromes D_field,
            sys.syndromeProjector τ *
              (sys.syndromeProjector (syndromeXor δ σ) * M * sys.syndromeProjector σ) =
            if σ = syndromeXor δ τ then
              sys.syndromeProjector τ * M * sys.syndromeProjector (syndromeXor δ τ)
            else 0 := by
          intro σ _
          by_cases h_eq : σ = syndromeXor δ τ
          · rw [if_pos h_eq, h_eq, syndromeXor_cancel_left]
            have h_idem := (h_res.2.1 τ).1
            calc sys.syndromeProjector τ *
                  (sys.syndromeProjector τ * M * sys.syndromeProjector (syndromeXor δ τ))
              _ = (sys.syndromeProjector τ * sys.syndromeProjector τ) * M *
                    sys.syndromeProjector (syndromeXor δ τ) := by simp only [mul_assoc]
              _ = sys.syndromeProjector τ * M * sys.syndromeProjector (syndromeXor δ τ) := by
                  rw [h_idem]
          · rw [if_neg h_eq]
            have h_ne : τ ≠ syndromeXor δ σ := by
              intro h_con
              apply h_eq
              rw [h_con, syndromeXor_cancel_left]
            calc sys.syndromeProjector τ *
                  (sys.syndromeProjector (syndromeXor δ σ) * M * sys.syndromeProjector σ)
              _ = (sys.syndromeProjector τ * sys.syndromeProjector (syndromeXor δ σ)) *
                    M * sys.syndromeProjector σ := by simp only [mul_assoc]
              _ = 0 := by rw [h_res.2.2.1 τ (syndromeXor δ σ) h_ne, zero_mul, zero_mul]
        rw [Finset.sum_congr rfl h_term, Finset.sum_ite_eq']
      have h_apply : sys.syndromeProjector τ (B ψ) = (sys.syndromeProjector τ * B) ψ := rfl
      rw [h_apply, h_orth]
      split_ifs
      · change ‖sys.syndromeProjector τ (M (sys.syndromeProjector (syndromeXor δ τ) ψ))‖ ^ 2 ≤ _
        have h_p := isStarProjection_norm_sq_apply_le_bhm (h_res.2.1 τ)
          (M (sys.syndromeProjector (syndromeXor δ τ) ψ))
        have h_m := pow_le_pow_left₀ (norm_nonneg _)
          (M.le_opNorm (sys.syndromeProjector (syndromeXor δ τ) ψ)) 2
        linarith [mul_pow ‖M‖ ‖sys.syndromeProjector (syndromeXor δ τ) ψ‖ 2]
      · simp
        positivity
    calc ∑ τ, ‖sys.syndromeProjector τ (B ψ)‖ ^ 2
      _ ≤ ∑ τ, ‖M‖ ^ 2 * ‖sys.syndromeProjector (syndromeXor δ τ) ψ‖ ^ 2 :=
        Finset.sum_le_sum fun τ _ => h_proj_B τ
      _ = ‖M‖ ^ 2 * ∑ τ, ‖sys.syndromeProjector (syndromeXor δ τ) ψ‖ ^ 2 := by
        rw [← Finset.mul_sum]
      _ = ‖M‖ ^ 2 * ∑ σ, ‖sys.syndromeProjector σ ψ‖ ^ 2 := by
        congr 1
        refine Fintype.sum_bijective (syndromeXor δ)
          (Function.Involutive.bijective (syndromeXor_cancel_left δ)) _ _ (fun _ => rfl)
  exact nonneg_le_nonneg_of_sq_le_sq (mul_nonneg (norm_nonneg M) (norm_nonneg ψ)) (by linarith)

lemma list_prod_opNorm_le {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [Nontrivial E] (l : List (E →L[ℂ] E)) :
    ‖l.prod‖ ≤ (l.map norm).prod := by
  induction l with
  | nil => simp
  | cons hd tl ih =>
    rw [List.prod_cons, List.map_cons, List.prod_cons]
    exact le_trans (norm_mul_le hd tl.prod)
      (mul_le_mul_of_nonneg_left ih (norm_nonneg hd))

lemma list_prod_reverse_map_opNorm_le {α E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] [Nontrivial E] (f : α → (E →L[ℂ] E)) (l : List α) :
    ‖(l.reverse.map f).prod‖ ≤ (l.map (fun x => ‖f x‖)).prod := by
  induction l with
  | nil => simp
  | cons hd tl ih =>
    rw [List.reverse_cons, List.map_append, List.prod_append, List.map_cons, List.map_nil,
      List.prod_cons, List.prod_nil, mul_one, List.map_cons, List.prod_cons,
      mul_comm ‖f hd‖]
    exact le_trans (norm_mul_le _ _)
      (mul_le_mul_of_nonneg_right ih (norm_nonneg (f hd)))

lemma worldlinePolymerWeightedLoopOp_norm_le {L q_code r_0 m_max : ℕ}
    (D_field : Box3D L → LocalCSSDescriptor q_code r_0 m_max)
    (sys : SysCSS[L, q_code, m_max])
    (V : QuasiLocalPerturbation 3 L (SiteCSS[L, q_code]))
    (γ : WorldlineDysonPolymer L q_code) :
    ‖worldlinePolymerWeightedLoopOp D_field sys V γ‖ ≤
      (γ.1.map (fun ξ => ‖worldlineSyndromeShiftBlockOp D_field sys V ξ‖)).prod :=
  list_prod_reverse_map_opNorm_le (worldlineSyndromeShiftBlockOp D_field sys V) γ.1

lemma abs_hilbertTrace_isStarProjection_mul_div_le
    {L q_code : ℕ}
    (P X : ℬ_CSS[L, q_code]) (hP : IsStarProjection P) :
    |hilbertTrace (P * X) / hilbertTrace P| ≤ ‖X‖ := by
  have hP_adj : P† = P := ContinuousLinearMap.isSelfAdjoint_iff'.mp hP.2
  have h_cyc : hilbertTrace (P * X) = hilbertTrace (P * X * P) := by
    calc hilbertTrace (P * X)
      _ = hilbertTrace ((P * P) * X) := by rw [hP.1]
      _ = hilbertTrace (P * (P * X)) := by rw [mul_assoc]
      _ = hilbertTrace ((P * X) * P) := hilbertTrace_mul_comm_aux P (P * X)
  have h_tr_P : ∀ ω : ManyBodyConfig (SiteCSS[L, q_code]),
      RCLike.re (inner ℂ (basisVecGlobal (SiteCSS[L, q_code]) ω) (P (basisVecGlobal (SiteCSS[L, q_code]) ω))) =
        ‖P (basisVecGlobal (SiteCSS[L, q_code]) ω)‖ ^ 2 := by
    intro ω
    let e := basisVecGlobal (SiteCSS[L, q_code]) ω
    calc RCLike.re (inner ℂ e (P e))
      _ = RCLike.re (inner ℂ e ((P * P) e)) := by rw [hP.1]
      _ = RCLike.re (inner ℂ ((P†) e) (P e)) := by
          rw [ContinuousLinearMap.mul_apply, ContinuousLinearMap.adjoint_inner_left]
      _ = RCLike.re (inner ℂ (P e) (P e)) := by rw [hP_adj]
      _ = ‖P e‖ ^ 2 := inner_self_eq_norm_sq (P e)
  have h_tr_PX : ∀ ω : ManyBodyConfig (SiteCSS[L, q_code]),
      |RCLike.re (inner ℂ (basisVecGlobal (SiteCSS[L, q_code]) ω) ((P * X * P) (basisVecGlobal (SiteCSS[L, q_code]) ω)))| ≤
        ‖X‖ * ‖P (basisVecGlobal (SiteCSS[L, q_code]) ω)‖ ^ 2 := by
    intro ω
    let e := basisVecGlobal (SiteCSS[L, q_code]) ω
    have h_in : inner ℂ e ((P * X * P) e) = inner ℂ (P e) (X (P e)) := by
      calc inner ℂ e ((P * X * P) e)
        _ = inner ℂ e (P (X (P e))) := rfl
        _ = inner ℂ ((P†) e) (X (P e)) := (ContinuousLinearMap.adjoint_inner_left P (X (P e)) e).symm
        _ = inner ℂ (P e) (X (P e)) := by rw [hP_adj]
    rw [h_in]
    calc |RCLike.re (inner ℂ (P e) (X (P e)))|
      _ ≤ ‖inner ℂ (P e) (X (P e))‖ := RCLike.abs_re_le_norm _
      _ ≤ ‖P e‖ * ‖X (P e)‖ := norm_inner_le_norm (P e) (X (P e))
      _ ≤ ‖P e‖ * (‖X‖ * ‖P e‖) :=
          mul_le_mul_of_nonneg_left (X.le_opNorm (P e)) (norm_nonneg (P e))
      _ = ‖X‖ * ‖P e‖ ^ 2 := by ring
  have h_abs_le : |hilbertTrace (P * X)| ≤ ‖X‖ * hilbertTrace P := by
    rw [h_cyc]
    unfold hilbertTrace
    calc |∑ ω, RCLike.re (inner ℂ (basisVecGlobal (SiteCSS[L, q_code]) ω)
            ((P * X * P) (basisVecGlobal (SiteCSS[L, q_code]) ω)))|
      _ ≤ ∑ ω, |RCLike.re (inner ℂ (basisVecGlobal (SiteCSS[L, q_code]) ω)
            ((P * X * P) (basisVecGlobal (SiteCSS[L, q_code]) ω)))| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ ω, ‖X‖ * ‖P (basisVecGlobal (SiteCSS[L, q_code]) ω)‖ ^ 2 :=
          Finset.sum_le_sum fun ω _ => h_tr_PX ω
      _ = ‖X‖ * ∑ ω, RCLike.re (inner ℂ (basisVecGlobal (SiteCSS[L, q_code]) ω)
            (P (basisVecGlobal (SiteCSS[L, q_code]) ω))) := by
          rw [← Finset.mul_sum]
          congr 1
          exact Finset.sum_congr rfl fun ω _ => (h_tr_P ω).symm
  have hP_nn : 0 ≤ hilbertTrace P := by
    unfold hilbertTrace
    refine Finset.sum_nonneg fun ω _ => ?_
    rw [h_tr_P ω]
    exact sq_nonneg _
  rcases eq_or_lt_of_le hP_nn with h_zero | h_pos
  · rw [← h_zero, div_zero, abs_zero]
    exact norm_nonneg X
  · rw [abs_div, abs_of_pos h_pos, div_le_iff₀ h_pos]
    exact h_abs_le

lemma opNorm_selfAdjoint_involution_mul_le {L q_code : ℕ}
    (U X : ℬ_CSS[L, q_code]) (hU_sa : IsSelfAdjoint U) (hU_sq : U * U = 1) :
    ‖U * X‖ ≤ ‖X‖ := by
  refine ContinuousLinearMap.opNorm_le_bound (U * X) (norm_nonneg X) fun ψ => ?_
  have hU_adj : U† = U := ContinuousLinearMap.isSelfAdjoint_iff'.mp hU_sa
  have h_norm_sq : ‖U (X ψ)‖ ^ 2 = ‖X ψ‖ ^ 2 := by
    calc ‖U (X ψ)‖ ^ 2
      _ = RCLike.re (inner ℂ (U (X ψ)) (U (X ψ))) := (inner_self_eq_norm_sq (U (X ψ))).symm
      _ = RCLike.re (inner ℂ ((U†) (U (X ψ))) (X ψ)) := by
          rw [ContinuousLinearMap.adjoint_inner_left]
      _ = RCLike.re (inner ℂ ((U * U) (X ψ)) (X ψ)) := by rw [hU_adj]; rfl
      _ = RCLike.re (inner ℂ (X ψ) (X ψ)) := by rw [hU_sq, ContinuousLinearMap.one_apply]
      _ = ‖X ψ‖ ^ 2 := inner_self_eq_norm_sq (X ψ)
  have h_le : ‖(U * X) ψ‖ ≤ ‖X ψ‖ :=
    nonneg_le_nonneg_of_sq_le_sq (norm_nonneg _)
      (by change ‖U (X ψ)‖ * ‖U (X ψ)‖ ≤ ‖X ψ‖ * ‖X ψ‖; linarith [sq ‖U (X ψ)‖, sq ‖X ψ‖])
  exact le_trans h_le (X.le_opNorm ψ)

lemma worldlinePolymerLoopAmplitude_abs_le {L q_code r_0 m_max : ℕ} [NeZero L]
    (D_field : Box3D L → LocalCSSDescriptor q_code r_0 m_max)
    (sys : SysCSS[L, q_code, m_max]) (C_RCA : ℝ)
    (V : QuasiLocalPerturbation 3 L (SiteCSS[L, q_code]))
    (γ : WorldlineDysonPolymer L q_code)
    (σ₀ : IdxCSS[L, q_code, m_max] → Bool) :
    |worldlinePolymerLoopAmplitude D_field sys C_RCA V γ σ₀| ≤
      (γ.1.map (fun ξ => ‖worldlineSyndromeShiftBlockOp D_field sys V ξ‖)).prod := by
  unfold worldlinePolymerLoopAmplitude
  (try dsimp only)
  let σ_rep := canonicalCollarRealizableSyndrome D_field (worldlinePolymerNativeCollar sys C_RCA γ) σ₀
  let μ := worldlinePolymerLogicalCoset D_field sys C_RCA γ
  let W_prod := worldlinePolymerWeightedLoopOp D_field sys V γ
  let B_prod := (hermitianPauliZX μ.1 μ.2)† * W_prod
  rw [mul_div_assoc, abs_mul, spanningSurfaceSign_abs, one_mul]
  have hP : IsStarProjection (sys.syndromeProjector σ_rep) :=
    (PerturbedThermalBarrier.syndrome_resolution_indexed sys).2.1 σ_rep
  have h_tr := abs_hilbertTrace_isStarProjection_mul_div_le (sys.syndromeProjector σ_rep) B_prod hP
  rcases hermitianPauliZX_isSelfAdjoint_and_sq_eq_one μ.1 μ.2 with ⟨hL_sa, hL_sq⟩
  have h_adj : (hermitianPauliZX μ.1 μ.2)† = hermitianPauliZX μ.1 μ.2 :=
    ContinuousLinearMap.isSelfAdjoint_iff'.mp hL_sa
  have h_norm_B : ‖B_prod‖ ≤ ‖W_prod‖ := by
    dsimp [B_prod]
    rw [h_adj]
    exact opNorm_selfAdjoint_involution_mul_le (hermitianPauliZX μ.1 μ.2) W_prod hL_sa hL_sq
  exact le_trans h_tr (le_trans h_norm_B (worldlinePolymerWeightedLoopOp_norm_le D_field sys V γ))

lemma list_prod_le_prod_map {α : Type*} (l : List α) (f g : α → ℝ)
    (hf : ∀ x ∈ l, 0 ≤ f x) (hfg : ∀ x ∈ l, f x ≤ g x) :
    (l.map f).prod ≤ (l.map g).prod := by
  induction l with
  | nil => simp
  | cons hd tl ih =>
    rw [List.map_cons, List.prod_cons, List.map_cons, List.prod_cons]
    have h_hd_nn : 0 ≤ f hd := hf hd List.mem_cons_self
    have h_hd_le : f hd ≤ g hd := hfg hd List.mem_cons_self
    have h_tl_nn : 0 ≤ (tl.map f).prod :=
      List.prod_nonneg (by intro y hy; rcases List.mem_map.mp hy with ⟨x, hx, rfl⟩; exact hf x (List.mem_cons_of_mem hd hx))
    have h_tl_le : (tl.map f).prod ≤ (tl.map g).prod :=
      ih (fun x hx => hf x (List.mem_cons_of_mem hd hx)) (fun x hx => hfg x (List.mem_cons_of_mem hd hx))
    exact mul_le_mul h_hd_le h_tl_le h_tl_nn (le_trans h_hd_nn h_hd_le)

lemma mem_scaleCubeFinset_iff {L R_cut : ℕ} {p : ℕ × Finset (Box3D L)} :
    p ∈ worldlineScaleCubeFinset L R_cut ↔
      p.1 ∈ Finset.Icc 1 (min R_cut L) ∧ p.2 ∈ boxCubes 3 L p.1 := by
  unfold worldlineScaleCubeFinset
  rw [Finset.mem_biUnion]
  constructor
  · rintro ⟨r, hr, hA⟩
    rw [Finset.mem_image] at hA
    rcases hA with ⟨A, hA_mem, h_eq⟩
    have hr_eq : r = p.1 := congrArg Prod.fst h_eq
    have hA_eq : A = p.2 := congrArg Prod.snd h_eq
    subst hr_eq hA_eq
    exact ⟨hr, hA_mem⟩
  · rintro ⟨hr, hA⟩
    exact ⟨p.1, hr, Finset.mem_image.mpr ⟨p.2, hA, Prod.eta p⟩⟩

lemma worldlinePolymerLoopAmplitude_abs_le_prod_two_mul_J_mul_f
    {L q_code r_0 m_max R_cut : ℕ} [NeZero L]
    {C_RCA J : ℝ}
    (D_field : Box3D L → LocalCSSDescriptor q_code r_0 m_max)
    (sys : SysCSS[L, q_code, m_max])
    (V : QuasiLocalPerturbation 3 L (SiteCSS[L, q_code])) (f : ℕ → ℝ)
    (hV_norm : ∀ r ∈ Finset.Icc 1 (min R_cut L), ∀ A ∈ boxCubes 3 L r, ‖V.term r A‖ ≤ J * f r)
    (γ : WorldlineDysonPolymer L q_code)
    (hγ : IsValidWorldlinePolymer D_field sys C_RCA R_cut γ)
    (σ₀ : IdxCSS[L, q_code, m_max] → Bool) :
    |worldlinePolymerLoopAmplitude D_field sys C_RCA V γ σ₀| ≤
      (γ.1.map (fun ξ => 2 * (J * f ξ.1.1))).prod := by
  refine le_trans (worldlinePolymerLoopAmplitude_abs_le D_field sys C_RCA V γ σ₀) ?_
  refine list_prod_le_prod_map γ.1
    (fun ξ => ‖worldlineSyndromeShiftBlockOp D_field sys V ξ‖)
    (fun ξ => 2 * (J * f ξ.1.1))
    (fun ξ _ => norm_nonneg _)
    (fun ξ hξ => ?_)
  have hp_mem : ξ.1 ∈ worldlinePolymerMonomers γ :=
    Finset.mem_union_left _ (List.mem_toFinset.mpr (List.mem_map_of_mem hξ))
  rcases mem_scaleCubeFinset_iff.mp (hγ.1 ξ.1 hp_mem) with ⟨hr, hA⟩
  calc ‖worldlineSyndromeShiftBlockOp D_field sys V ξ‖
    _ ≤ ‖pauliOffDiagonalTerm sys V ξ.1.1 ξ.1.2‖ :=
        worldlineSyndromeShiftBlockOp_norm_le D_field sys V ξ
    _ ≤ 2 * ‖V.term ξ.1.1 ξ.1.2‖ :=
        pauliOffDiagonalTerm_norm_le_two_mul_norm sys V ξ.1.1 ξ.1.2
    _ ≤ 2 * (J * f ξ.1.1) :=
        mul_le_mul_of_nonneg_left (hV_norm ξ.1.1 hr ξ.1.2 hA) (by norm_num)

lemma abs_exp_sub_one_le_abs_mul_exp_abs (x : ℝ) :
    |Real.exp x - 1| ≤ |x| * Real.exp |x| := by
  rcases le_total 0 x with hx | hx
  · have h_abs : |x| = x := abs_of_nonneg hx
    have h_exp_ge : 1 ≤ Real.exp x := Real.one_le_exp hx
    rw [abs_of_nonneg (sub_nonneg.mpr h_exp_ge), h_abs]
    have h_le : 1 - x ≤ Real.exp (-x) := by
      have := Real.add_one_le_exp (-x)
      linarith
    have h_mul := mul_le_mul_of_nonneg_right h_le (le_of_lt (Real.exp_pos x))
    rw [sub_mul, one_mul, ← Real.exp_add, neg_add_cancel, Real.exp_zero] at h_mul
    linarith
  · have h_abs : |x| = -x := abs_of_nonpos hx
    have h_exp_le : Real.exp x ≤ 1 := Real.exp_le_one_iff.mpr hx
    rw [abs_of_nonpos (sub_nonpos.mpr h_exp_le), h_abs]
    have h_le : 1 + x ≤ Real.exp x := by
      have := Real.add_one_le_exp x
      linarith
    have h_exp_ge_one : 1 ≤ Real.exp (-x) := Real.one_le_exp (neg_nonneg.mpr hx)
    have h_neg_nn : 0 ≤ -x := neg_nonneg.mpr hx
    nlinarith

lemma abs_setIntegral_Icc_le_of_abs_le {β C : ℝ} (hβ : 0 ≤ β) (hC : 0 ≤ C)
    (g : ℝ → ℝ) (hg : ∀ t ∈ Set.Icc 0 β, |g t| ≤ C) :
    |∫ t in Set.Icc 0 β, g t| ≤ β * C := by
  have h_vol : (MeasureTheory.volume (Set.Icc 0 β)).toReal = β := by
    rw [Real.volume_Icc, sub_zero, ENNReal.toReal_ofReal hβ]
  have h_lt : MeasureTheory.volume (Set.Icc 0 β) < ⊤ := by
    rw [Real.volume_Icc]
    exact ENNReal.ofReal_lt_top
  have h_bound := MeasureTheory.norm_setIntegral_le_of_norm_le_const
    (s := Set.Icc 0 β) (C := C) h_lt (fun t ht => by rw [Real.norm_eq_abs]; exact hg t ht)
  rw [Real.norm_eq_abs, MeasureTheory.measureReal_def, h_vol, mul_comm C β] at h_bound
  exact h_bound

lemma abs_worldlineMayerBondFactor_le
    {L q_code r_0 m_max R_cut : ℕ} [NeZero L]
    {C_RCA β J : ℝ} (hβ : 0 ≤ β) (hJ : 0 ≤ J)
    (D_field : Box3D L → LocalCSSDescriptor q_code r_0 m_max)
    (sys : SysCSS[L, q_code, m_max])
    (f : ℕ → ℝ) (hf_nn : ∀ r, 0 ≤ f r)
    (d_loc : ℕ → Finset (Box3D L) → (IdxCSS[L, q_code, m_max] → Bool) → ℝ)
    (hd_scale : ∀ r ∈ Finset.Icc 1 (min R_cut L), ∀ A ∈ boxCubes 3 L r,
      ∀ σ : IdxCSS[L, q_code, m_max] → Bool, |d_loc r A σ| ≤ 2 * (J * f r))
    (γ : WorldlineDysonPolymer L q_code)
    (hγ : IsValidWorldlinePolymer D_field sys C_RCA R_cut γ)
    (σ₀ : IdxCSS[L, q_code, m_max] → Bool)
    (τ : Fin γ.1.length → ℝ)
    {ϑ : ℕ × Finset (Box3D L)} (hϑ : ϑ ∈ γ.2) :
    |worldlineMayerBondFactor D_field γ.1 d_loc σ₀ β ϑ τ| ≤
      4 * β * J * f ϑ.1 * Real.exp (4 * β * J * f ϑ.1) := by
  unfold worldlineMayerBondFactor
  have hϑ_mon : ϑ ∈ worldlinePolymerMonomers γ := Finset.mem_union_right _ hϑ
  rcases mem_scaleCubeFinset_iff.mp (hγ.1 ϑ hϑ_mon) with ⟨hr, hB⟩
  have h_diff_le : ∀ t ∈ Set.Icc 0 β,
      |d_loc ϑ.1 ϑ.2 (worldlineTrajectorySyndrome D_field γ.1 σ₀ τ t) - d_loc ϑ.1 ϑ.2 σ₀| ≤
        4 * (J * f ϑ.1) := by
    intro t _
    have h1 := hd_scale ϑ.1 hr ϑ.2 hB (worldlineTrajectorySyndrome D_field γ.1 σ₀ τ t)
    have h2 := hd_scale ϑ.1 hr ϑ.2 hB σ₀
    have h_tri := abs_sub (d_loc ϑ.1 ϑ.2 (worldlineTrajectorySyndrome D_field γ.1 σ₀ τ t)) (d_loc ϑ.1 ϑ.2 σ₀)
    linarith
  have hC_nn : 0 ≤ 4 * (J * f ϑ.1) := by have := hf_nn ϑ.1; positivity
  have h_int_le : |-(∫ t in Set.Icc 0 β,
      (d_loc ϑ.1 ϑ.2 (worldlineTrajectorySyndrome D_field γ.1 σ₀ τ t) - d_loc ϑ.1 ϑ.2 σ₀))| ≤
      4 * β * J * f ϑ.1 := by
    rw [abs_neg]
    calc |∫ t in Set.Icc 0 β,
          (d_loc ϑ.1 ϑ.2 (worldlineTrajectorySyndrome D_field γ.1 σ₀ τ t) - d_loc ϑ.1 ϑ.2 σ₀)|
      _ ≤ β * (4 * (J * f ϑ.1)) := abs_setIntegral_Icc_le_of_abs_le hβ hC_nn _ h_diff_le
      _ = 4 * β * J * f ϑ.1 := by ring
  refine le_trans (abs_exp_sub_one_le_abs_mul_exp_abs _) ?_
  exact mul_le_mul h_int_le (Real.exp_le_exp.mpr h_int_le) (le_of_lt (Real.exp_pos _)) (by have := hf_nn ϑ.1; positivity)

private lemma fixed_of_half_one_sub_mul_eq_zero {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] {U P : E →L[ℂ] E}
    (h : ((2 : ℂ)⁻¹ • (1 - U)) * P = 0) : U * P = P := by
  have h2 : (2 : ℂ) • (((2 : ℂ)⁻¹ • (1 - U)) * P) = 0 := by rw [h, smul_zero]
  rw [← clm_smul_mul, smul_smul] at h2
  have h_two_inv : (2 : ℂ) * (2 : ℂ)⁻¹ = 1 := by norm_num
  rw [h_two_inv, one_smul, sub_mul, one_mul, sub_eq_zero] at h2
  exact h2.symm

/-- Every check bitstring generator `staticCSSCheckPauliZ D_field c` and `staticCSSCheckPauliX D_field c`
acts as $+1$ on the vacuum projector `sys.P0`. -/
lemma weylPauli_staticCSSCheckPauli_mul_P0
    {L q_code r_0 m_max : ℕ}
    (D_field : Box3D L → LocalCSSDescriptor q_code r_0 m_max)
    (sys : SysCSS[L, q_code, m_max])
    (h_sys_checks : ∀ idx, sys.checkProj idx = staticCSSCheckProj D_field idx ∧
      sys.support idx = staticCSSCheckSupport D_field idx ∧ sys.weight idx = 1)
    (c : IdxCSS[L, q_code, m_max]) :
    weylPauliZ (staticCSSCheckPauliZ D_field c) * sys.P0 = sys.P0 ∧
    weylPauliX (staticCSSCheckPauliX D_field c) * sys.P0 = sys.P0 := by
  have h_res := PerturbedThermalBarrier.syndrome_resolution_indexed sys
  have h_chk_zero : staticCSSCheckProj D_field c * sys.P0 = 0 := by
    rw [← (h_sys_checks c).1, ← h_res.1]
    simpa using h_res.2.2.2.2.2.1 (fun _ => false) c
  rcases c with ⟨v, s⟩ | ⟨v, idx⟩ | ⟨v, idx⟩
  · dsimp [staticCSSCheckPauliZ, staticCSSCheckPauliX]
    refine ⟨?_, by rw [weylPauliX_zero, one_mul]⟩
    dsimp [staticCSSCheckProj] at h_chk_zero
    split_ifs with h_inact
    · rw [if_pos h_inact] at h_chk_zero; exact fixed_of_half_one_sub_mul_eq_zero h_chk_zero
    · rw [weylPauliZ_zero, one_mul]
  · dsimp [staticCSSCheckPauliZ, staticCSSCheckPauliX]
    refine ⟨by rw [weylPauliZ_zero, one_mul], ?_⟩
    dsimp [staticCSSCheckProj] at h_chk_zero
    split_ifs with h_lt
    · rw [if_pos h_lt] at h_chk_zero; exact fixed_of_half_one_sub_mul_eq_zero h_chk_zero
    · rw [weylPauliX_zero, one_mul]
  · dsimp [staticCSSCheckPauliZ, staticCSSCheckPauliX]
    refine ⟨?_, by rw [weylPauliX_zero, one_mul]⟩
    dsimp [staticCSSCheckProj] at h_chk_zero
    split_ifs with h_lt
    · rw [if_pos h_lt] at h_chk_zero; exact fixed_of_half_one_sub_mul_eq_zero h_chk_zero
    · rw [weylPauliZ_zero, one_mul]

end DirectWorldlineCluster
end
