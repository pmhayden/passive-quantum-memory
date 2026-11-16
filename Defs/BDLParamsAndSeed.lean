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

import Defs.F2ChainAndCSS
import Mathlib.Order.Prod.Lex.Basic

/-!
# Explicit Three-Layer Welded Hierarchy Parameters and `[[5, 1, 2]]` Planar Seed Code

Defines the bundled 3D CSS code carrier `BundledCSSCode3D`, its X/Z-check duality involution `dualBundled`, and the explicit geometric, spherical-cap LLL, and b-adic open-box dilation constants (`wBDL`, `bBDL`, `r0BDL`, `bdlPeriodL`, `qCodeBDL`, `mMaxBDL`, and `bdlBoxSide`). Constructs the base `[[5, 1, 2]]` planar surface seed code `bdlSurfaceSeedCode` (`bdlSurfaceSeedBundled`) and proves exact CSS check commutativity (`surfaceCheck_comm`).

## References

* Part I, Section 2.1 (`subsec:css-complexes`), Definition 2.1 (`def:3d-css-complex`), Lemma 2.3 (`lem:seed-code`)
* Part I, Section 2.2 (`subsec:step1-lll`), Proposition 2.4 (`prop:step1-lll`)
* Part II, Section 4 (`subsec:welded-hierarchy-cleaner`), Lemma 4.1 (`lem:seed-code`)
* Balasubramanian, Davydova, and Lin (2026)
-/

noncomputable section

open scoped Classical BigOperators

/-! ## 1. Bundled 3D CSS Code Carrier and Dual Functor -/

/-- Bundled 3D CSS code carrier type enabling uniform iteration $(R_Z \circ R_X)^{k+1}(\mathcal{C}_0)$
    together with a local combinatorial slot index `slotQ : Q → ℕ` for tie-breaking. -/
structure BundledCSSCode3D where
  Q : Type
  M_Z : Type
  M_X : Type
  [fintypeQ : Fintype Q]
  [decEqQ : DecidableEq Q]
  [fintypeMZ : Fintype M_Z]
  [decEqMZ : DecidableEq M_Z]
  [fintypeMX : Fintype M_X]
  [decEqMX : DecidableEq M_X]
  code : CSSCode3D Q M_Z M_X
  slotQ : Q → ℕ := fun _ => 0

attribute [instance] BundledCSSCode3D.fintypeQ BundledCSSCode3D.decEqQ
attribute [instance] BundledCSSCode3D.fintypeMZ BundledCSSCode3D.decEqMZ
attribute [instance] BundledCSSCode3D.fintypeMX BundledCSSCode3D.decEqMX

/-- Dual bundled 3D CSS code `dualBundled B` swapping $X$-checks and $Z$-checks ($H_X \leftrightarrow H_Z$). -/
def dualBundled (B : BundledCSSCode3D) : BundledCSSCode3D where
  Q := B.Q
  M_Z := B.M_X
  M_X := B.M_Z
  code := dualCode B.code
  slotQ := B.slotQ

/-! ## 2. Explicit Geometric, LLL, and $b$-Adic Dilation Constants -/

/-- Maximum vertex degree $z_v = 7$ in the coarse Tanner complex. -/
def bdlMaxVertexDegree : ℕ := 7

/-- Uniform LDPC check/qubit degree bound $w_{\mathrm{BDL}} = 3 z_v + 1 = 22$. -/
def wBDL : ℕ := 3 * bdlMaxVertexDegree + 1

/-- Spherical cap radius integer parameter $\alpha_{\mathbb{N}} = 1000$. -/
def bdlAlphaNat : ℕ := 1000

/-- Spherical cap radius parameter $\alpha = (\alpha_{\mathbb{N}} : \mathbb{R})$. -/
def bdlAlpha : ℝ := (bdlAlphaNat : ℝ)

/-- Cap arc-size parameter $\alpha_1 = 139$. -/
def bdlAlpha1 : ℝ := 139

/-- Cap half-separation parameter $\alpha_2 = \alpha_1 / 2$. -/
def bdlAlpha2 : ℝ := bdlAlpha1 / 2

/-- Simplex width lower-bound constant $\gamma = \alpha(1 - \cos(\alpha_2 / \alpha)) - 1$. -/
def bdlGamma : ℝ := bdlAlpha * (1 - Real.cos (bdlAlpha2 / bdlAlpha)) - 1

/-- Perturbed 2-simplex unit-ball density threshold $t' = 5595$. -/
def bdlDensityTPrime : ℝ := 5595

/-- Restored $(t, 1)$-embedding 2-cell density bound $t = 6.6 \times 10^{10}$. -/
def bdlDensityT : ℝ := 66000000000

/-- Spatial scale factor $\lambda_{\mathrm{BDL}} = 5.4 \times 10^{24}$. -/
def bdlLambda : ℕ := 5400000000000000000000000

/-- Symbolic subdivision multiplier $2(2\alpha_{\mathbb{N}} + 1)$. -/
def bdlSubdivFactor : ℕ := 2 * (2 * bdlAlphaNat + 1)

/-- Subdivision factor $m = 2(2\alpha_{\mathbb{N}} + 1)\lambda_{\mathrm{BDL}}$. -/
def bdlSubdivM : ℕ := bdlSubdivFactor * bdlLambda

/-- Predecessor $M = m - 1$ so $m = \mathrm{bdlSubdivPred} + 1$. -/
def bdlSubdivPred : ℕ := bdlSubdivM - 1

/-- Uniform integer $b$-adic open-box dilation factor $b_{\mathrm{BDL}} = \lambda_{\mathrm{BDL}}$. -/
def bBDL : ℕ := bdlLambda

/-- Local LLL dependency neighborhood radius $R_{\mathrm{reach}} = 2 r_0 + 1 = 19$. -/
def r0BDL : ℕ := 9
def bdlLLLReach : ℕ := 2 * r0BDL + 1

/-- Periodic LLL coloring period $P_{\mathrm{LLL}} = 2 R_{\mathrm{reach}} + 1$. -/
def bdlPeriodL : ℕ := 2 * bdlLLLReach + 1

/-- Number of cellular layers ($C_X, C_Q, C_Z$) in the welded cylinder complex. -/
def numWeldedLayers : ℕ := 3

/-- Number of concentric radial checkpoint shells in each cylinder. -/
def numCheckpointsBDL : ℕ := 2 * numWeldedLayers

/-- Scale-independent per-site physical qubit slot capacity $q_{\mathrm{code}} = 6.6 \times 10^{10}$. -/
def qCodeBDL : ℕ := 66000000000

/-- Scale-independent per-site check slot capacity $m_{\max} = 6.6 \times 10^{10}$. -/
def mMaxBDL : ℕ := 66000000000

/-- Hierarchy step count $2k + 4$ at macroscopic level $k \in \mathbb{N}$. -/
def bdlHierarchySteps (k : ℕ) : ℕ := 2 * k + 4

/-- Open-box system side length $L_k = b_{\mathrm{BDL}}^{2k+4}$ at level $k \in \mathbb{N}$. -/
def bdlBoxSide (k : ℕ) : ℕ := bBDL ^ bdlHierarchySteps k

lemma bdlLambda_pos : 0 < bdlLambda := by
  dsimp [bdlLambda]; positivity

lemma bdlSubdivM_eq_succ : bdlSubdivPred + 1 = bdlSubdivM := by
  dsimp [bdlSubdivPred, bdlSubdivM, bdlSubdivFactor, bdlAlphaNat, bdlLambda]

lemma b_bdl_pos : 0 < bBDL := by
  dsimp [bBDL, bdlLambda]; positivity

lemma two_le_b_bdl : 2 ≤ bBDL := by
  dsimp [bBDL, bdlLambda]; omega

lemma bdlBoxSide_pos (k : ℕ) : 0 < bdlBoxSide k :=
  Nat.pow_pos b_bdl_pos

instance instNeZeroBDLBoxSide (k : ℕ) : NeZero (bdlBoxSide k) :=
  ⟨Nat.pos_iff_ne_zero.mp (bdlBoxSide_pos k)⟩

lemma q_code_bdl_pos : 0 < qCodeBDL := by
  dsimp [qCodeBDL]; omega

instance instNeZeroQCodeBDL : NeZero qCodeBDL := ⟨Nat.pos_iff_ne_zero.mp q_code_bdl_pos⟩

/-! ## 3. Base Case Seed Code $\mathcal{C}_{(0)}$: The `[[5, 1, 2]]` Planar Surface Code -/

/-- $X$-check matrix of the `[[5, 1, 2]]` surface code seed $\mathcal{C}_{(0)}$:
    $x = 0$ checks $\{0, 1, 2\}$; $x = 1$ checks $\{2, 3, 4\}$. -/
def surfaceCheckX (mX : Fin 2) (q : Fin 5) : ZMod 2 :=
  if mX = 0 then (if q.val ≤ 2 then 1 else 0) else (if 2 ≤ q.val then 1 else 0)

/-- $Z$-check matrix of the `[[5, 1, 2]]` surface code seed $\mathcal{C}_{(0)}$:
    $z = 0$ checks $\{0, 2, 3\}$; $z = 1$ checks $\{1, 2, 4\}$. -/
def surfaceCheckZ (mZ : Fin 2) (q : Fin 5) : ZMod 2 :=
  if mZ = 0 then (if q.val = 0 ∨ q.val = 2 ∨ q.val = 3 then 1 else 0)
  else (if q.val = 1 ∨ q.val = 2 ∨ q.val = 4 then 1 else 0)

/-- Exact CSS commutativity $H_X H_Z^T = 0$ for the `[[5, 1, 2]]` planar surface seed. -/
lemma surfaceCheck_comm (mX mZ : Fin 2) :
    (∑ q : Fin 5, surfaceCheckX mX q * surfaceCheckZ mZ q) = 0 := by
  revert mX mZ; decide

/-- Planar $3 \times 3$ grid embedding `surfacePosQ` of the 5 physical qubits of $T_{(0)}$. -/
def surfacePosQ (q : Fin 5) : Point3D
  | 0 => if q.val = 0 ∨ q.val = 3 then 0 else if q.val = 2 then 1 else 2
  | 1 => if q.val ≤ 1 then 2 else if q.val = 2 then 1 else 0
  | 2 => 0

/-- Planar $3 \times 3$ grid embedding `surfacePosX` of the 2 $X$-checks of $T_{(0)}$. -/
def surfacePosX (mX : Fin 2) : Point3D
  | 0 => 1
  | 1 => if mX = 0 then 2 else 0
  | 2 => 0

/-- Planar $3 \times 3$ grid embedding `surfacePosZ` of the 2 $Z$-checks of $T_{(0)}$. -/
def surfacePosZ (mZ : Fin 2) : Point3D
  | 0 => if mZ = 0 then 0 else 2
  | 1 => 1
  | 2 => 0

/-- The `[[5, 1, 2]]` planar surface code seed $\mathcal{C}_{(0)}$. -/
def bdlSurfaceSeedCode : CSSCode3D (Fin 5) (Fin 2) (Fin 2) where
  posQ := surfacePosQ
  posZ := surfacePosZ
  posX := surfacePosX
  checkX := surfaceCheckX
  checkZ := surfaceCheckZ
  commutativity := surfaceCheck_comm

/-- Bundled `[[5, 1, 2]]` planar surface seed code with local slot index `q.val`. -/
def bdlSurfaceSeedBundled : BundledCSSCode3D where
  Q := Fin 5
  M_Z := Fin 2
  M_X := Fin 2
  code := bdlSurfaceSeedCode
  slotQ := fun q => q.val

end
