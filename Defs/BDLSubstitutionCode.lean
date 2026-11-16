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

import Defs.Step2CheckMatrices
import Defs.LocalCSSDescriptor

/-!
# Grid-Snapped Local CSS Descriptors and Scaling Constants for the Welded Code Hierarchy

Snaps the Euclidean cell coordinates of the three-layer welded CSS hierarchy `bdlWeldedCode k` onto the open 3D cubic lattice `Box3D (bdlBoxSide k)` via `snapPointToOpenBox` and constructs the multi-site local check-incidence descriptor field `bdlLocalDescriptor`. Defines the explicit critical inverse temperature `betaCritBDL`, free-energy barrier prefactor `cFBDL`, confinement exponent `etaBDL`, RCA collar constants `collarConstRCABDL` and `cAddBDL`, linear TQO fraction `cStarBDL`, and macroscopic free-energy barrier `bdlFreeEnergyBarrier`.

## References

* Part I, Section 5.3 (`subsec:walsh-fourier-peierls`), Theorem 5.5 (`thm:walsh-fourier-peierls`)
* Part I, Section 5.4 (`subsec:safe-decoded-observables`), Definition 5.6 (`def:safe-decoded-observables`)
* Part II, Section 2 (`subsec:setup`), Definition 2.1 (`def:bdl-lattice`), Section 4 (`subsec:welded-hierarchy-cleaner`), Definition 4.2 (`def:multiscale-cluster-decoder`)
-/

noncomputable section

open scoped Classical BigOperators

set_option linter.constructorNameAsVariable false
set_option maxRecDepth 200000

/-! ## 1. Open-Box Grid-Snapping of the 3-Layer Welded BDL Code `bdlWeldedCode k` -/

/-- Snaps a 3D Euclidean point `p : Point3D` to the open box `Box3D L` (`Fin 3 → Fin L`)
    by shifting by `(L : ℝ) / 2` and taking the integer floor along each axis. -/
def snapPointToOpenBox (L : ℕ) [NeZero L] (p : Point3D) : Box3D L :=
  fun μ =>
    let n := Int.toNat ⌊p μ + (L : ℝ) / 2⌋
    if h : n < L then ⟨n, h⟩ else ⟨0, NeZero.pos L⟩

/-- Snapped open-box lattice sites in `Box3D (bdlBoxSide k)` of physical qubits and checks. -/
def bdlGridVertexQ (k : ℕ) (q : BDLWeldedQubit k) : Box3D (bdlBoxSide k) :=
  snapPointToOpenBox (bdlBoxSide k) ((bdlWeldedCode k).posQ q)

def bdlGridVertexZ (k : ℕ) (mZ : BDLWeldedCheckZ k) : Box3D (bdlBoxSide k) :=
  snapPointToOpenBox (bdlBoxSide k) ((bdlWeldedCode k).posZ mZ)

def bdlGridVertexX (k : ℕ) (mX : BDLWeldedCheckX k) : Box3D (bdlBoxSide k) :=
  snapPointToOpenBox (bdlBoxSide k) ((bdlWeldedCode k).posX mX)

/-- Injective indices on `BDLWeldedQubit k`, `BDLWeldedCheckZ k`, and `BDLWeldedCheckX k`. -/
def bdlCellIndexQ (k : ℕ) (q : BDLWeldedQubit k) : ℕ := (Fintype.equivFin (BDLWeldedQubit k) q).val
def bdlCellIndexZ (k : ℕ) (mZ : BDLWeldedCheckZ k) : ℕ := (Fintype.equivFin (BDLWeldedCheckZ k) mZ).val
def bdlCellIndexX (k : ℕ) (mX : BDLWeldedCheckX k) : ℕ := (Fintype.equivFin (BDLWeldedCheckX k) mX).val

/-- Fibers of welded qubits and checks mapped to open-box site `v` under placements `vQ, vX, vZ`. -/
def bdlQubitFiberOf {k : ℕ} (vQ : BDLWeldedQubit k → Box3D (bdlBoxSide k))
    (v : Box3D (bdlBoxSide k)) : Finset (BDLWeldedQubit k) :=
  Finset.univ.filter (fun q => vQ q = v)

def bdlCheckXFiberOf {k : ℕ} (vX : BDLWeldedCheckX k → Box3D (bdlBoxSide k))
    (v : Box3D (bdlBoxSide k)) : Finset (BDLWeldedCheckX k) :=
  Finset.univ.filter (fun mX => vX mX = v)

def bdlCheckZFiberOf {k : ℕ} (vZ : BDLWeldedCheckZ k → Box3D (bdlBoxSide k))
    (v : Box3D (bdlBoxSide k)) : Finset (BDLWeldedCheckZ k) :=
  Finset.univ.filter (fun mZ => vZ mZ = v)

/-- Local intra-site rank of qubit `q` within its fiber `bdlQubitFiberOf vQ (vQ q)`. -/
def bdlQubitLocalRankOf {k : ℕ} (vQ : BDLWeldedQubit k → Box3D (bdlBoxSide k))
    (iQ : BDLWeldedQubit k → ℕ) (q : BDLWeldedQubit k) : ℕ :=
  ((bdlQubitFiberOf vQ (vQ q)).filter (fun q' => iQ q' < iQ q)).card

/-- Open-box `(site, slot)` pair in `BoxSlot3D (bdlBoxSide k) qCodeBDL` assigned to qubit `q`. -/
def bdlQubitSiteSlotOf {k : ℕ} (vQ : BDLWeldedQubit k → Box3D (bdlBoxSide k))
    (iQ : BDLWeldedQubit k → ℕ) (q : BDLWeldedQubit k) :
    BoxSlot3D (bdlBoxSide k) qCodeBDL :=
  let r := bdlQubitLocalRankOf vQ iQ q
  (vQ q, if h : r < qCodeBDL then ⟨r, h⟩ else ⟨0, q_code_bdl_pos⟩)

/-- Local intra-site ranks of $X$-check `mX` and $Z$-check `mZ` within their fibers. -/
def bdlCheckXLocalRankOf {k : ℕ} (vX : BDLWeldedCheckX k → Box3D (bdlBoxSide k))
    (iX : BDLWeldedCheckX k → ℕ) (mX : BDLWeldedCheckX k) : ℕ :=
  ((bdlCheckXFiberOf vX (vX mX)).filter (fun mX' => iX mX' < iX mX)).card

def bdlCheckZLocalRankOf {k : ℕ} (vZ : BDLWeldedCheckZ k → Box3D (bdlBoxSide k))
    (iZ : BDLWeldedCheckZ k → ℕ) (mZ : BDLWeldedCheckZ k) : ℕ :=
  ((bdlCheckZFiberOf vZ (vZ mZ)).filter (fun mZ' => iZ mZ' < iZ mZ)).card

/-- Canonical qubit and check fibers and local intra-site ranks on `Box3D (bdlBoxSide k)`. -/
def bdlQubitFiber (k : ℕ) (v : Box3D (bdlBoxSide k)) : Finset (BDLWeldedQubit k) :=
  bdlQubitFiberOf (bdlGridVertexQ k) v
def bdlCheckXFiber (k : ℕ) (v : Box3D (bdlBoxSide k)) : Finset (BDLWeldedCheckX k) :=
  bdlCheckXFiberOf (bdlGridVertexX k) v
def bdlCheckZFiber (k : ℕ) (v : Box3D (bdlBoxSide k)) : Finset (BDLWeldedCheckZ k) :=
  bdlCheckZFiberOf (bdlGridVertexZ k) v
def bdlQubitLocalRank (k : ℕ) (q : BDLWeldedQubit k) : ℕ :=
  bdlQubitLocalRankOf (bdlGridVertexQ k) (bdlCellIndexQ k) q
def bdlQubitSiteSlot (k : ℕ) (q : BDLWeldedQubit k) : BoxSlot3D (bdlBoxSide k) qCodeBDL :=
  bdlQubitSiteSlotOf (bdlGridVertexQ k) (bdlCellIndexQ k) q
def bdlCheckXLocalRank (k : ℕ) (mX : BDLWeldedCheckX k) : ℕ :=
  bdlCheckXLocalRankOf (bdlGridVertexX k) (bdlCellIndexX k) mX
def bdlCheckZLocalRank (k : ℕ) (mZ : BDLWeldedCheckZ k) : ℕ :=
  bdlCheckZLocalRankOf (bdlGridVertexZ k) (bdlCellIndexZ k) mZ

/-- Multi-site local CSS check-incidence descriptor at open-box site `v : Box3D (bdlBoxSide k)`
    induced by a grid placement `(vQ, iQ, vX, iX, vZ, iZ)` of the 3-layer welded BDL code `bdlWeldedCode k`. -/
def bdlLocalDescriptorOfPlacement (k : ℕ)
    (vQ : BDLWeldedQubit k → Box3D (bdlBoxSide k)) (iQ : BDLWeldedQubit k → ℕ)
    (vX : BDLWeldedCheckX k → Box3D (bdlBoxSide k)) (iX : BDLWeldedCheckX k → ℕ)
    (vZ : BDLWeldedCheckZ k → Box3D (bdlBoxSide k)) (iZ : BDLWeldedCheckZ k → ℕ)
    (v : Box3D (bdlBoxSide k)) : LocalCSSDescriptor qCodeBDL r0BDL mMaxBDL where
  activeSlot := fun s =>
    decide (s.val < (bdlQubitFiberOf vQ v).card)
  numXChecks :=
    let n := (bdlCheckXFiberOf vX v).card
    if h : n ≤ mMaxBDL then ⟨n, Nat.lt_succ_of_le h⟩ else ⟨0, Nat.succ_pos _⟩
  numZChecks :=
    let n := (bdlCheckZFiberOf vZ v).card
    if h : n ≤ mMaxBDL then ⟨n, Nat.lt_succ_of_le h⟩ else ⟨0, Nat.succ_pos _⟩
  xCheckMask := fun c nb s =>
    InOpenBox v (neighborhoodOffset r0BDL nb) &&
    let u := shiftOpenBox v (neighborhoodOffset r0BDL nb)
    decide (∃ (mX : BDLWeldedCheckX k) (q : BDLWeldedQubit k),
      vX mX = v ∧ bdlCheckXLocalRankOf vX iX mX = c.val ∧
      bdlQubitSiteSlotOf vQ iQ q = (u, s) ∧ (bdlWeldedCode k).checkX mX q ≠ 0)
  zCheckMask := fun c nb s =>
    InOpenBox v (neighborhoodOffset r0BDL nb) &&
    let u := shiftOpenBox v (neighborhoodOffset r0BDL nb)
    decide (∃ (mZ : BDLWeldedCheckZ k) (q : BDLWeldedQubit k),
      vZ mZ = v ∧ bdlCheckZLocalRankOf vZ iZ mZ = c.val ∧
      bdlQubitSiteSlotOf vQ iQ q = (u, s) ∧ (bdlWeldedCode k).checkZ mZ q ≠ 0)

/-- **Genuine Grid-Snapped Level-$k$ Local CSS Descriptor Field `bdlLocalDescriptor k`**:
    At hierarchy level $k \in \mathbb{N}$ and open-box site $v \in \mathrm{Box3D}(\mathrm{bdlBoxSide}\ k)$,
    encodes the exact multi-site 3-layer welded check incidence of `bdlWeldedCode k` across
    neighboring open-box sites `nb : LocalNeighborhoodIdx r0BDL`. -/
def bdlLocalDescriptor (k : ℕ) (v : Box3D (bdlBoxSide k)) :
    LocalCSSDescriptor qCodeBDL r0BDL mMaxBDL :=
  bdlLocalDescriptorOfPlacement k
    (bdlGridVertexQ k) (bdlCellIndexQ k)
    (bdlGridVertexX k) (bdlCellIndexX k)
    (bdlGridVertexZ k) (bdlCellIndexZ k) v

/-! ## 2. Concrete BDL Scaling Constants -/

/-- Single-step cell-count growth factor $F_{\mathrm{BDL}} = 600 m^2$ for the multiscale cluster decoder. -/
def bdlSingleStepFactor : ℕ := 600 * bdlSubdivM ^ 2

/-- Critical inverse temperature $\beta_{c,\mathrm{BDL}} > 0$ calibrated above the multiscale
    cluster parity-witness animal and check-overlap growth constants. -/
def betaCritBDL : ℝ :=
  1200 * (bdlSingleStepFactor : ℝ) +
  2 * ((mMaxBDL + qCodeBDL : ℕ) : ℝ) * ((4 * r0BDL + 1 : ℕ) ^ 3 : ℝ) + 100

/-- Free-energy barrier prefactor $c_{F,\mathrm{BDL}} = 1 / (6 b_{\mathrm{BDL}}^{12}) > 0$. -/
def cFBDL : ℝ := (1 : ℝ) / (6 * ((bBDL ^ 12 : ℕ) : ℝ))

/-- Polynomial confinement exponent $\eta_{\mathrm{BDL}} = \log(3/2) / (6 \log b_{\mathrm{BDL}} + 1) > 0$. -/
def etaBDL : ℝ := Real.log (3 / 2) / (6 * Real.log (bBDL : ℝ) + 1)

/-- Relative cone acyclicity collar constant
    $C_{\mathrm{rca},\mathrm{BDL}} = 2 \lambda_{\mathrm{BDL}} (\lambda_{\mathrm{BDL}} (10005 \lambda_{\mathrm{BDL}} + 13006) + 13008) + 20$. -/
def collarConstRCABDL : ℕ :=
  2 * bdlLambda * (bdlLambda * (10005 * bdlLambda + 13006) + 13008) + 20

/-- Euclidean additive collar constant $c_{\mathrm{add},\mathrm{BDL}} = (C_{\mathrm{rca},\mathrm{BDL}} : \mathbb{R})$. -/
def cAddBDL : ℝ := (collarConstRCABDL : ℝ)

/-- Linear TQO radius fraction $c_{*,\mathrm{BDL}} = 1 / b_{\mathrm{BDL}}^4 > 0$. -/
def cStarBDL : ℝ := (1 : ℝ) / ((bBDL ^ 4 : ℝ))

/-- KMS passive memory lifetime prefactor $c_{\mathrm{mem},\mathrm{BDL}} = 1 / 32 > 0$. -/
def cMemBDL : ℝ := (1 : ℝ) / 32

lemma beta_crit_bdl_pos : 0 < betaCritBDL := by
  dsimp [betaCritBDL, bdlSingleStepFactor, bdlSubdivM, bdlSubdivFactor,
    bdlAlphaNat, bdlLambda, mMaxBDL, qCodeBDL, r0BDL]; norm_num

lemma c_f_bdl_pos : 0 < cFBDL := by
  dsimp [cFBDL]
  have hb : (0 : ℝ) < ((bBDL ^ 12 : ℕ) : ℝ) := Nat.cast_pos.mpr (Nat.pow_pos b_bdl_pos)
  positivity

lemma eta_bdl_pos : 0 < etaBDL := by
  dsimp [etaBDL]
  have h_num : 0 < Real.log (3 / 2 : ℝ) := Real.log_pos (by norm_num)
  have h_log_b : 0 ≤ Real.log (bBDL : ℝ) :=
    Real.log_nonneg (by exact_mod_cast Nat.succ_le_of_lt b_bdl_pos)
  positivity

lemma c_mem_bdl_pos : 0 < cMemBDL := by dsimp [cMemBDL]; norm_num

lemma c_star_bdl_pos : 0 < cStarBDL := by
  dsimp [cStarBDL]; have hb : (0 : ℝ) < (bBDL : ℝ) := Nat.cast_pos.mpr b_bdl_pos; positivity

/-- Linear macroscopic TQO radius $R_{\mathrm{tqo}}(k) = \lfloor c_{*,\mathrm{BDL}} L_k \rfloor$. -/
def bdlLinearTQORadius (k : ℕ) : ℕ := Nat.floor (cStarBDL * (bdlBoxSide k : ℝ))

/-- Macroscopic polynomial free-energy barrier $\Delta F_{\mathrm{BDL}}(k, \beta)$. -/
def bdlFreeEnergyBarrier (k : ℕ) (β : ℝ) : ℝ :=
  cFBDL * (β - betaCritBDL) * (((bdlBoxSide k ^ 3 : ℕ) : ℝ) ^ etaBDL)

end
