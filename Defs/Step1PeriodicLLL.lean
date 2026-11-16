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

import Defs.BDLParamsAndSeed

/-!
# Step 1 Spherical-Cap Geometry, Periodic LLL De-Crowding, and Canonical Perturbations

Defines closed 2-simplices in R^3 (`simplex2D3D`), Step 1 vertex scaling and shifts (`bdlPerturbStep`), Archimedes spherical-cap surface-area measures (`archimedesCapMeasure`, `sphericalCapAreaFraction`), and the asymmetric Lovasz Local Lemma criterion (`AsymmetricLLLThreshold`). Formalizes spherical-cap de-crowding validity (`ValidLLLSphericalCapPerturbation`), period-`bdlPeriodL` patch locality (`IsPeriodicLLLShift`, `IsLocalLLLCapAssignment`), and the canonical Step 1 selector `bdlLLLPerturbation`.

## References

* Part I, Section 2.1 (`subsec:css-complexes`), Definition 2.2 (`def:well-separated-base`), Section 2.2 (`subsec:step1-lll`), Proposition 2.4 (`prop:step1-lll`)
* Balasubramanian, Davydova, and Lin (2026)
-/

noncomputable section

open scoped Classical BigOperators

/-! ## 1. Step 1 Scaling by $\lambda_{\mathrm{BDL}}$ and Spherical-Cap Perturbation -/

/-- 3D linear interpolation between `p, q : Point3D` at subdivision step `j` of `M`. -/
def subdividePoint3D (p q : Point3D) (M : ℕ) (j : ℕ) : Point3D :=
  fun axis => p axis + ((j : ℝ) / (M : ℝ)) * (q axis - p axis)

/-- Continuous linear interpolation $(1 - t) p + t q$ ($t \in [0, 1]$) between `p, q : Point3D`. -/
def lerpPoint3D (p q : Point3D) (t : ℝ) : Point3D :=
  fun axis => (1 - t) * p axis + t * q axis

/-- Closed 2-simplex $\Delta(p_1, p_2, p_3) \subset \mathbb{R}^3$ spanned by `p1, p2, p3 : Point3D`. -/
def simplex2D3D (p1 p2 p3 : Point3D) : Set Point3D :=
  {x : Point3D | ∃ (t1 t2 t3 : ℝ), 0 ≤ t1 ∧ 0 ≤ t2 ∧ 0 ≤ t3 ∧ t1 + t2 + t3 = 1 ∧
    ∀ axis : Fin 3, x axis = t1 * p1 axis + t2 * p2 axis + t3 * p3 axis}

/-- Step 1 scaling and perturbation: scales vertex positions by `lam` and shifts by `(cQ, cZ, cX)`. -/
def bdlPerturbStep {Q M_Z M_X : Type}
    [Fintype Q] [DecidableEq Q] [Fintype M_Z] [DecidableEq M_Z] [Fintype M_X] [DecidableEq M_X]
    (code : CSSCode3D Q M_Z M_X) (lam : ℕ)
    (cQ : Q → Point3D) (cZ : M_Z → Point3D) (cX : M_X → Point3D) :
    CSSCode3D Q M_Z M_X where
  posQ q axis := (lam : ℝ) * code.posQ q axis + cQ q axis
  posZ mZ axis := (lam : ℝ) * code.posZ mZ axis + cZ mZ axis
  posX mX axis := (lam : ℝ) * code.posX mX axis + cX mX axis
  checkX := code.checkX
  checkZ := code.checkZ
  commutativity := code.commutativity

/-- Active 2-simplices `(mX, q, mZ)` of the triangulated Tanner complex $T_{(i)}$. -/
abbrev ActiveSimplex2 {Q M_Z M_X : Type}
    [Fintype Q] [DecidableEq Q] [Fintype M_Z] [DecidableEq M_Z] [Fintype M_X] [DecidableEq M_X]
    (code : CSSCode3D Q M_Z M_X) : Type :=
  {s : M_X × Q × M_Z // code.checkX s.1 s.2.1 ≠ 0 ∧ code.checkZ s.2.2 s.2.1 ≠ 0}

/-- Spherical-cap radius $R_{\mathrm{cap}} = \alpha \lambda_{\mathrm{BDL}}$ (Part I, Section 2.2 (`subsec:step1-lll`), Proposition 2.4 (`prop:step1-lll`)). -/
def bdlCapRadius : ℝ := bdlAlpha * (bdlLambda : ℝ)

/-- Default spherical-cap shift vector on the sphere of radius `bdlCapRadius` along `axis_idx`. -/
def fallbackCapShift (axis_idx : Fin 3) : Point3D :=
  fun a => if a = axis_idx then bdlCapRadius else 0

/-! ## 2. Archimedes Spherical-Cap Measure & Asymmetric Lovász Local Lemma -/

/-- Archimedes normalized spherical-cap measure $\mu_{S^2}(\mathrm{Cap}(r)) = r / 2$ for slab height
    $r = 1 - \cos\theta \in [0, 2]$ on the unit sphere $S^2$. -/
def archimedesCapMeasure (r : ℝ) : ℝ := r / 2

/-- Asymmetric Lovász Local Lemma threshold condition $p(e) \le x(e) \prod_{e' \in \Gamma(e)} (1 - x(e'))$. -/
def AsymmetricLLLThreshold {E : Type} [Fintype E]
    (dep : E → Finset E) (p x : E → ℝ) : Prop :=
  (∀ e : E, e ∉ dep e) ∧
  (∀ e : E, 0 ≤ x e ∧ x e < 1) ∧
  (∀ e : E, 0 ≤ p e ∧ p e ≤ x e * ∏ e' ∈ dep e, (1 - x e'))

/-- Strictly positive Lovász Local Lemma simultaneous avoidance weight $\prod_{e \in E} (1 - x(e)) > 0$. -/
def asymmetricLLLAvoidanceLowerBound {E : Type} [Fintype E] (x : E → ℝ) : ℝ :=
  ∏ e : E, (1 - x e)

lemma asymmetricLLLAvoidanceLowerBound_pos {E : Type} [Fintype E]
    {dep : E → Finset E} {p x : E → ℝ} (h : AsymmetricLLLThreshold dep p x) :
    0 < asymmetricLLLAvoidanceLowerBound x := by
  dsimp [asymmetricLLLAvoidanceLowerBound]
  exact Finset.prod_pos (fun e _ => sub_pos.mpr (h.2.1 e).2)

/-! ## 3. Continuous $\mathbb{R}$-Valued Spherical-Cap Perturbation Validity & Period-$P_{\mathrm{LLL}}$ Locality -/

/-- LLL Spherical-Cap Perturbation Validity (Part I, Section 2.2 (`subsec:step1-lll`), Proposition 2.4 (`prop:step1-lll`); Balasubramanian–Davydova–Lin (2026), Section 3.1, Lemma 3.3). -/
def ValidLLLSphericalCapPerturbation (B : BundledCSSCode3D)
    (c : (B.Q → Point3D) × (B.M_Z → Point3D) × (B.M_X → Point3D)) : Prop :=
  let pcode := bdlPerturbStep B.code bdlLambda c.1 c.2.1 c.2.2
  (∀ q : B.Q, distSq3D (c.1 q) (fun _ => 0) = bdlCapRadius ^ 2) ∧
  (∀ mZ : B.M_Z, distSq3D (c.2.1 mZ) (fun _ => 0) = bdlCapRadius ^ 2) ∧
  (∀ mX : B.M_X, distSq3D (c.2.2 mX) (fun _ => 0) = bdlCapRadius ^ 2) ∧
  (∀ (mZ : B.M_Z) (q : B.Q), B.code.checkZ mZ q ≠ 0 →
    ((bdlAlpha2 - 1) * (bdlLambda : ℝ)) ^ 2 ≤ distSq3D (pcode.posQ q) (pcode.posZ mZ) ∧
    distSq3D (pcode.posQ q) (pcode.posZ mZ) ≤ ((2 * bdlAlpha + 1) * (bdlLambda : ℝ)) ^ 2) ∧
  (∀ (mX : B.M_X) (q : B.Q), B.code.checkX mX q ≠ 0 →
    ((bdlAlpha2 - 1) * (bdlLambda : ℝ)) ^ 2 ≤ distSq3D (pcode.posQ q) (pcode.posX mX) ∧
    distSq3D (pcode.posQ q) (pcode.posX mX) ≤ ((2 * bdlAlpha + 1) * (bdlLambda : ℝ)) ^ 2) ∧
  (∀ (s : ActiveSimplex2 B.code) (ε : ℝ), 0 ≤ ε → ε ≤ 1 →
    (bdlGamma * (bdlLambda : ℝ)) ^ 2 ≤
      distSq3D (pcode.posX s.val.1) (lerpPoint3D (pcode.posQ s.val.2.1) (pcode.posZ s.val.2.2) ε) ∧
    (bdlGamma * (bdlLambda : ℝ)) ^ 2 ≤
      distSq3D (pcode.posQ s.val.2.1) (lerpPoint3D (pcode.posX s.val.1) (pcode.posZ s.val.2.2) ε) ∧
    (bdlGamma * (bdlLambda : ℝ)) ^ 2 ≤
      distSq3D (pcode.posZ s.val.2.2) (lerpPoint3D (pcode.posX s.val.1) (pcode.posQ s.val.2.1) ε)) ∧
  (∀ x0 : Point3D,
    ((Finset.univ.filter (fun s : ActiveSimplex2 B.code =>
      (simplex2D3D (pcode.posX s.val.1) (pcode.posQ s.val.2.1) (pcode.posZ s.val.2.2) ∩
        ball3D x0 1).Nonempty)).card : ℝ) ≤ bdlDensityTPrime ∧
    ((Finset.univ.filter (fun q : B.Q => pcode.posQ q ∈ ball3D x0 1)).card : ℝ) ≤ bdlDensityTPrime ∧
    ((Finset.univ.filter (fun m : B.M_Z => pcode.posZ m ∈ ball3D x0 1)).card : ℝ) ≤ bdlDensityTPrime ∧
    ((Finset.univ.filter (fun m : B.M_X => pcode.posX m ∈ ball3D x0 1)).card : ℝ) ≤ bdlDensityTPrime)

/-- Exact normalized surface-area fraction $\mu_{S^2}(\mathrm{Cap}(\theta)) = (1 - \cos\theta) / 2$
    of a spherical cap of angular radius $\theta$ on $S^2$ (`Real.cos`). -/
def sphericalCapAreaFraction (θ : ℝ) : ℝ :=
  (1 - Real.cos θ) / 2

/-- Conditional spherical-cap probability $\mathbb{P}(\mathrm{Cap}(\theta_{\mathrm{bad}}) \mid \mathrm{Cap}(\theta_{\mathrm{cap}}))
    = (1 - \cos\theta_{\mathrm{bad}}) / (1 - \cos\theta_{\mathrm{cap}})$ under uniform surface measure on $S^2$. -/
def relativeSphericalCapProb (θ_bad θ_cap : ℝ) : ℝ :=
  (1 - Real.cos θ_bad) / (1 - Real.cos θ_cap)

/-- Continuous spherical coordinates on the cap along axis `0` of $S^2(R_{\mathrm{cap}})$
    parameterized by polar angle $\theta$ and azimuthal angle $\varphi$ (`Real.cos`, `Real.sin`). -/
def sphericalCapPoint0 (θ φ : ℝ) : Point3D :=
  fun a =>
    if a = 0 then bdlCapRadius * Real.cos θ
    else if a = 1 then bdlCapRadius * Real.sin θ * Real.cos φ
    else bdlCapRadius * Real.sin θ * Real.sin φ

/-- Continuous spherical coordinates on the cap along axis `1` of $S^2(R_{\mathrm{cap}})$. -/
def sphericalCapPoint1 (θ φ : ℝ) : Point3D :=
  fun a =>
    if a = 0 then bdlCapRadius * Real.sin θ * Real.sin φ
    else if a = 1 then bdlCapRadius * Real.cos θ
    else bdlCapRadius * Real.sin θ * Real.cos φ

/-- Continuous spherical coordinates on the cap along axis `2` of $S^2(R_{\mathrm{cap}})$. -/
def sphericalCapPoint2 (θ φ : ℝ) : Point3D :=
  fun a =>
    if a = 0 then bdlCapRadius * Real.sin θ * Real.cos φ
    else if a = 1 then bdlCapRadius * Real.sin θ * Real.sin φ
    else bdlCapRadius * Real.cos θ

/-- Continuous spherical-cap angle assignment $(\theta_v, \varphi_v) \in [0, \theta_{\mathrm{cap}}] \times [0, 2\pi)$
    for all vertices of `B : BundledCSSCode3D`. -/
abbrev BDLCapAngleAssignment (B : BundledCSSCode3D) : Type :=
  (B.Q → ℝ × ℝ) × (B.M_Z → ℝ × ℝ) × (B.M_X → ℝ × ℝ)

/-- Perturbation tuple `(cQ, cZ, cX)` induced by a continuous spherical-cap angle assignment `ω`. -/
def bdlCapPerturbationOf (B : BundledCSSCode3D) (ω : BDLCapAngleAssignment B) :
    (B.Q → Point3D) × (B.M_Z → Point3D) × (B.M_X → Point3D) :=
  (fun q => sphericalCapPoint0 (ω.1 q).1 (ω.1 q).2,
   fun z => sphericalCapPoint1 (ω.2.1 z).1 (ω.2.1 z).2,
   fun x => sphericalCapPoint2 (ω.2.2 x).1 (ω.2.2 x).2)

/-- Periodic cube-color shift relation $p_2 - p_1 \in (P_{\mathrm{LLL}} \mathbb{Z})^3$ (`bdlPeriodL`). -/
def IsPeriodicLLLShift (p1 p2 : Point3D) : Prop :=
  ∃ k : Fin 3 → ℤ, ∀ a : Fin 3, p2 a - p1 a = (bdlPeriodL : ℝ) * (k a : ℝ)

/-- Local coarse neighborhood isomorphism modulo $P_{\mathrm{LLL}} \mathbb{Z}^3$ on balls of radius `bdlLLLReach`. -/
def SameLocalCoarsePatchAt (B : BundledCSSCode3D) (p1 p2 : Point3D) : Prop :=
  IsPeriodicLLLShift p1 p2 ∧
  (∀ δ : Point3D, distSq3D δ (fun _ => 0) ≤ (bdlLLLReach : ℝ) ^ 2 →
    ((∃ q : B.Q, ∀ a, B.code.posQ q a - p1 a = δ a) ↔
     (∃ q : B.Q, ∀ a, B.code.posQ q a - p2 a = δ a)) ∧
    ((∃ z : B.M_Z, ∀ a, B.code.posZ z a - p1 a = δ a) ↔
     (∃ z : B.M_Z, ∀ a, B.code.posZ z a - p2 a = δ a)) ∧
    ((∃ x : B.M_X, ∀ a, B.code.posX x a - p1 a = δ a) ↔
     (∃ x : B.M_X, ∀ a, B.code.posX x a - p2 a = δ a))) ∧
  (∀ δ1 δ2 : Point3D,
    distSq3D δ1 (fun _ => 0) ≤ (bdlLLLReach : ℝ) ^ 2 →
    distSq3D δ2 (fun _ => 0) ≤ (bdlLLLReach : ℝ) ^ 2 →
    ((∃ (x : B.M_X) (q : B.Q), B.code.checkX x q ≠ 0 ∧
       (∀ a, B.code.posX x a - p1 a = δ1 a) ∧ (∀ a, B.code.posQ q a - p1 a = δ2 a)) ↔
     (∃ (x : B.M_X) (q : B.Q), B.code.checkX x q ≠ 0 ∧
       (∀ a, B.code.posX x a - p2 a = δ1 a) ∧ (∀ a, B.code.posQ q a - p2 a = δ2 a))) ∧
    ((∃ (z : B.M_Z) (q : B.Q), B.code.checkZ z q ≠ 0 ∧
       (∀ a, B.code.posZ z a - p1 a = δ1 a) ∧ (∀ a, B.code.posQ q a - p1 a = δ2 a)) ↔
     (∃ (z : B.M_Z) (q : B.Q), B.code.checkZ z q ≠ 0 ∧
       (∀ a, B.code.posZ z a - p2 a = δ1 a) ∧ (∀ a, B.code.posQ q a - p2 a = δ2 a))))

/-- Locality predicate: `ω` assigns identical spherical-cap angles to vertices with identical local
    coarse neighborhoods of radius `bdlLLLReach` modulo $P_{\mathrm{LLL}} \mathbb{Z}^3$. -/
def IsLocalLLLCapAssignment (B : BundledCSSCode3D) (ω : BDLCapAngleAssignment B) : Prop :=
  (∀ q1 q2 : B.Q, SameLocalCoarsePatchAt B (B.code.posQ q1) (B.code.posQ q2) → ω.1 q1 = ω.1 q2) ∧
  (∀ z1 z2 : B.M_Z, SameLocalCoarsePatchAt B (B.code.posZ z1) (B.code.posZ z2) → ω.2.1 z1 = ω.2.1 z2) ∧
  (∀ x1 x2 : B.M_X, SameLocalCoarsePatchAt B (B.code.posX x1) (B.code.posX x2) → ω.2.2 x1 = ω.2.2 x2)

/-- Canonical local spherical-cap LLL perturbation: valid and local on radius-`bdlLLLReach` patches
    modulo `bdlPeriodL`. -/
def IsCanonicalLocalCapLLLPerturbation (B : BundledCSSCode3D)
    (c : (B.Q → Point3D) × (B.M_Z → Point3D) × (B.M_X → Point3D)) : Prop :=
  ValidLLLSphericalCapPerturbation B c ∧
  ∃ ω : BDLCapAngleAssignment B,
    c = bdlCapPerturbationOf B ω ∧ IsLocalLLLCapAssignment B ω

/-- Full canonical validity predicate for `bdlLLLPerturbation`. -/
def ValidCanonicalLLLSphericalCapPerturbation (B : BundledCSSCode3D)
    (c : (B.Q → Point3D) × (B.M_Z → Point3D) × (B.M_X → Point3D)) : Prop :=
  ValidLLLSphericalCapPerturbation B c ∧
  ((∃ c', IsCanonicalLocalCapLLLPerturbation B c') → IsCanonicalLocalCapLLLPerturbation B c)

lemma exists_validCanonicalLLLSphericalCapPerturbation (B : BundledCSSCode3D)
    (h : ∃ c, ValidLLLSphericalCapPerturbation B c) :
    ∃ c, ValidCanonicalLLLSphericalCapPerturbation B c := by
  by_cases h1 : ∃ c', IsCanonicalLocalCapLLLPerturbation B c'
  · rcases h1 with ⟨c', hc'⟩
    exact ⟨c', hc'.1, fun _ => hc'⟩
  · rcases h with ⟨c, hc⟩
    exact ⟨c, hc, fun h1' => False.elim (h1 h1')⟩

/-- Deterministic canonical LLL spherical-cap perturbation selector `bdlLLLPerturbation`. -/
noncomputable def bdlLLLPerturbation (B : BundledCSSCode3D) :
    (B.Q → Point3D) × (B.M_Z → Point3D) × (B.M_X → Point3D) :=
  if h : ∃ c, ValidCanonicalLLLSphericalCapPerturbation B c then
    Classical.choose h
  else
    (fun _ => fallbackCapShift 0, fun _ => fallbackCapShift 1, fun _ => fallbackCapShift 2)

lemma bdlLLLPerturbation_spec_of_exists (B : BundledCSSCode3D)
    (h : ∃ c, ValidLLLSphericalCapPerturbation B c) :
    ValidLLLSphericalCapPerturbation B (bdlLLLPerturbation B) := by
  have h_can := exists_validCanonicalLLLSphericalCapPerturbation B h
  dsimp [bdlLLLPerturbation]
  rw [dif_pos h_can]
  exact (Classical.choose_spec h_can).1

end
