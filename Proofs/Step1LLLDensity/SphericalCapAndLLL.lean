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

import Proofs.Step2DegreeAndWeld.DegreeOverlapAndDensityPreservation

/-!
# Spherical-Cap Geometry, Archimedes Measure, and Unconditional Step-1 LLL Existence

Top-level Step-1 synthesis module proving the continuous spherical-cap norm identity (`sphericalCapPoint_distSq_eq`), conditional cap probability bounds (`relativeSphericalCapProb_mem_Icc`), and Archimedes slab measure identity (`sphericalCapAreaFraction_eq_archimedes`). Packages the inductive geometric bounds (`bdlWeldedBundled_geometric_bounds`), unconditional Step-1 perturbation existence (`bdl_step1_lll_perturbation_exists`), and canonical selector validity (`bdlWeldedBundled_validLLLPerturbation`) for `bdlWeldedBundled k` at every hierarchy level.

## References

* Part I, Section 2.2 (`subsec:step1-lll`), Proposition 2.4 (`prop:step1-lll`), Equation (2) (`eq:archimedes-slab-bound`)
* Part I, Section 2.3 (`subsec:step2-mapping-cone`), Proposition 2.6 (`prop:mapping-cone-invariants`)
-/

noncomputable section

open scoped Classical BigOperators

/-! ## 1. Continuous Spherical-Cap Norm Identity, Archimedes Slab Measure & Lovász Local Lemma -/

/-- Every point on the continuous spherical caps `sphericalCapPoint0 θ φ`, `sphericalCapPoint1 θ φ`,
    and `sphericalCapPoint2 θ φ` lies on the sphere of radius `bdlCapRadius = bdlAlpha * bdlLambda`
    centered at the origin (`Real.cos_sq_add_sin_sq`). -/
theorem sphericalCapPoint_distSq_eq (θ φ : ℝ) :
    distSq3D (sphericalCapPoint0 θ φ) (fun _ => 0) = bdlCapRadius ^ 2 ∧
    distSq3D (sphericalCapPoint1 θ φ) (fun _ => 0) = bdlCapRadius ^ 2 ∧
    distSq3D (sphericalCapPoint2 θ φ) (fun _ => 0) = bdlCapRadius ^ 2 := by
  have hθ : Real.cos θ ^ 2 + Real.sin θ ^ 2 = 1 := Real.cos_sq_add_sin_sq θ
  have hφ : Real.cos φ ^ 2 + Real.sin φ ^ 2 = 1 := Real.cos_sq_add_sin_sq φ
  refine ⟨?_, ?_, ?_⟩
  · dsimp [distSq3D, sphericalCapPoint0]
    simp only [Fin.isValue, ↓reduceIte, Fin.one_eq_zero_iff, OfNat.ofNat_ne_zero,
      Fin.reduceEq, sub_zero]
    calc (bdlCapRadius * Real.cos θ) ^ 2 +
          (bdlCapRadius * Real.sin θ * Real.cos φ) ^ 2 +
          (bdlCapRadius * Real.sin θ * Real.sin φ) ^ 2
      _ = bdlCapRadius ^ 2 * (Real.cos θ ^ 2 + Real.sin θ ^ 2 * (Real.cos φ ^ 2 + Real.sin φ ^ 2)) := by ring
      _ = bdlCapRadius ^ 2 * (Real.cos θ ^ 2 + Real.sin θ ^ 2 * 1) := by rw [hφ]
      _ = bdlCapRadius ^ 2 * (Real.cos θ ^ 2 + Real.sin θ ^ 2) := by ring
      _ = bdlCapRadius ^ 2 * 1 := by rw [hθ]
      _ = bdlCapRadius ^ 2 := by ring
  · dsimp [distSq3D, sphericalCapPoint1]
    simp only [Fin.isValue, ↓reduceIte, Fin.zero_eq_one_iff, OfNat.ofNat_ne_zero,
      Fin.reduceEq, sub_zero]
    calc (bdlCapRadius * Real.sin θ * Real.sin φ) ^ 2 +
          (bdlCapRadius * Real.cos θ) ^ 2 +
          (bdlCapRadius * Real.sin θ * Real.cos φ) ^ 2
      _ = bdlCapRadius ^ 2 * (Real.cos θ ^ 2 + Real.sin θ ^ 2 * (Real.cos φ ^ 2 + Real.sin φ ^ 2)) := by ring
      _ = bdlCapRadius ^ 2 * (Real.cos θ ^ 2 + Real.sin θ ^ 2 * 1) := by rw [hφ]
      _ = bdlCapRadius ^ 2 * (Real.cos θ ^ 2 + Real.sin θ ^ 2) := by ring
      _ = bdlCapRadius ^ 2 * 1 := by rw [hθ]
      _ = bdlCapRadius ^ 2 := by ring
  · dsimp [distSq3D, sphericalCapPoint2]
    simp only [Fin.isValue, ↓reduceIte, Fin.zero_eq_one_iff, OfNat.ofNat_ne_zero,
      Fin.reduceEq, sub_zero]
    calc (bdlCapRadius * Real.sin θ * Real.cos φ) ^ 2 +
          (bdlCapRadius * Real.sin θ * Real.sin φ) ^ 2 +
          (bdlCapRadius * Real.cos θ) ^ 2
      _ = bdlCapRadius ^ 2 * (Real.cos θ ^ 2 + Real.sin θ ^ 2 * (Real.cos φ ^ 2 + Real.sin φ ^ 2)) := by ring
      _ = bdlCapRadius ^ 2 * (Real.cos θ ^ 2 + Real.sin θ ^ 2 * 1) := by rw [hφ]
      _ = bdlCapRadius ^ 2 * (Real.cos θ ^ 2 + Real.sin θ ^ 2) := by ring
      _ = bdlCapRadius ^ 2 * 1 := by rw [hθ]
      _ = bdlCapRadius ^ 2 := by ring

/-- For $0 \le \theta_{\mathrm{bad}} \le \theta_{\mathrm{cap}} \le \pi$ with $\cos \theta_{\mathrm{cap}} < 1$,
    the conditional spherical-cap probability `relativeSphericalCapProb θ_bad θ_cap` lies in $[0, 1]$. -/
theorem relativeSphericalCapProb_mem_Icc {θ_bad θ_cap : ℝ}
    (h0 : 0 ≤ θ_bad) (hle : θ_bad ≤ θ_cap) (hpi : θ_cap ≤ Real.pi)
    (hcos : Real.cos θ_cap < 1) :
    0 ≤ relativeSphericalCapProb θ_bad θ_cap ∧
    relativeSphericalCapProb θ_bad θ_cap ≤ 1 := by
  dsimp [relativeSphericalCapProb]
  have h_pos : 0 < 1 - Real.cos θ_cap := sub_pos.mpr hcos
  have h_nonneg : 0 ≤ 1 - Real.cos θ_bad := sub_nonneg.mpr (Real.cos_le_one θ_bad)
  have h_cos_le : Real.cos θ_cap ≤ Real.cos θ_bad :=
    Real.cos_le_cos_of_nonneg_of_le_pi h0 hpi hle
  refine ⟨div_nonneg h_nonneg (le_of_lt h_pos), (div_le_one h_pos).mpr ?_⟩
  linarith

/-- Exact Archimedes slab identity connecting `sphericalCapAreaFraction θ` to
    `archimedesCapMeasure (1 - Real.cos θ)`. -/
theorem sphericalCapAreaFraction_eq_archimedes (θ : ℝ) :
    sphericalCapAreaFraction θ = archimedesCapMeasure (1 - Real.cos θ) := rfl

/-- Asymmetric Lovász Local Lemma simultaneous avoidance positivity (Part I, Section 2.2 (`subsec:step1-lll`), Proposition 2.4 (`prop:step1-lll`)). -/
theorem bdl_asymmetric_lll_avoidance_pos {E : Type} [Fintype E]
    {dep : E → Finset E} {p x : E → ℝ} (h_lll : AsymmetricLLLThreshold dep p x) :
    0 < asymmetricLLLAvoidanceLowerBound x :=
  asymmetricLLLAvoidanceLowerBound_pos h_lll

/-! ## 2. Unconditional Step 1 LLL Perturbation Existence & Selector Validity (Part I, Section 2.2 (`subsec:step1-lll`), Proposition 2.4 (`prop:step1-lll`)) -/

/-- **Inductive Simplex Degree $D \le 32$, Check-Degree Overlap, Non-Isolated Qubits, Interaction Range $\le 8$,
    and Unit-Ball Vertex Density $T$ Bounds (Part I, Section 2.2 (`subsec:step1-lll`), Proposition 2.4 (`prop:step1-lll`) and Section 2.3 (`subsec:step2-mapping-cone`), Proposition 2.6 (`prop:mapping-cone-invariants`))**:
    For every hierarchy level $k \in \mathbb{N}$, the bundled 3-layer welded BDL code `bdlWeldedBundled k`
    satisfies `WeldedHierarchy.HasBoundedSimplexDegreeD (bdlWeldedBundled k) 32`,
    `WeldedHierarchy.HasInteractionRange8 (bdlWeldedBundled k)`,
    and `WeldedHierarchy.HasUnitBallDensityT (bdlWeldedBundled k)`. -/
theorem bdlWeldedBundled_geometric_bounds (k : ℕ) :
    WeldedHierarchy.HasBoundedSimplexDegreeD (bdlWeldedBundled k) 32 ∧
    WeldedHierarchy.HasInteractionRange8 (bdlWeldedBundled k) ∧
    WeldedHierarchy.HasUnitBallDensityT (bdlWeldedBundled k) := by
  have h_ov : WeldedHierarchy.HasBoundedCheckDegreeOverlap (bdlWeldedBundled k) :=
    WeldedHierarchy.hasBoundedCheckDegreeOverlap_bdlIterated (k + 1)
  exact ⟨WeldedHierarchy.hasBoundedSimplexDegreeD_32_of_hasBoundedCheckDegreeOverlap (bdlWeldedBundled k) h_ov,
         WeldedHierarchy.bdl_random_interaction_range8 k,
         WeldedHierarchy.hasUnitBallDensityT_bdlIterated (k + 1)⟩

/-- **Unconditional Step 1 Lovász Local Lemma Perturbation Existence Theorem (Part I, Section 2.2 (`subsec:step1-lll`), Proposition 2.4 (`prop:step1-lll`); Balasubramanian–Davydova–Lin (2026), Lemma 3.3, Claims 3.4 & 3.5)**:
    For any bundled 3D CSS code `B` with simplex degree $D \le 32$, interaction range $\le 8$, and
    unit-ball vertex density $\le T$, the spherical-cap product measure and asymmetric Lovász
    Local Lemma guarantee the existence of a valid spherical-cap perturbation
    `c : (B.Q → Point3D) × (B.M_Z → Point3D) × (B.M_X → Point3D)` satisfying
    `ValidLLLSphericalCapPerturbation B c`. -/
theorem bdl_step1_lll_perturbation_exists (B : BundledCSSCode3D)
    (h_deg : WeldedHierarchy.HasBoundedSimplexDegreeD B 32)
    (h8 : WeldedHierarchy.HasInteractionRange8 B)
    (h_dens : WeldedHierarchy.HasUnitBallDensityT B) :
    ∃ c, ValidLLLSphericalCapPerturbation B c :=
  WeldedHierarchy.bdl_step1_lll_perturbation_exists B h_deg h8 h_dens

/-- **Unconditional Step 1 LLL Perturbation Existence and Selector Validity for `bdlWeldedBundled k`**:
    For every hierarchy level $k \in \mathbb{N}$ (with **zero conditional existence hypothesis**),
    a valid spherical-cap perturbation exists on `bdlWeldedBundled k` and the canonical selector
    `bdlLLLPerturbation (bdlWeldedBundled k)` satisfies `ValidLLLSphericalCapPerturbation`. -/
theorem bdlWeldedBundled_validLLLPerturbation (k : ℕ) :
    (∃ c, ValidLLLSphericalCapPerturbation (bdlWeldedBundled k) c) ∧
    ValidLLLSphericalCapPerturbation (bdlWeldedBundled k)
      (bdlLLLPerturbation (bdlWeldedBundled k)) := by
  have h_geom := bdlWeldedBundled_geometric_bounds k
  rcases bdl_step1_lll_perturbation_exists (bdlWeldedBundled k) h_geom.1 h_geom.2.1 h_geom.2.2 with
    ⟨c, hc⟩
  exact ⟨⟨c, hc⟩, bdlLLLPerturbation_spec_of_exists (bdlWeldedBundled k) ⟨c, hc⟩⟩
