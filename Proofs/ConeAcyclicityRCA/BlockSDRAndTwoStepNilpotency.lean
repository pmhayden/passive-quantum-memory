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

import Proofs.Step2DegreeAndWeld.BDLSubstitutionRealization
import Proofs.ConeAcyclicityRCA.RescaledRCASynthesis
import Defs.ContractionAndHPL
import Defs.RescaledRCA

/-!
# Three-Layer Block SDR Nilpotency, Descriptor Validity, and Welded Collar Transfer

Proves two-step nilpotency (h ∘ g)^2 = 0 for three-layer block-diagonal homotopies and strictly grade-increasing vertical attachments (three_layer_welded_two_step_nilpotency), verifies ValidDescriptorField for bdlLocalDescriptor (bdlLocalDescriptor_validDescriptorField), and transfers continuum l_infty cone acyclicity of bdlWeldedCode to the explicit linear collar expansion constants (bdlWeldedStep_blockSDR_transfer).

## References

* Part I, Section 3.2 (`subsec:nilpotent-hpl`), Lemma 3.6 (`lem:block-sdr`), Proposition 3.7 (`prop:classical-hpl`)
* Part I, Section 3.3 (`subsec:scale-matched-rca`), Theorem 3.9 (`thm:rca-welded-hierarchy`)
* Part II, Section 4 (`subsec:welded-hierarchy-cleaner`), Proposition 4.3 (`prop:rca-hierarchy`)
-/

noncomputable section

open scoped Classical BigOperators

/-! ## 1. Two-Step Nilpotency $(h \circ g)^2 = 0$ of the 3-Layer Welded Block Coupling -/

/-- Any 3-layer block-diagonal homotopy $h = h_X \oplus h_Q \oplus 0$ on $I_X \oplus I_Q \oplus I_Z$
    satisfies `PreservesSectorGradeAndVanishesOnZ sectorGrade h`, and any vertical attachment map
    $g = g_{XQ} + g_{QZ}$ mapping $I_X \to I_Q$, $I_Q \to I_Z$, and $I_Z \to 0$ satisfies
    `StrictlyIncreasesSectorGrade sectorGrade g`, so $h(g(h(g(c)))) = 0$ for every chain $c$. -/
theorem three_layer_welded_two_step_nilpotency
    {I_X I_Q I_Z : Type*} [Fintype I_X] [DecidableEq I_X]
    [Fintype I_Q] [DecidableEq I_Q] [Fintype I_Z] [DecidableEq I_Z]
    (h g : (I_X ⊕ I_Q ⊕ I_Z → ZMod 2) → (I_X ⊕ I_Q ⊕ I_Z → ZMod 2))
    (hlh : ∀ x y, h (x + y) = h x + h y)
    (hlg : ∀ x y, g (x + y) = g x + g y)
    (hh : PreservesSectorGradeAndVanishesOnZ sectorGrade h)
    (hg : StrictlyIncreasesSectorGrade sectorGrade g)
    (c : I_X ⊕ I_Q ⊕ I_Z → ZMod 2) :
    h (g (h (g c))) = 0 := by
  have hh0 : h 0 = 0 := hh.2 0 (fun _ hi => False.elim (hi rfl))
  have hg0 : g 0 = 0 := hg.2.2 0 (fun _ hi => False.elim (hi rfl))
  let c0 : I_X ⊕ I_Q ⊕ I_Z → ZMod 2 := fun i => if sectorGrade i = 0 then c i else 0
  let c1 : I_X ⊕ I_Q ⊕ I_Z → ZMod 2 := fun i => if sectorGrade i = 1 then c i else 0
  let c2 : I_X ⊕ I_Q ⊕ I_Z → ZMod 2 := fun i => if sectorGrade i = 2 then c i else 0
  have hc_decomp : c = c0 + c1 + c2 := by
    ext i
    change c i = c0 i + c1 i + c2 i
    dsimp [c0, c1, c2, sectorGrade]
    rcases i with _ | (_ | _) <;> simp
  have hc0_grade : ∀ i, c0 i ≠ 0 → sectorGrade i = 0 := by
    intro i hi; dsimp [c0] at hi; by_contra hne; exact hi (if_neg hne)
  have hc1_grade : ∀ i, c1 i ≠ 0 → sectorGrade i = 1 := by
    intro i hi; dsimp [c1] at hi; by_contra hne; exact hi (if_neg hne)
  have hc2_grade : ∀ i, c2 i ≠ 0 → sectorGrade i = 2 := by
    intro i hi; dsimp [c2] at hi; by_contra hne; exact hi (if_neg hne)
  have h_c2 : h (g (h (g c2))) = 0 := by
    rw [hg.2.2 c2 hc2_grade, hh0, hg0, hh0]
  have h_c1 : h (g (h (g c1))) = 0 := by
    have hg1 : ∀ i, g c1 i ≠ 0 → sectorGrade i = 2 := hg.2.1 c1 hc1_grade
    rw [hh.2 (g c1) hg1, hg0, hh0]
  have h_c0 : h (g (h (g c0))) = 0 := by
    have hg0_1 : ∀ i, g c0 i ≠ 0 → sectorGrade i = 1 := hg.1 c0 hc0_grade
    have hhg0_1 : ∀ i, h (g c0) i ≠ 0 → sectorGrade i = 1 := hh.1 (g c0) 1 hg0_1
    have hghg0_2 : ∀ i, g (h (g c0)) i ≠ 0 → sectorGrade i = 2 := hg.2.1 (h (g c0)) hhg0_1
    exact hh.2 (g (h (g c0))) hghg0_2
  rw [hc_decomp, hlg, hlg, hlh, hlh, hlg, hlg, hlh, hlh, h_c0, h_c1, h_c2, add_zero, add_zero]

/-! ## 2. Global Validity of the Multi-Site BDL Descriptor Field & 3-Layer Block SDR Transfer -/

/-- **Global Open-Box Validity of the Multi-Site BDL Descriptor Field (`ValidDescriptorField (bdlLocalDescriptor k)`)**:
    For every hierarchy level $k \in \mathbb{N}$, the grid-snapped multi-site 3-layer welded descriptor field
    `bdlLocalDescriptor k` on `Box3D (bdlBoxSide k)` satisfies:
    1. Every active check fits inside the open box `Box3D (bdlBoxSide k)` without wrapping around boundaries;
    2. Every active check touches only active qubit slots (`activeSlot s = true`);
    3. Every active $X$-check chain and active $Z$-check chain have even symplectic overlap over $\mathbb{F}_2$. -/
theorem bdlLocalDescriptor_validDescriptorField (k : ℕ) :
    ValidDescriptorField (bdlLocalDescriptor k) :=
  bdlLocalDescriptor_validDescriptorField_proof k

lemma bdlLinearTQORadius_le_pow (k : ℕ) :
    (bdlLinearTQORadius k : ℝ) ≤ (bdlLambda : ℝ) ^ (2 * k) := by
  have h_pos : (0 : ℝ) < (bdlLambda : ℝ) := Nat.cast_pos.mpr bdlLambda_pos
  have h_ne4 : ((bdlLambda : ℝ) ^ 4) ≠ 0 := pow_ne_zero 4 (ne_of_gt h_pos)
  have h_nonneg : 0 ≤ cStarBDL * (bdlBoxSide k : ℝ) :=
    mul_nonneg (le_of_lt c_star_bdl_pos) (Nat.cast_nonneg _)
  have h_fl : (bdlLinearTQORadius k : ℝ) ≤ cStarBDL * (bdlBoxSide k : ℝ) :=
    Nat.floor_le h_nonneg
  have h_eq : cStarBDL * (bdlBoxSide k : ℝ) = (bdlLambda : ℝ) ^ (2 * k) := by
    dsimp [cStarBDL, bdlBoxSide, bdlHierarchySteps, bBDL]
    push_cast
    rw [pow_add]
    field_simp [h_ne4]
  linarith

/-- **Collar Radius-Monotonicity Corollary for `bdlWeldedCode k` (Part I, Theorem 3.9 (`thm:rca-welded-hierarchy`))**:
    For every hierarchy level $k \in \mathbb{N}$, center $x_0 \in \mathbb{R}^3$, and radius
    $0 \le r \le \mathrm{bdlLinearTQORadius}\ k$, primal and dual 1-cocycles supported in
    `ballQ (bdlWeldedCode k) x0 r` are generated by checks in `ballMZ` / `ballMX` of radius
    `(collarConstRCABDL : ℝ) * r + cAddBDL`. This theorem is a radius-monotonicity corollary derived
    from `WeldedHierarchy.bdlWeldedCode_inf_cone_acyclicity` via `ballMZ_mono` and `ballMX_mono`
    (rather than transferring block strong deformation retractions via the HPL). -/
theorem bdlWeldedStep_blockSDR_transfer (k : ℕ) (x0 : Point3D) (r : ℝ)
    (hr : 0 ≤ r) (hr_max : r ≤ (bdlLinearTQORadius k : ℝ)) :
    (∀ z1 : BDLWeldedQubit k → ZMod 2,
      (∀ q : BDLWeldedQubit k, z1 q ≠ 0 → q ∈ ballQ (bdlWeldedCode k) x0 r) →
      syndrome (bdlWeldedCode k) z1 = 0 →
      ∃ c2 : BDLWeldedCheckZ k → ZMod 2,
        checkGen (bdlWeldedCode k) c2 = z1 ∧
        ∀ mZ : BDLWeldedCheckZ k, c2 mZ ≠ 0 →
          mZ ∈ ballMZ (bdlWeldedCode k) x0 ((collarConstRCABDL : ℝ) * r + cAddBDL)) ∧
    (∀ b1 : BDLWeldedQubit k → ZMod 2,
      (∀ q : BDLWeldedQubit k, b1 q ≠ 0 → q ∈ ballQ (bdlWeldedCode k) x0 r) →
      syndrome (dualCode (bdlWeldedCode k)) b1 = 0 →
      ∃ d2 : BDLWeldedCheckX k → ZMod 2,
        checkGen (dualCode (bdlWeldedCode k)) d2 = b1 ∧
        ∀ mX : BDLWeldedCheckX k, d2 mX ≠ 0 →
          mX ∈ ballMX (bdlWeldedCode k) x0 ((collarConstRCABDL : ℝ) * r + cAddBDL)) := by
  have hr_pow : r ≤ (bdlLambda : ℝ) ^ (2 * k) + 2 := by
    have := bdlLinearTQORadius_le_pow k; linarith
  have h_cone := WeldedHierarchy.bdlWeldedCode_inf_cone_acyclicity k x0 hr hr_pow
  have h_rad : (WeldedHierarchy.bdlRandomLinearConstant / 11) * (2 * r + 1) +
      WeldedHierarchy.bdlBaseFillingRadius ≤ (collarConstRCABDL : ℝ) * r + cAddBDL := by
    have hlam : (1 : ℝ) ≤ (bdlLambda : ℝ) := by
      have := WeldedHierarchy.bdlLambda_ge_10000; linarith
    have h_base_pos : 0 ≤ WeldedHierarchy.bdlBaseFillingRadius := by
      dsimp [WeldedHierarchy.bdlBaseFillingRadius]; positivity
    have h_lin_ge : WeldedHierarchy.bdlBaseFillingRadius ≤ WeldedHierarchy.bdlRandomLinearConstant := by
      dsimp [WeldedHierarchy.bdlRandomLinearConstant]; nlinarith
    have h_C : (collarConstRCABDL : ℝ) = 2 * WeldedHierarchy.bdlRandomLinearConstant + 20 := by
      dsimp [collarConstRCABDL, WeldedHierarchy.bdlRandomLinearConstant, WeldedHierarchy.bdlBaseFillingRadius]
      push_cast; ring
    have h_add : cAddBDL = (collarConstRCABDL : ℝ) := rfl
    have h_C_r : 2 * (WeldedHierarchy.bdlRandomLinearConstant * r) ≤ (collarConstRCABDL : ℝ) * r := by
      rw [h_C]; nlinarith
    have h_mul_pos : 0 ≤ WeldedHierarchy.bdlRandomLinearConstant * r :=
      mul_nonneg (by linarith) hr
    linarith
  refine ⟨?_, ?_⟩
  · intro z1 h_supp h_syn
    obtain ⟨c2, hc2_gen, hc2_supp⟩ := h_cone.1 z1 h_syn h_supp
    exact ⟨c2, hc2_gen, fun mZ hmZ => ballMZ_mono (bdlWeldedCode k) x0 h_rad (hc2_supp mZ hmZ)⟩
  · intro b1 h_supp h_syn
    obtain ⟨d2, hd2_gen, hd2_supp⟩ := h_cone.2 b1 h_syn h_supp
    exact ⟨d2, hd2_gen, fun mX hmX => ballMX_mono (bdlWeldedCode k) x0 h_rad (hd2_supp mX hmX)⟩
