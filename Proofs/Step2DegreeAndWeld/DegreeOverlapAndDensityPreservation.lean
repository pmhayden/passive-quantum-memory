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

import Proofs.Step2DegreeAndWeld.CylinderCheckOverlapShellAndOuter

/-!
# Inductive Preservation of Check-Degree Overlap and Unit-Ball Vertex Density

Completes the uniform `X`/`Z`-check shared-support bound of at most 2 across all check sectors (`card_filter_bdlStepX_overlap_le_two`) and proves inductive preservation of `HasBoundedCheckDegreeOverlap` (`bdlCylinderStepX_preserves_bounded_check_degree_overlap`, `hasBoundedCheckDegreeOverlap_bdlIterated`). Combines `bdl_step1_lll_perturbation_exists` with Step-2 cylinder replacement density bounds to establish `HasUnitBallDensityT` across all welded hierarchy levels (`hasUnitBallDensityT_bdlIterated`, `bdl_random_lll_unit_ball_density`).

## References

* Part I, Section 2.2 (`subsec:step1-lll`), Proposition 2.4 (`prop:step1-lll`)
* Part I, Section 2.3 (`subsec:step2-mapping-cone`), Definition 2.5 (`def:three-layer-mapping-cone`), Proposition 2.6 (`prop:mapping-cone-invariants`)
-/

noncomputable section
open scoped Classical BigOperators
namespace WeldedHierarchy

/-! ## 1. Complete Shared-Check Overlap Bound (≤ 2) Across All Z-Check Sectors -/

set_option maxHeartbeats 800000 in
/-- **Cylinder Shared-Check Overlap Bound (Part I, Section 2.3 (`subsec:step2-mapping-cone`), Proposition 2.6 (`prop:mapping-cone-invariants`); Balasubramanian–Davydova–Lin (2026), Lemma 3.11)**:
    For any $X$-check $m_X \in \mathrm{BDLStepXMX}(pcode, M)$ and any $Z$-check
    $m_Z \in \mathrm{BDLStepXMZ}(pcode, M)$, at most $2$ qubits lie in the support of both checks. -/
lemma card_filter_bdlStepX_overlap_le_two {Q M_Z M_X : Type}
    [Fintype Q] [DecidableEq Q] [Fintype M_Z] [DecidableEq M_Z] [Fintype M_X] [DecidableEq M_X]
    (pcode : CSSCode3D Q M_Z M_X) (M : ℕ)
    (hov : ∀ (x : M_X) (z : M_Z),
      (Finset.univ.filter (fun q : Q => pcode.checkX x q ≠ 0 ∧ pcode.checkZ z q ≠ 0)).card ≤ 2)
    (mX : BDLStepXMX pcode M) (mZ : BDLStepXMZ pcode M) :
    (Finset.univ.filter (fun q1 : BDLStepXQ pcode M =>
      bdlStepXCheckX pcode M mX q1 ≠ 0 ∧ bdlStepXCheckZ pcode M mZ q1 ≠ 0)).card ≤ 2 := by
  rw [card_filter_sum_eq']
  rcases mZ with ⟨⟨seg, b⟩ | ⟨s, k, v⟩⟩ | ⟨mZQ | mZZ⟩
  · -- Step 1: Dispatch interior shell-segment Z-checks to card_filter_bdlStepX_overlap_seg_le_two.
    have h_seg := card_filter_bdlStepX_overlap_seg_le_two pcode M hov mX seg b
    rw [card_filter_sum_eq'] at h_seg
    exact h_seg
  · -- Step 2: Dispatch outer boundary Z-checks to card_filter_bdlStepX_overlap_outer_le_two.
    have h_out := card_filter_bdlStepX_overlap_outer_le_two pcode M mX s k v
    rw [card_filter_sum_eq'] at h_out
    exact h_out
  · -- Step 3: Bound overlap for subdivided Z-arm and vertical Z-checks (mZ = Sum.inr (Sum.inl mZQ)).
    have h_cx1 : (Finset.univ.filter (fun qX : BDLCX1 pcode M =>
        bdlStepXCheckX pcode M mX (Sum.inl qX) ≠ 0 ∧
        bdlStepXCheckZ pcode M (Sum.inr (Sum.inl mZQ)) (Sum.inl qX) ≠ 0)).card ≤ 1 := by
      apply card_filter_le_one_of_unique
      intro qX1 ⟨hX1, hZ1⟩ qX2 ⟨hX2, hZ2⟩
      rcases mX with ⟨x0, b0⟩ | ⟨sv0, b0⟩
      · rcases qX1 with _ | ⟨_ | _⟩ <;> [(rcases mZQ with _ | _ <;> exact False.elim (hZ1 rfl)); exact False.elim (hX1 rfl); exact False.elim (hX1 rfl)]
      · rcases mZQ with ⟨eZ, k, bZ⟩ | ⟨eZ, v⟩
        · rcases qX1 with _ | ⟨⟨seg1, b1⟩ | _⟩ <;> [exact False.elim (hZ1 rfl); skip; exact False.elim (hZ1 rfl)]
          rcases qX2 with _ | ⟨⟨seg2, b2⟩ | _⟩ <;> [exact False.elim (hZ2 rfl); skip; exact False.elim (hZ2 rfl)]
          dsimp [bdlStepXCheckZ, bdlGXQ1] at hZ1 hZ2
          split_ifs at hZ1 with hc1 <;> [skip; exact False.elim (hZ1 rfl)]
          split_ifs at hZ2 with hc2 <;> [skip; exact False.elim (hZ2 rfl)]
          have hx1 : seg1.val.1.val.1 = sv0.val.1.val.1 := by
            unfold bdlStepXCheckX bdlDeltaX0 at hX1; dsimp only at hX1
            rcases add_ite_one_ne_zero_imp hX1 with h | h <;>
              (injection h with h; injection h with hsv _;
               exact (congr_arg (fun s : ShellVertex pcode M => s.val.1.val.1) hsv).symm)
          have hx2 : seg2.val.1.val.1 = sv0.val.1.val.1 := by
            unfold bdlStepXCheckX bdlDeltaX0 at hX2; dsimp only at hX2
            rcases add_ite_one_ne_zero_imp hX2 with h | h <;>
              (injection h with h; injection h with hsv _;
               exact (congr_arg (fun s : ShellVertex pcode M => s.val.1.val.1) hsv).symm)
          have hs : seg1.val.1 = seg2.val.1 := Subtype.ext (Prod.ext (hx1.trans hx2.symm) (hc1.2.1.trans hc2.2.1.symm))
          have hseg : seg1 = seg2 := Subtype.ext (Prod.ext hs (Prod.ext (hc1.1.trans hc2.1.symm) (hc1.2.2.1.trans hc2.2.2.1.symm)))
          exact congr_arg (fun p => Sum.inr (Sum.inl p)) (Prod.ext hseg (hc1.2.2.2.trans hc2.2.2.2.symm))
        · rcases qX1 with _ | ⟨_ | ⟨xv1, v1⟩⟩ <;> [exact False.elim (hZ1 rfl); exact False.elim (hZ1 rfl); skip]
          rcases qX2 with _ | ⟨_ | ⟨xv2, v2⟩⟩ <;> [exact False.elim (hZ2 rfl); exact False.elim (hZ2 rfl); skip]
          dsimp [bdlStepXCheckZ, bdlGXQ1] at hZ1 hZ2
          split_ifs at hZ1 with hc1 <;> [skip; exact False.elim (hZ1 rfl)]
          split_ifs at hZ2 with hc2 <;> [skip; exact False.elim (hZ2 rfl)]
          have h_eq1 : xv1 = sv0.val.1 := by
            unfold bdlStepXCheckX bdlDeltaX0 at hX1; dsimp only at hX1
            rcases add_ite_one_ne_zero_imp hX1 with h | h <;>
              (injection h with h; injection h with hsv _;
               exact (congr_arg (fun s : ShellVertex pcode M => s.val.1) hsv).symm)
          have h_eq2 : xv2 = sv0.val.1 := by
            unfold bdlStepXCheckX bdlDeltaX0 at hX2; dsimp only at hX2
            rcases add_ite_one_ne_zero_imp hX2 with h | h <;>
              (injection h with h; injection h with hsv _;
               exact (congr_arg (fun s : ShellVertex pcode M => s.val.1) hsv).symm)
          exact congr_arg (fun xv => Sum.inr (Sum.inr xv)) (Prod.ext (h_eq1.trans h_eq2.symm) (hc1.2.trans hc2.2.symm))
    have h_cq1 : (Finset.univ.filter (fun qQ : BDLCQ1 pcode M =>
        bdlStepXCheckX pcode M mX (Sum.inr qQ) ≠ 0 ∧
        bdlStepXCheckZ pcode M (Sum.inr (Sum.inl mZQ)) (Sum.inr qQ) ≠ 0)).card ≤ 1 := by
      apply card_filter_le_one_of_unique
      intro qQ1 ⟨hX1, hZ1⟩ qQ2 ⟨hX2, hZ2⟩
      rcases mX with ⟨x0, b0⟩ | ⟨sv0, b0⟩
      · exact False.elim (hX1 rfl)
      · dsimp [bdlStepXCheckX, bdlGXQ0] at hX1 hX2
        split_ifs at hX1 with hc1 <;> [skip; exact False.elim (hX1 rfl)]
        split_ifs at hX2 with hc2 <;> [skip; exact False.elim (hX2 rfl)]
        rcases mZQ with ⟨eZ, k, bZ⟩ | ⟨eZ, v⟩
        · unfold bdlStepXCheckZ bdlDeltaQ1 at hZ1 hZ2; dsimp only at hZ1 hZ2
          rcases add_ite_one_ne_zero_imp hZ1 with h1 | h1 <;> rcases add_ite_one_ne_zero_imp hZ2 with h2 | h2
          · exact h1.trans h2.symm
          · have hp1 : projXq0ToBoundaryX0 pcode M qQ1.1 = bxStart pcode M eZ k :=
              congr_arg (projXq0ToBoundaryX0 pcode M) (congr_arg Prod.fst h1)
            have hp2 : projXq0ToBoundaryX0 pcode M qQ2.1 = bxEnd pcode M eZ k :=
              congr_arg (projXq0ToBoundaryX0 pcode M) (congr_arg Prod.fst h2)
            exact False.elim (bxStart_ne_bxEnd pcode M eZ k (hp1.symm.trans (hc1.2.1.symm.trans (hc2.2.1.trans hp2))))
          · have hp1 : projXq0ToBoundaryX0 pcode M qQ1.1 = bxEnd pcode M eZ k :=
              congr_arg (projXq0ToBoundaryX0 pcode M) (congr_arg Prod.fst h1)
            have hp2 : projXq0ToBoundaryX0 pcode M qQ2.1 = bxStart pcode M eZ k :=
              congr_arg (projXq0ToBoundaryX0 pcode M) (congr_arg Prod.fst h2)
            exact False.elim (bxStart_ne_bxEnd pcode M eZ k (hp2.symm.trans (hc2.2.1.symm.trans (hc1.2.1.trans hp1))))
          · exact h1.trans h2.symm
        · unfold bdlStepXCheckZ bdlDeltaQ1 at hZ1 hZ2; dsimp only at hZ1 hZ2
          have hv1 : qQ1.1 = Sum.inr (Sum.inr eZ) := by
            rcases add_ite_one_ne_zero_imp hZ1 with h | h <;> exact congr_arg Prod.fst h
          have hv2 : qQ2.1 = Sum.inr (Sum.inr eZ) := by
            rcases add_ite_one_ne_zero_imp hZ2 with h | h <;> exact congr_arg Prod.fst h
          exact Prod.ext (hv1.trans hv2.symm) (hc1.2.2.symm.trans hc2.2.2)
    omega
  · -- Step 4: Bound overlap for coarse Z-checks (mZ = Sum.inr (Sum.inr mZZ)).
    have h_cx1 : (Finset.univ.filter (fun qX : BDLCX1 pcode M =>
        bdlStepXCheckX pcode M mX (Sum.inl qX) ≠ 0 ∧
        bdlStepXCheckZ pcode M (Sum.inr (Sum.inr mZZ)) (Sum.inl qX) ≠ 0)).card = 0 :=
      card_filter_eq_zero_of_imp_false _ (fun _ h => h.2 rfl)
    rcases mX with ⟨x0, b0⟩ | ⟨sv0, b0⟩
    · have h_cq1 : (Finset.univ.filter (fun qQ : BDLCQ1 pcode M =>
          bdlStepXCheckX pcode M (Sum.inl (x0, b0)) (Sum.inr qQ) ≠ 0 ∧
          bdlStepXCheckZ pcode M (Sum.inr (Sum.inr mZZ)) (Sum.inr qQ) ≠ 0)).card = 0 :=
        card_filter_eq_zero_of_imp_false _ (fun _ h => h.1 rfl)
      omega
    · by_cases hz0 : sv0.val.1.val.2 = Sum.inr (Sum.inr mZZ.1)
      · have h_cq1 : (Finset.univ.filter (fun qQ : BDLCQ1 pcode M =>
            bdlStepXCheckX pcode M (Sum.inr (sv0, b0)) (Sum.inr qQ) ≠ 0 ∧
            bdlStepXCheckZ pcode M (Sum.inr (Sum.inr mZZ)) (Sum.inr qQ) ≠ 0)).card ≤ 2 := by
          refine (card_filter_le_of_injOn_filter _
            (fun qQ : BDLCQ1 pcode M => bdlGXQ0 pcode M (Sum.inr (sv0, b0)) qQ ≠ 0)
            id (fun _ h => h.1) (fun _ _ _ _ h => h)).trans
            (card_filter_bdlGXQ0_le_two_of_inr_inr pcode M sv0 b0 mZZ.1 hov hz0)
        omega
      · have h_cq1 : (Finset.univ.filter (fun qQ : BDLCQ1 pcode M =>
            bdlStepXCheckX pcode M (Sum.inr (sv0, b0)) (Sum.inr qQ) ≠ 0 ∧
            bdlStepXCheckZ pcode M (Sum.inr (Sum.inr mZZ)) (Sum.inr qQ) ≠ 0)).card = 0 := by
          apply card_filter_eq_zero_of_imp_false
          intro ⟨v0, bQ⟩ ⟨hX, hZ⟩
          dsimp [bdlStepXCheckX, bdlGXQ0] at hX
          split_ifs at hX with hcX <;> [skip; exact hX rfl]
          rcases v0 with _ | ⟨_ | eZ⟩ <;> [exact hZ rfl; exact hZ rfl; skip]
          dsimp [bdlStepXCheckZ, bdlGQZ1] at hZ
          split_ifs at hZ with hcZ <;> [skip; exact hZ rfl]
          exact hz0 (hcX.2.1.trans (congr_arg (fun z => Sum.inr (Sum.inr z)) hcZ.1))
        omega

/-! ## 2. Preservation of Bounded Check Degree & Overlap Across the Hierarchy -/

/-- **Coupled Cylinder Replacement Degree & Overlap Preservation Theorem (`bdlCylinderStepX_preserves_bounded_check_degree_overlap`; Part I, Section 2.3 (`subsec:step2-mapping-cone`), Proposition 2.6 (`prop:mapping-cone-invariants`); Balasubramanian–Davydova–Lin (2026), Lemma 3.11):** -/
theorem bdlCylinderStepX_preserves_bounded_check_degree_overlap {Q M_Z M_X : Type}
    [Fintype Q] [DecidableEq Q] [Fintype M_Z] [DecidableEq M_Z] [Fintype M_X] [DecidableEq M_X]
    (pcode : CSSCode3D Q M_Z M_X) (M : ℕ)
    (h : HasBoundedCheckDegreeOverlap ⟨Q, M_Z, M_X, pcode, fun _ => 0⟩) :
    HasBoundedCheckDegreeOverlap ⟨BDLStepXQ pcode M, BDLStepXMZ pcode M, BDLStepXMX pcode M, bdlCylinderStepX pcode M, fun _ => 0⟩ := by
  rcases h with ⟨⟨hdX, hdZ, hdQX, hdQZ⟩, hov⟩
  refine ⟨⟨?_, ?_, ?_, ?_⟩, ?_⟩
  · intro mX
    exact card_filter_bdlStepXCheckX_q1_le pcode M hdX hdQZ hov mX
  · intro mZ
    exact card_filter_bdlStepXCheckZ_q1_le pcode M hdZ hdQX hov mZ
  · intro q1
    exact card_filter_bdlStepXCheckX_mX_le pcode M hdQX q1
  · intro q1
    exact card_filter_bdlStepXCheckZ_mZ_le pcode M hdQZ hov q1
  · intro mX mZ
    exact card_filter_bdlStepX_overlap_le_two pcode M hov mX mZ

/-- Proves that `bdlRandomStepX` preserves `HasBoundedCheckDegreeOverlap`. -/
lemma bdlRandomStepX_preserves_bounded_check_degree_overlap (B : BundledCSSCode3D)
    (h : HasBoundedCheckDegreeOverlap B) :
    HasBoundedCheckDegreeOverlap (bdlRandomStepX B) :=
  bdlCylinderStepX_preserves_bounded_check_degree_overlap
    (bdlPerturbStep B.code bdlLambda (bdlLLLPerturbation B).1 (bdlLLLPerturbation B).2.1 (bdlLLLPerturbation B).2.2)
    bdlSubdivPred h

/-- Proves that `bdlRandomStepZ` preserves `HasBoundedCheckDegreeOverlap` via CSS duality. -/
lemma bdlRandomStepZ_preserves_bounded_check_degree_overlap (B : BundledCSSCode3D)
    (h : HasBoundedCheckDegreeOverlap B) :
    HasBoundedCheckDegreeOverlap (bdlRandomStepZ B) := by
  unfold bdlRandomStepZ
  exact dualBundled_preserves_bounded_check_degree_overlap _
    (bdlRandomStepX_preserves_bounded_check_degree_overlap (dualBundled B)
      (dualBundled_preserves_bounded_check_degree_overlap B h))

/-- Proves by induction on $k$ that `(bdlRandomStepZ ∘ bdlRandomStepX)^[k] bdlSurfaceSeedBundled`
    satisfies `HasBoundedCheckDegreeOverlap`. -/
lemma hasBoundedCheckDegreeOverlap_bdlIterated (k : ℕ) :
    HasBoundedCheckDegreeOverlap ((bdlRandomStepZ ∘ bdlRandomStepX)^[k] bdlSurfaceSeedBundled) := by
  induction k with
  | zero => exact hasBoundedCheckDegreeOverlap_surfaceSeed
  | succ k ih =>
    rw [Function.iterate_succ']
    dsimp only [Function.comp_apply]
    exact bdlRandomStepZ_preserves_bounded_check_degree_overlap _
      (bdlRandomStepX_preserves_bounded_check_degree_overlap _ ih)

/-! ## 3. Step-1 LLL Perturbation Existence, Unit-Ball Density & 3D Geometric Locality -/

/-- **Step 1 Lovász Local Lemma Spherical-Cap Perturbation Existence (`bdl_step1_lll_perturbation_exists`; Part I, Section 2.2 (`subsec:step1-lll`), Proposition 2.4 (`prop:step1-lll`); Balasubramanian–Davydova–Lin (2026), Lemma 3.3, Claims 3.4 & 3.5):** -/
lemma bdl_step1_lll_perturbation_exists (B : BundledCSSCode3D)
    (h_deg : HasBoundedSimplexDegreeD B 32)
    (h8 : HasInteractionRange8 B) (h_dens : HasUnitBallDensityT B) :
    ∃ c, ValidLLLSphericalCapPerturbation B c := by
  obtain ⟨tQ, tZ, tX, h_mult⟩ := bdl_step1_lll_unit_ball_multiplicity B h_deg h8 h_dens
  refine ⟨(fun q => rationalCap0 (tQ q), fun z => rationalCap1 (tZ z), fun x => rationalCap2 (tX x)), ?_⟩
  refine ⟨fun q => rationalCap0_distSq3D_origin (tQ q),
          fun z => rationalCap1_distSq3D_origin (tZ z),
          fun x => rationalCap2_distSq3D_origin (tX x),
          rationalCap_edgeZ_bounds B h8 tQ tZ tX,
          rationalCap_edgeX_bounds B h8 tQ tZ tX,
          rationalCap_simplex_width_bounds B h8 tQ tZ tX,
          h_mult⟩

/-- Combines `bdl_step1_lll_perturbation_exists` and `bdlReplaceStepX_unit_ball_density_of_valid_lll`
    to show that `bdlRandomStepX` preserves `HasUnitBallDensityT`. -/
lemma bdlRandomStepX_preserves_unit_ball_density (B : BundledCSSCode3D)
    (h_deg : HasBoundedSimplexDegreeD B 32)
    (h8 : HasInteractionRange8 B) (hq : HasNoIsolatedQ B.code) (h_dens : HasUnitBallDensityT B) :
    HasUnitBallDensityT (bdlRandomStepX B) := by
  intro x0
  have h_valid : ValidLLLSphericalCapPerturbation B (bdlLLLPerturbation B) :=
    bdlLLLPerturbation_spec_of_exists B (bdl_step1_lll_perturbation_exists B h_deg h8 h_dens)
  exact bdlReplaceStepX_unit_ball_density_of_valid_lll B hq (bdlLLLPerturbation B) h_valid x0

/-- Proves that `bdlRandomStepZ` preserves `HasUnitBallDensityT` via CSS duality. -/
lemma bdlRandomStepZ_preserves_unit_ball_density (B : BundledCSSCode3D)
    (h_deg : HasBoundedSimplexDegreeD B 32)
    (h8 : HasInteractionRange8 B) (hq : HasNoIsolatedQ B.code) (h_dens : HasUnitBallDensityT B) :
    HasUnitBallDensityT (bdlRandomStepZ B) := by
  unfold bdlRandomStepZ
  apply dualBundled_preserves_unit_ball_density
  apply bdlRandomStepX_preserves_unit_ball_density
  · exact dualBundled_preserves_bounded_simplex_degreeD B h_deg
  · exact dualBundled_preserves_interaction_range8 B h8
  · exact hasNoIsolatedQ_dualCode B.code hq
  · exact dualBundled_preserves_unit_ball_density B h_dens

/-- Proves by induction on $k$ that `(bdlRandomStepZ ∘ bdlRandomStepX)^[k] bdlSurfaceSeedBundled`
    satisfies `HasUnitBallDensityT` ($t = 8325$). -/
lemma hasUnitBallDensityT_bdlIterated (k : ℕ) :
    HasUnitBallDensityT ((bdlRandomStepZ ∘ bdlRandomStepX)^[k] bdlSurfaceSeedBundled) := by
  induction k with
  | zero => exact hasUnitBallDensityT_surfaceSeed
  | succ k ih =>
    rw [Function.iterate_succ']
    dsimp only [Function.comp_apply]
    let Bk := (bdlRandomStepZ ∘ bdlRandomStepX)^[k] bdlSurfaceSeedBundled
    have h_ov_Bk : HasBoundedCheckDegreeOverlap Bk :=
      hasBoundedCheckDegreeOverlap_bdlIterated k
    have h_deg_Bk : HasBoundedSimplexDegreeD Bk 32 :=
      hasBoundedSimplexDegreeD_32_of_hasBoundedCheckDegreeOverlap Bk h_ov_Bk
    have h_deg_stepX : HasBoundedSimplexDegreeD (bdlRandomStepX Bk) 32 :=
      hasBoundedSimplexDegreeD_32_of_hasBoundedCheckDegreeOverlap (bdlRandomStepX Bk)
        (bdlRandomStepX_preserves_bounded_check_degree_overlap Bk h_ov_Bk)
    have h8_Bk : HasInteractionRange8 Bk :=
      hasInteractionRange8_bdlIterated k bdlSurfaceSeedBundled hasInteractionRange8_surfaceSeed
    have hq_Bk : HasNoIsolatedQ Bk.code := hasNoIsolatedQ_iterate_stepZX k
    have h_stepX : HasUnitBallDensityT (bdlRandomStepX Bk) :=
      bdlRandomStepX_preserves_unit_ball_density Bk h_deg_Bk h8_Bk hq_Bk ih
    exact bdlRandomStepZ_preserves_unit_ball_density (bdlRandomStepX Bk)
      h_deg_stepX
      (bdlRandomStepX_preserves_interaction_range8 Bk h8_Bk)
      (hasNoIsolatedQ_bdlRandomStepX Bk hq_Bk)
      h_stepX

/-- **Unit-Ball Vertex Multiplicity Bound on `bdlRandomCode k` (`bdl_random_lll_unit_ball_density`):**
    Proved by combining the Step 1 LLL perturbation existence (`bdl_step1_lll_perturbation_exists`; Part I, Section 2.2 (`subsec:step1-lll`), Proposition 2.4 (`prop:step1-lll`); Balasubramanian–Davydova–Lin (2026), Lemma 3.3)
    with the Step 2 `(t, 1)`-embedding density theorem (`bdlReplaceStepX_unit_ball_density_of_valid_lll`; Part I, Section 2.3 (`subsec:step2-mapping-cone`), Proposition 2.6 (`prop:mapping-cone-invariants`); Balasubramanian–Davydova–Lin (2026), Lemma 3.12). -/
lemma bdl_random_lll_unit_ball_density (k : ℕ) (x0 : Point3D) :
    ((Finset.univ.filter (fun q : BDLRandomQubit k => (bdlRandomCode k).posQ q ∈ ball3D x0 1)).card : ℝ) ≤ bdlDensityT ∧
    ((Finset.univ.filter (fun m : BDLRandomCheckZ k => (bdlRandomCode k).posZ m ∈ ball3D x0 1)).card : ℝ) ≤ bdlDensityT ∧
    ((Finset.univ.filter (fun m : BDLRandomCheckX k => (bdlRandomCode k).posX m ∈ ball3D x0 1)).card : ℝ) ≤ bdlDensityT :=
  hasUnitBallDensityT_bdlIterated (k + 1) x0

end WeldedHierarchy
