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

import Proofs.Step1LLLDensity.BadEventDependencyGraph

/-!
# Main Step-1 LLL Synthesis for Vertex Separation and Unit-Ball Simplex Multiplicity

Synthesizes the six-stage bad-event dependency graph bounds, evaluation-assignment conditional LLL reduction, and three-stage dominant Cramer cascade to prove `bdl_step1_lll_unit_ball_multiplicity`. Establishes that every bundled 3D CSS code satisfying `HasBoundedSimplexDegreeD B 32`, `HasInteractionRange8 B`, and `HasUnitBallDensityT B` admits a spherical-cap perturbation achieving pairwise vertex separation and bounded unit-ball 2-simplex multiplicity.

## References

* Part I, Section 2.2 (`subsec:step1-lll`), Proposition 2.4 (`prop:step1-lll`), Equation (2) (`eq:archimedes-slab-bound`)
-/

noncomputable section
open scoped Classical BigOperators
namespace WeldedHierarchy

/-! ## 1. Application of Conditional LLL and Unit-Ball Vertex Separation -/

set_option maxHeartbeats 800000 in
/-- **Step 1 Lovász Local Lemma Unit-Ball Multiplicity Bound (`bdl_step1_lll_unit_ball_multiplicity`; Part I, Section 2.2 (`subsec:step1-lll`), Proposition 2.4 (`prop:step1-lll`); Balasubramanian–Davydova–Lin (2026), Lemma 3.3):** -/
lemma bdl_step1_lll_unit_ball_multiplicity (B : BundledCSSCode3D)
    (h_deg : HasBoundedSimplexDegreeD B 32)
    (h8 : HasInteractionRange8 B) (h_dens : HasUnitBallDensityT B) :
    ∃ (tQ : B.Q → ℝ) (tZ : B.M_Z → ℝ) (tX : B.M_X → ℝ),
      let pcode := bdlPerturbStep B.code bdlLambda
        (fun q => rationalCap0 (tQ q)) (fun z => rationalCap1 (tZ z)) (fun x => rationalCap2 (tX x))
      ∀ x0 : Point3D,
        ((Finset.univ.filter (fun s : ActiveSimplex2 B.code =>
          (simplex2D3D (pcode.posX s.val.1) (pcode.posQ s.val.2.1) (pcode.posZ s.val.2.2) ∩
            ball3D x0 1).Nonempty)).card : ℝ) ≤ bdlDensityTPrime ∧
        ((Finset.univ.filter (fun q : B.Q => pcode.posQ q ∈ ball3D x0 1)).card : ℝ) ≤ bdlDensityTPrime ∧
        ((Finset.univ.filter (fun m : B.M_Z => pcode.posZ m ∈ ball3D x0 1)).card : ℝ) ≤ bdlDensityTPrime ∧
        ((Finset.univ.filter (fun m : B.M_X => pcode.posX m ∈ ball3D x0 1)).card : ℝ) ≤ bdlDensityTPrime := by
  -- Step 1: Establish initial algebraic and geometric reductions for `bdl_step1_lll_unit_ball_multiplicity`
  obtain ⟨ω, hω⟩ := exists_good_assignment_of_evalAssign_lll
    (lllSupport B) (lllCandV B) (LLLRawBad B)
    (lllCandV_subset_lllSupport B)
    (card_lllCandV_le B h_dens)
    (card_LLLRawBad_update_le_deg B (by norm_num : 1 ≤ 32) h_deg)
    (card_lllSupport_not_disjoint_le B h_deg h_dens)
    lll_numerical_condition_32_54
  let tQ := lllTQ B ω
  let tZ := lllTZ B ω
  let tX := lllTX B ω
  have htQ : ∀ q, 0 ≤ tQ q ∧ tQ q ≤ 1 / 1000 := fun q => lllGridParam_bounds (ω (Sum.inl q))
  have htZ : ∀ z, 0 ≤ tZ z ∧ tZ z ≤ 1 / 1000 := fun z => lllGridParam_bounds (ω (Sum.inr (Sum.inl z)))
  have htX : ∀ x, 0 ≤ tX x ∧ tX x ≤ 1 / 1000 := fun x => lllGridParam_bounds (ω (Sum.inr (Sum.inr x)))
  let pcode := lllPCode B ω
  have hQ_sep : ∀ q0 : B.Q, (Finset.univ.filter (fun q : B.Q => q ≠ q0 ∧ distSq3D (pcode.posQ q0) (pcode.posQ q) ≤ 4)).card ≤ 54 := by
    intro q0
    let t : LLLEvent B := Sum.inl (Sum.inl q0)
    have h_inj : ∀ v : LLLVertex B, (Finset.univ.filter (fun q : B.Q => (Sum.inl q : LLLVertex B) = v)).card ≤ 1 := by
      intro v; rw [Finset.card_le_one]; intro q1 h1 q2 h2
      exact Sum.inl.inj ((Finset.mem_filter.mp h1).2.trans (Finset.mem_filter.mp h2).2.symm)
    have h_le := card_filter_simplex_le_mul_deg_of_cand_filter_le
      (fun q : B.Q => (Sum.inl q : LLLVertex B)) h_inj
      ((lllCandV B t).filter (fun v => LLLRawBad B t v (evalAssign (lllSupport B t) (lllCandV B t) v ω)))
      (hω t)
      (Finset.univ.filter (fun q : B.Q => q ≠ q0 ∧ distSq3D (pcode.posQ q0) (pcode.posQ q) ≤ 4))
      (fun q hq => by
        rw [Finset.mem_filter] at hq
        rw [Finset.mem_filter]
        have h_box : InLocalBox (B.code.posQ q0) (B.code.posQ q) :=
          inLocalBox_of_perturbed_distSq_le_four (B.code.posQ q0) (B.code.posQ q) rationalCap0 (tQ q0) (tQ q)
            (rationalCap0_distSq3D_small (tQ q0) (tQ q) (htQ q0) (htQ q)) hq.2.2
        have h_mem_cand : (Sum.inl q : LLLVertex B) ∈ lllCandV B t := by
          dsimp [lllCandV, t, candQ]
          exact Finset.mem_erase.mpr ⟨fun h => hq.2.1 (Sum.inl.inj h),
            Finset.mem_map.mpr ⟨q, Finset.mem_filter.mpr ⟨Finset.mem_univ q, h_box⟩, rfl⟩⟩
        refine ⟨h_mem_cand, hq.2.1, ?_⟩
        have hq0_ev : (lllPCode B (evalAssign (lllSupport B t) (lllCandV B t) (Sum.inl q) ω)).posQ q0 = pcode.posQ q0 := by
          have h_ev0 : evalAssign (lllSupport B t) (lllCandV B t) (Sum.inl q) ω (Sum.inl q0) = ω (Sum.inl q0) :=
            evalAssign_apply_of_mem_sdiff _ _ _ _ (mem_sdiff_erase_self (mem_localBoxSupport_self B (Sum.inl q0)))
          dsimp [lllPCode, pcode, bdlPerturbStep, lllTQ]
          rw [h_ev0]
        have hq_ev : (lllPCode B (evalAssign (lllSupport B t) (lllCandV B t) (Sum.inl q) ω)).posQ q = pcode.posQ q := by
          dsimp [lllPCode, pcode, bdlPerturbStep, lllTQ]
          rw [evalAssign_apply_self]
        rw [hq0_ev, hq_ev]; exact hq.2.2)
    omega
  have hZ_sep : ∀ z0 : B.M_Z, (Finset.univ.filter (fun z : B.M_Z => z ≠ z0 ∧ distSq3D (pcode.posZ z0) (pcode.posZ z) ≤ 4)).card ≤ 54 := by
    intro z0
    let t : LLLEvent B := Sum.inl (Sum.inr (Sum.inl z0))
    have h_inj : ∀ v : LLLVertex B, (Finset.univ.filter (fun z : B.M_Z => (Sum.inr (Sum.inl z) : LLLVertex B) = v)).card ≤ 1 := by
      intro v; rw [Finset.card_le_one]; intro z1 h1 z2 h2
      exact Sum.inl.inj (Sum.inr.inj ((Finset.mem_filter.mp h1).2.trans (Finset.mem_filter.mp h2).2.symm))
    have h_le := card_filter_simplex_le_mul_deg_of_cand_filter_le
      (fun z : B.M_Z => (Sum.inr (Sum.inl z) : LLLVertex B)) h_inj
      ((lllCandV B t).filter (fun v => LLLRawBad B t v (evalAssign (lllSupport B t) (lllCandV B t) v ω)))
      (hω t)
      (Finset.univ.filter (fun z : B.M_Z => z ≠ z0 ∧ distSq3D (pcode.posZ z0) (pcode.posZ z) ≤ 4))
      (fun z hz => by
        rw [Finset.mem_filter] at hz
        rw [Finset.mem_filter]
        have h_box : InLocalBox (B.code.posZ z0) (B.code.posZ z) :=
          inLocalBox_of_perturbed_distSq_le_four (B.code.posZ z0) (B.code.posZ z) rationalCap1 (tZ z0) (tZ z)
            (rationalCap1_distSq3D_small (tZ z0) (tZ z) (htZ z0) (htZ z)) hz.2.2
        have h_mem_cand : (Sum.inr (Sum.inl z) : LLLVertex B) ∈ lllCandV B t := by
          dsimp [lllCandV, t, candZ]
          exact Finset.mem_erase.mpr ⟨fun h => hz.2.1 (Sum.inl.inj (Sum.inr.inj h)),
            Finset.mem_map.mpr ⟨z, Finset.mem_filter.mpr ⟨Finset.mem_univ z, h_box⟩, rfl⟩⟩
        refine ⟨h_mem_cand, hz.2.1, ?_⟩
        have hz0_ev : (lllPCode B (evalAssign (lllSupport B t) (lllCandV B t) (Sum.inr (Sum.inl z)) ω)).posZ z0 = pcode.posZ z0 := by
          have h_ev0 : evalAssign (lllSupport B t) (lllCandV B t) (Sum.inr (Sum.inl z)) ω (Sum.inr (Sum.inl z0)) = ω (Sum.inr (Sum.inl z0)) :=
            evalAssign_apply_of_mem_sdiff _ _ _ _ (mem_sdiff_erase_self (mem_localBoxSupport_self B (Sum.inr (Sum.inl z0))))
          dsimp [lllPCode, pcode, bdlPerturbStep, lllTZ]
          rw [h_ev0]
        have hz_ev : (lllPCode B (evalAssign (lllSupport B t) (lllCandV B t) (Sum.inr (Sum.inl z)) ω)).posZ z = pcode.posZ z := by
          dsimp [lllPCode, pcode, bdlPerturbStep, lllTZ]
          rw [evalAssign_apply_self]
        rw [hz0_ev, hz_ev]; exact hz.2.2)
    omega
  have hX_sep : ∀ x0 : B.M_X, (Finset.univ.filter (fun x : B.M_X => x ≠ x0 ∧ distSq3D (pcode.posX x0) (pcode.posX x) ≤ 4)).card ≤ 54 := by
    intro x0
    let t : LLLEvent B := Sum.inl (Sum.inr (Sum.inr x0))
    have h_inj : ∀ v : LLLVertex B, (Finset.univ.filter (fun x : B.M_X => (Sum.inr (Sum.inr x) : LLLVertex B) = v)).card ≤ 1 := by
      intro v; rw [Finset.card_le_one]; intro x1 h1 x2 h2
      exact Sum.inr.inj (Sum.inr.inj ((Finset.mem_filter.mp h1).2.trans (Finset.mem_filter.mp h2).2.symm))
    have h_le := card_filter_simplex_le_mul_deg_of_cand_filter_le
      (fun x : B.M_X => (Sum.inr (Sum.inr x) : LLLVertex B)) h_inj
      ((lllCandV B t).filter (fun v => LLLRawBad B t v (evalAssign (lllSupport B t) (lllCandV B t) v ω)))
      (hω t)
      (Finset.univ.filter (fun x : B.M_X => x ≠ x0 ∧ distSq3D (pcode.posX x0) (pcode.posX x) ≤ 4))
      (fun x hx => by
        rw [Finset.mem_filter] at hx
        rw [Finset.mem_filter]
        have h_box : InLocalBox (B.code.posX x0) (B.code.posX x) :=
          inLocalBox_of_perturbed_distSq_le_four (B.code.posX x0) (B.code.posX x) rationalCap2 (tX x0) (tX x)
            (rationalCap2_distSq3D_small (tX x0) (tX x) (htX x0) (htX x)) hx.2.2
        have h_mem_cand : (Sum.inr (Sum.inr x) : LLLVertex B) ∈ lllCandV B t := by
          dsimp [lllCandV, t, candX]
          exact Finset.mem_erase.mpr ⟨fun h => hx.2.1 (Sum.inr.inj (Sum.inr.inj h)),
            Finset.mem_map.mpr ⟨x, Finset.mem_filter.mpr ⟨Finset.mem_univ x, h_box⟩, rfl⟩⟩
        refine ⟨h_mem_cand, hx.2.1, ?_⟩
        have hx0_ev : (lllPCode B (evalAssign (lllSupport B t) (lllCandV B t) (Sum.inr (Sum.inr x)) ω)).posX x0 = pcode.posX x0 := by
          have h_ev0 : evalAssign (lllSupport B t) (lllCandV B t) (Sum.inr (Sum.inr x)) ω (Sum.inr (Sum.inr x0)) = ω (Sum.inr (Sum.inr x0)) :=
            evalAssign_apply_of_mem_sdiff _ _ _ _ (mem_sdiff_erase_self (mem_localBoxSupport_self B (Sum.inr (Sum.inr x0))))
          dsimp [lllPCode, pcode, bdlPerturbStep, lllTX]
          rw [h_ev0]
        have hx_ev : (lllPCode B (evalAssign (lllSupport B t) (lllCandV B t) (Sum.inr (Sum.inr x)) ω)).posX x = pcode.posX x := by
          dsimp [lllPCode, pcode, bdlPerturbStep, lllTX]
          rw [evalAssign_apply_self]
        rw [hx0_ev, hx_ev]; exact hx.2.2)
    omega
  refine ⟨tQ, tZ, tX, fun x0 => ⟨?_,
    card_filter_ball3D_one_le_of_bounded_close_neighbors pcode.posQ 54 (by norm_num) hQ_sep x0,
    card_filter_ball3D_one_le_of_bounded_close_neighbors pcode.posZ 54 (by norm_num) hZ_sep x0,
    card_filter_ball3D_one_le_of_bounded_close_neighbors pcode.posX 54 (by norm_num) hX_sep x0⟩⟩
  refine card_le_bdlDensityTPrime_of_three_stage_dominant_cramer_cascade
    B h8 32 54 108 162 (by norm_num) h_deg tQ tZ tX htQ htZ htX
    ((bdlLambda : ℝ) ^ 2)
    (SimplexInLocalBox B)
    (fun s1 s2 => (bdlLambda : ℝ) ^ 3 < |(cross3D (ptsNormal (lllSimplexPts B ω s1)) (ptsNormal (lllSimplexPts B ω s2))) 2|)
    ?_ ?_ ?_ x0
    (fun s1 s2 hs1 hs2 => simplex_inter_ball3D_implies_inLocalBox B h8 tQ tZ tX htQ htZ htX x0 s1 s2 hs1 hs2)
  · -- Stage 1 bound
    intro s1
    let t : LLLEvent B := Sum.inr (Sum.inl s1)
    have h_sub_cand : lllCandV B t ⊆ candX B (B.code.posQ s1.val.2.1) := Finset.erase_subset _ _
    have hs1_supp := lllSimplexPts_mem_localBoxSupport B s1 s1 (simplexInLocalBox_self B h8 s1)
    refine card_filter_simplex_le_mul_deg_of_cand_filter_le
      (fun u : ActiveSimplex2 B.code => (Sum.inr (Sum.inr u.val.1) : LLLVertex B))
      (card_activeSimplex_map_X_le_deg B h_deg)
      ((lllCandV B t).filter (fun v => LLLRawBad B t v (evalAssign (lllSupport B t) (lllCandV B t) v ω)))
      (hω t) _
      (fun u hu => ?_)
    rw [Finset.mem_filter] at hu
    rw [Finset.mem_filter]
    rcases hu.2 with ⟨h_disj, h_loc, h_not_good⟩
    have h_mem_cand : (Sum.inr (Sum.inr u.val.1) : LLLVertex B) ∈ lllCandV B t := by
      dsimp [lllCandV, t, candX]
      exact Finset.mem_erase.mpr ⟨fun h => h_disj.1 (Sum.inr.inj (Sum.inr.inj h)).symm,
        Finset.mem_map.mpr ⟨u.val.1, Finset.mem_filter.mpr ⟨Finset.mem_univ _, h_loc.1⟩, rfl⟩⟩
    refine ⟨h_mem_cand, u, rfl, ?_⟩
    have hs1_ev : lllSimplexPts B (evalAssign (lllSupport B t) (lllCandV B t) (Sum.inr (Sum.inr u.val.1)) ω) s1 =
        lllSimplexPts B ω s1 :=
      lllSimplexPts_evalAssign_fixed B _ ω s1
        ⟨hs1_supp.1, Finset.notMem_erase _ _⟩
        ⟨hs1_supp.2.1, fun h => not_mem_candX_inl B _ _ (h_sub_cand h)⟩
        ⟨hs1_supp.2.2, fun h => not_mem_candX_inr_inl B _ _ (h_sub_cand h)⟩
    have hu_ev : lllSimplexPts B (evalAssign (lllSupport B t) (lllCandV B t) (Sum.inr (Sum.inr u.val.1)) ω) u =
        lllSimplexPts B ω u :=
      lllSimplexPts_evalAssign_candX B s1 u h_sub_cand h_loc ω
    rw [hs1_ev, hu_ev]
    have h_N1 := perturbed_simplex_normal_bounds B h8 tQ tZ tX s1 (htQ _) (htZ _) (htX _)
    have h_eu := perturbed_simplex_edge_bounds B h8 tQ tZ tX u (htQ _) (htZ _) (htX _)
    exact ⟨h_disj, ⟨h_N1.1, h_N1.2.1, h_eu.1⟩, not_lt.mp h_not_good⟩
  · -- Stage 2 bound
    intro s1 s2 h_disj12 h_loc12 h_good1
    let Bad2A := Finset.univ.filter (fun u : ActiveSimplex2 B.code =>
      SimplexInLocalBox B s1 u ∧
      Stage2ABadPts (lllSimplexPts B ω s1) (lllSimplexPts B ω s2) (lllSimplexPts B ω u)
        (VertexDisjointSimplex2 s1.val u.val ∧ VertexDisjointSimplex2 s2.val u.val))
    let Bad2B := Finset.univ.filter (fun u : ActiveSimplex2 B.code =>
      SimplexInLocalBox B s1 u ∧
      Stage2BBadPts (lllSimplexPts B ω s1) (lllSimplexPts B ω s2) (lllSimplexPts B ω u)
        (VertexDisjointSimplex2 s1.val u.val ∧ VertexDisjointSimplex2 s2.val u.val))
    have hs1_supp := lllSimplexPts_mem_localBoxSupport B s1 s1 (simplexInLocalBox_self B h8 s1)
    have hs2_supp := lllSimplexPts_mem_localBoxSupport B s1 s2 h_loc12
    have h_card2A : Bad2A.card ≤ 54 * 32 := by
      let t : LLLEvent B := Sum.inr (Sum.inr (Sum.inl (Sum.inl (s1, s2))))
      have h_act : LLLEventActive B t := h_loc12
      have h_cand_eq : lllCandV B t = ((candX B (B.code.posQ s1.val.2.1)).erase (Sum.inr (Sum.inr s1.val.1))).erase (Sum.inr (Sum.inr s2.val.1)) := by
        dsimp [lllCandV, t]; rw [if_pos h_loc12]
      have h_supp_eq : lllSupport B t = localBoxSupport B (B.code.posQ s1.val.2.1) := by
        dsimp [lllSupport, t]; rw [if_pos h_act]; rfl
      have h_sub_cand : lllCandV B t ⊆ candX B (B.code.posQ s1.val.2.1) := by
        rw [h_cand_eq]; exact Finset.Subset.trans (Finset.erase_subset _ _) (Finset.erase_subset _ _)
      refine card_filter_simplex_le_mul_deg_of_cand_filter_le
        (fun u : ActiveSimplex2 B.code => (Sum.inr (Sum.inr u.val.1) : LLLVertex B))
        (card_activeSimplex_map_X_le_deg B h_deg)
        ((lllCandV B t).filter (fun v => LLLRawBad B t v (evalAssign (lllSupport B t) (lllCandV B t) v ω)))
        (hω t) Bad2A
        (fun u hu => ?_)
      rw [Finset.mem_filter] at hu
      rw [Finset.mem_filter]
      rcases hu.2 with ⟨hloc, hbad⟩
      have h_mem_cand : (Sum.inr (Sum.inr u.val.1) : LLLVertex B) ∈ lllCandV B t := by
        rw [h_cand_eq]
        exact Finset.mem_erase.mpr ⟨fun h => hbad.1.2.1 (Sum.inr.inj (Sum.inr.inj h)).symm,
          Finset.mem_erase.mpr ⟨fun h => hbad.1.1.1 (Sum.inr.inj (Sum.inr.inj h)).symm,
            Finset.mem_map.mpr ⟨u.val.1, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hloc.1⟩, rfl⟩⟩⟩
      refine ⟨h_mem_cand, u, rfl, ?_⟩
      have hs1_ev : lllSimplexPts B (evalAssign (lllSupport B t) (lllCandV B t) (Sum.inr (Sum.inr u.val.1)) ω) s1 =
          lllSimplexPts B ω s1 := by
        rw [h_supp_eq]
        exact lllSimplexPts_evalAssign_fixed B _ ω s1
          ⟨hs1_supp.1, by rw [h_cand_eq]; intro h; exact Finset.notMem_erase _ _ (Finset.mem_of_mem_erase h)⟩
          ⟨hs1_supp.2.1, fun h => not_mem_candX_inl B _ _ (h_sub_cand h)⟩
          ⟨hs1_supp.2.2, fun h => not_mem_candX_inr_inl B _ _ (h_sub_cand h)⟩
      have hs2_ev : lllSimplexPts B (evalAssign (lllSupport B t) (lllCandV B t) (Sum.inr (Sum.inr u.val.1)) ω) s2 =
          lllSimplexPts B ω s2 := by
        rw [h_supp_eq]
        exact lllSimplexPts_evalAssign_fixed B _ ω s2
          ⟨hs2_supp.1, by rw [h_cand_eq]; exact Finset.notMem_erase _ _⟩
          ⟨hs2_supp.2.1, fun h => not_mem_candX_inl B _ _ (h_sub_cand h)⟩
          ⟨hs2_supp.2.2, fun h => not_mem_candX_inr_inl B _ _ (h_sub_cand h)⟩
      have hu_ev : lllSimplexPts B (evalAssign (lllSupport B t) (lllCandV B t) (Sum.inr (Sum.inr u.val.1)) ω) u =
          lllSimplexPts B ω u := by
        rw [h_supp_eq]; exact lllSimplexPts_evalAssign_candX B s1 u h_sub_cand hloc ω
      rw [hs1_ev, hs2_ev, hu_ev]; exact hbad
    have h_card2B : Bad2B.card ≤ 54 * 32 := by
      let t : LLLEvent B := Sum.inr (Sum.inr (Sum.inl (Sum.inr (s1, s2))))
      have h_act : LLLEventActive B t := h_loc12
      have h_cand_eq : lllCandV B t = ((candQ B (B.code.posQ s1.val.2.1)).erase (Sum.inl s1.val.2.1)).erase (Sum.inl s2.val.2.1) := by
        dsimp [lllCandV, t]; rw [if_pos h_loc12]
      have h_supp_eq : lllSupport B t = localBoxSupport B (B.code.posQ s1.val.2.1) := by
        dsimp [lllSupport, t]; rw [if_pos h_act]; rfl
      -- Step 2: Complete the main case analysis and bound assembly for `bdl_step1_lll_unit_ball_multiplicity`
      have h_sub_cand : lllCandV B t ⊆ candQ B (B.code.posQ s1.val.2.1) := by
        rw [h_cand_eq]; exact Finset.Subset.trans (Finset.erase_subset _ _) (Finset.erase_subset _ _)
      refine card_filter_simplex_le_mul_deg_of_cand_filter_le
        (fun u : ActiveSimplex2 B.code => (Sum.inl u.val.2.1 : LLLVertex B))
        (card_activeSimplex_map_Q_le_deg B h_deg)
        ((lllCandV B t).filter (fun v => LLLRawBad B t v (evalAssign (lllSupport B t) (lllCandV B t) v ω)))
        (hω t) Bad2B
        (fun u hu => ?_)
      rw [Finset.mem_filter] at hu
      rw [Finset.mem_filter]
      rcases hu.2 with ⟨hloc, hbad⟩
      have h_mem_cand : (Sum.inl u.val.2.1 : LLLVertex B) ∈ lllCandV B t := by
        rw [h_cand_eq]
        exact Finset.mem_erase.mpr ⟨fun h => hbad.1.2.2.1 (Sum.inl.inj h).symm,
          Finset.mem_erase.mpr ⟨fun h => hbad.1.1.2.1 (Sum.inl.inj h).symm,
            Finset.mem_map.mpr ⟨u.val.2.1, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hloc.2.1⟩, rfl⟩⟩⟩
      refine ⟨h_mem_cand, u, rfl, ?_⟩
      have hs1_ev : lllSimplexPts B (evalAssign (lllSupport B t) (lllCandV B t) (Sum.inl u.val.2.1) ω) s1 =
          lllSimplexPts B ω s1 := by
        rw [h_supp_eq]
        exact lllSimplexPts_evalAssign_fixed B _ ω s1
          ⟨hs1_supp.1, fun h => not_mem_candQ_inr_inr B _ _ (h_sub_cand h)⟩
          ⟨hs1_supp.2.1, by rw [h_cand_eq]; intro h; exact Finset.notMem_erase _ _ (Finset.mem_of_mem_erase h)⟩
          ⟨hs1_supp.2.2, fun h => not_mem_candQ_inr_inl B _ _ (h_sub_cand h)⟩
      have hs2_ev : lllSimplexPts B (evalAssign (lllSupport B t) (lllCandV B t) (Sum.inl u.val.2.1) ω) s2 =
          lllSimplexPts B ω s2 := by
        rw [h_supp_eq]
        exact lllSimplexPts_evalAssign_fixed B _ ω s2
          ⟨hs2_supp.1, fun h => not_mem_candQ_inr_inr B _ _ (h_sub_cand h)⟩
          ⟨hs2_supp.2.1, by rw [h_cand_eq]; exact Finset.notMem_erase _ _⟩
          ⟨hs2_supp.2.2, fun h => not_mem_candQ_inr_inl B _ _ (h_sub_cand h)⟩
      have hu_ev : lllSimplexPts B (evalAssign (lllSupport B t) (lllCandV B t) (Sum.inl u.val.2.1) ω) u =
          lllSimplexPts B ω u := by
        rw [h_supp_eq]; exact lllSimplexPts_evalAssign_candQ B s1 u h_sub_cand hloc ω
      rw [hs1_ev, hs2_ev, hu_ev]; exact hbad
    refine le_trans (Finset.card_le_card (t := Bad2A ∪ Bad2B) (fun u hu => ?_))
      (le_trans (Finset.card_union_le Bad2A Bad2B) (by omega))
    rw [Finset.mem_filter] at hu
    rcases hu.2 with ⟨hd1, hd2, hloc, h_not_det⟩
    have h_dich := stage2_dominant_type_dichotomy B h8 tQ tZ tX htQ htZ htX s1 s2 u h_good1 h_not_det
    rcases h_dich with hA | hB
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨Finset.mem_univ u, hloc, ⟨hd1, hd2⟩, hA, not_lt.mp h_not_det⟩)
    · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨Finset.mem_univ u, hloc, ⟨hd1, hd2⟩, hB, not_lt.mp h_not_det⟩)
  · -- Stage 3 bound
    intro s1 s2 s3 hd12 hd13 hd23 hloc12 hloc13 _pcode _N hD4
    let Bad3A := Finset.univ.filter (fun u : ActiveSimplex2 B.code =>
      SimplexInLocalBox B s1 u ∧
      Stage3ABadPts (lllSimplexPts B ω s1) (lllSimplexPts B ω s2) (lllSimplexPts B ω s3) (lllSimplexPts B ω u)
        (VertexDisjointSimplex2 s1.val u.val ∧ VertexDisjointSimplex2 s2.val u.val ∧ VertexDisjointSimplex2 s3.val u.val))
    let Bad3B := Finset.univ.filter (fun u : ActiveSimplex2 B.code =>
      SimplexInLocalBox B s1 u ∧
      Stage3BBadPts (lllSimplexPts B ω s1) (lllSimplexPts B ω s2) (lllSimplexPts B ω s3) (lllSimplexPts B ω u)
        (VertexDisjointSimplex2 s1.val u.val ∧ VertexDisjointSimplex2 s2.val u.val ∧ VertexDisjointSimplex2 s3.val u.val))
    let Bad3C := Finset.univ.filter (fun u : ActiveSimplex2 B.code =>
      SimplexInLocalBox B s1 u ∧
      Stage3CBadPts (lllSimplexPts B ω s1) (lllSimplexPts B ω s2) (lllSimplexPts B ω s3) (lllSimplexPts B ω u)
        (VertexDisjointSimplex2 s1.val u.val ∧ VertexDisjointSimplex2 s2.val u.val ∧ VertexDisjointSimplex2 s3.val u.val))
    have hs1_supp := lllSimplexPts_mem_localBoxSupport B s1 s1 (simplexInLocalBox_self B h8 s1)
    have hs2_supp := lllSimplexPts_mem_localBoxSupport B s1 s2 hloc12
    have hs3_supp := lllSimplexPts_mem_localBoxSupport B s1 s3 hloc13
    have h_card3A : Bad3A.card ≤ 54 * 32 := by
      let t : LLLEvent B := Sum.inr (Sum.inr (Sum.inr (Sum.inl (s1, s2, s3))))
      have h_act : LLLEventActive B t := ⟨hloc12, hloc13⟩
      have h_cand_eq : lllCandV B t = (((candX B (B.code.posQ s1.val.2.1)).erase (Sum.inr (Sum.inr s1.val.1))).erase (Sum.inr (Sum.inr s2.val.1))).erase (Sum.inr (Sum.inr s3.val.1)) := by
        dsimp [lllCandV, t]; dsimp [LLLEventActive, t] at h_act; rw [if_pos h_act]
      have h_supp_eq : lllSupport B t = localBoxSupport B (B.code.posQ s1.val.2.1) := by
        dsimp [lllSupport, t]; rw [if_pos h_act]; rfl
      have h_sub_cand : lllCandV B t ⊆ candX B (B.code.posQ s1.val.2.1) := by
        rw [h_cand_eq]; exact Finset.Subset.trans (Finset.erase_subset _ _) (Finset.Subset.trans (Finset.erase_subset _ _) (Finset.erase_subset _ _))
      refine card_filter_simplex_le_mul_deg_of_cand_filter_le
        (fun u : ActiveSimplex2 B.code => (Sum.inr (Sum.inr u.val.1) : LLLVertex B))
        (card_activeSimplex_map_X_le_deg B h_deg)
        ((lllCandV B t).filter (fun v => LLLRawBad B t v (evalAssign (lllSupport B t) (lllCandV B t) v ω)))
        (hω t) Bad3A
        (fun u hu => ?_)
      -- Step 3: Conclude final cardinality and norm estimates for `bdl_step1_lll_unit_ball_multiplicity`
      rw [Finset.mem_filter] at hu
      rw [Finset.mem_filter]
      rcases hu.2 with ⟨hloc, hbad⟩
      have h_mem_cand : (Sum.inr (Sum.inr u.val.1) : LLLVertex B) ∈ lllCandV B t := by
        rw [h_cand_eq]
        exact Finset.mem_erase.mpr ⟨fun h => hbad.1.2.2.1 (Sum.inr.inj (Sum.inr.inj h)).symm,
          Finset.mem_erase.mpr ⟨fun h => hbad.1.2.1.1 (Sum.inr.inj (Sum.inr.inj h)).symm,
            Finset.mem_erase.mpr ⟨fun h => hbad.1.1.1 (Sum.inr.inj (Sum.inr.inj h)).symm,
              Finset.mem_map.mpr ⟨u.val.1, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hloc.1⟩, rfl⟩⟩⟩⟩
      refine ⟨h_mem_cand, u, rfl, ?_⟩
      have hs1_ev : lllSimplexPts B (evalAssign (lllSupport B t) (lllCandV B t) (Sum.inr (Sum.inr u.val.1)) ω) s1 =
          lllSimplexPts B ω s1 := by
        rw [h_supp_eq]
        exact lllSimplexPts_evalAssign_fixed B _ ω s1
          ⟨hs1_supp.1, by rw [h_cand_eq]; intro h; exact Finset.notMem_erase _ _ (Finset.mem_of_mem_erase (Finset.mem_of_mem_erase h))⟩
          ⟨hs1_supp.2.1, fun h => not_mem_candX_inl B _ _ (h_sub_cand h)⟩
          ⟨hs1_supp.2.2, fun h => not_mem_candX_inr_inl B _ _ (h_sub_cand h)⟩
      have hs2_ev : lllSimplexPts B (evalAssign (lllSupport B t) (lllCandV B t) (Sum.inr (Sum.inr u.val.1)) ω) s2 =
          lllSimplexPts B ω s2 := by
        rw [h_supp_eq]
        exact lllSimplexPts_evalAssign_fixed B _ ω s2
          ⟨hs2_supp.1, by rw [h_cand_eq]; intro h; exact Finset.notMem_erase _ _ (Finset.mem_of_mem_erase h)⟩
          ⟨hs2_supp.2.1, fun h => not_mem_candX_inl B _ _ (h_sub_cand h)⟩
          ⟨hs2_supp.2.2, fun h => not_mem_candX_inr_inl B _ _ (h_sub_cand h)⟩
      have hs3_ev : lllSimplexPts B (evalAssign (lllSupport B t) (lllCandV B t) (Sum.inr (Sum.inr u.val.1)) ω) s3 =
          lllSimplexPts B ω s3 := by
        rw [h_supp_eq]
        exact lllSimplexPts_evalAssign_fixed B _ ω s3
          ⟨hs3_supp.1, by rw [h_cand_eq]; exact Finset.notMem_erase _ _⟩
          ⟨hs3_supp.2.1, fun h => not_mem_candX_inl B _ _ (h_sub_cand h)⟩
          ⟨hs3_supp.2.2, fun h => not_mem_candX_inr_inl B _ _ (h_sub_cand h)⟩
      have hu_ev : lllSimplexPts B (evalAssign (lllSupport B t) (lllCandV B t) (Sum.inr (Sum.inr u.val.1)) ω) u =
          lllSimplexPts B ω u := by
        rw [h_supp_eq]; exact lllSimplexPts_evalAssign_candX B s1 u h_sub_cand hloc ω
      rw [hs1_ev, hs2_ev, hs3_ev, hu_ev]; exact hbad
    have h_card3B : Bad3B.card ≤ 54 * 32 := by
      let t : LLLEvent B := Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl (s1, s2, s3)))))
      have h_act : LLLEventActive B t := ⟨hloc12, hloc13⟩
      have h_cand_eq : lllCandV B t = (((candQ B (B.code.posQ s1.val.2.1)).erase (Sum.inl s1.val.2.1)).erase (Sum.inl s2.val.2.1)).erase (Sum.inl s3.val.2.1) := by
        dsimp [lllCandV, t]; dsimp [LLLEventActive, t] at h_act; rw [if_pos h_act]
      have h_supp_eq : lllSupport B t = localBoxSupport B (B.code.posQ s1.val.2.1) := by
        dsimp [lllSupport, t]; rw [if_pos h_act]; rfl
      have h_sub_cand : lllCandV B t ⊆ candQ B (B.code.posQ s1.val.2.1) := by
        rw [h_cand_eq]; exact Finset.Subset.trans (Finset.erase_subset _ _) (Finset.Subset.trans (Finset.erase_subset _ _) (Finset.erase_subset _ _))
      refine card_filter_simplex_le_mul_deg_of_cand_filter_le
        (fun u : ActiveSimplex2 B.code => (Sum.inl u.val.2.1 : LLLVertex B))
        (card_activeSimplex_map_Q_le_deg B h_deg)
        ((lllCandV B t).filter (fun v => LLLRawBad B t v (evalAssign (lllSupport B t) (lllCandV B t) v ω)))
        (hω t) Bad3B
        (fun u hu => ?_)
      rw [Finset.mem_filter] at hu
      rw [Finset.mem_filter]
      rcases hu.2 with ⟨hloc, hbad⟩
      have h_mem_cand : (Sum.inl u.val.2.1 : LLLVertex B) ∈ lllCandV B t := by
        rw [h_cand_eq]
        exact Finset.mem_erase.mpr ⟨fun h => hbad.1.2.2.2.1 (Sum.inl.inj h).symm,
          Finset.mem_erase.mpr ⟨fun h => hbad.1.2.1.2.1 (Sum.inl.inj h).symm,
            Finset.mem_erase.mpr ⟨fun h => hbad.1.1.2.1 (Sum.inl.inj h).symm,
              Finset.mem_map.mpr ⟨u.val.2.1, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hloc.2.1⟩, rfl⟩⟩⟩⟩
      refine ⟨h_mem_cand, u, rfl, ?_⟩
      have hs1_ev : lllSimplexPts B (evalAssign (lllSupport B t) (lllCandV B t) (Sum.inl u.val.2.1) ω) s1 =
          lllSimplexPts B ω s1 := by
        rw [h_supp_eq]
        exact lllSimplexPts_evalAssign_fixed B _ ω s1
          ⟨hs1_supp.1, fun h => not_mem_candQ_inr_inr B _ _ (h_sub_cand h)⟩
          ⟨hs1_supp.2.1, by rw [h_cand_eq]; intro h; exact Finset.notMem_erase _ _ (Finset.mem_of_mem_erase (Finset.mem_of_mem_erase h))⟩
          ⟨hs1_supp.2.2, fun h => not_mem_candQ_inr_inl B _ _ (h_sub_cand h)⟩
      have hs2_ev : lllSimplexPts B (evalAssign (lllSupport B t) (lllCandV B t) (Sum.inl u.val.2.1) ω) s2 =
          lllSimplexPts B ω s2 := by
        rw [h_supp_eq]
        exact lllSimplexPts_evalAssign_fixed B _ ω s2
          ⟨hs2_supp.1, fun h => not_mem_candQ_inr_inr B _ _ (h_sub_cand h)⟩
          ⟨hs2_supp.2.1, by rw [h_cand_eq]; intro h; exact Finset.notMem_erase _ _ (Finset.mem_of_mem_erase h)⟩
          ⟨hs2_supp.2.2, fun h => not_mem_candQ_inr_inl B _ _ (h_sub_cand h)⟩
      have hs3_ev : lllSimplexPts B (evalAssign (lllSupport B t) (lllCandV B t) (Sum.inl u.val.2.1) ω) s3 =
          lllSimplexPts B ω s3 := by
        rw [h_supp_eq]
        exact lllSimplexPts_evalAssign_fixed B _ ω s3
          ⟨hs3_supp.1, fun h => not_mem_candQ_inr_inr B _ _ (h_sub_cand h)⟩
          ⟨hs3_supp.2.1, by rw [h_cand_eq]; exact Finset.notMem_erase _ _⟩
          ⟨hs3_supp.2.2, fun h => not_mem_candQ_inr_inl B _ _ (h_sub_cand h)⟩
      have hu_ev : lllSimplexPts B (evalAssign (lllSupport B t) (lllCandV B t) (Sum.inl u.val.2.1) ω) u =
          lllSimplexPts B ω u := by
        rw [h_supp_eq]; exact lllSimplexPts_evalAssign_candQ B s1 u h_sub_cand hloc ω
      rw [hs1_ev, hs2_ev, hs3_ev, hu_ev]; exact hbad
    have h_card3C : Bad3C.card ≤ 54 * 32 := by
      let t : LLLEvent B := Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (s1, s2, s3)))))
      have h_act : LLLEventActive B t := ⟨hloc12, hloc13⟩
      have h_cand_eq : lllCandV B t = (((candZ B (B.code.posQ s1.val.2.1)).erase (Sum.inr (Sum.inl s1.val.2.2))).erase (Sum.inr (Sum.inl s2.val.2.2))).erase (Sum.inr (Sum.inl s3.val.2.2)) := by
        dsimp [lllCandV, t]; dsimp [LLLEventActive, t] at h_act; rw [if_pos h_act]
      have h_supp_eq : lllSupport B t = localBoxSupport B (B.code.posQ s1.val.2.1) := by
        dsimp [lllSupport, t]; rw [if_pos h_act]; rfl
      have h_sub_cand : lllCandV B t ⊆ candZ B (B.code.posQ s1.val.2.1) := by
        rw [h_cand_eq]; exact Finset.Subset.trans (Finset.erase_subset _ _) (Finset.Subset.trans (Finset.erase_subset _ _) (Finset.erase_subset _ _))
      refine card_filter_simplex_le_mul_deg_of_cand_filter_le
        (fun u : ActiveSimplex2 B.code => (Sum.inr (Sum.inl u.val.2.2) : LLLVertex B))
        (card_activeSimplex_map_Z_le_deg B h_deg)
        ((lllCandV B t).filter (fun v => LLLRawBad B t v (evalAssign (lllSupport B t) (lllCandV B t) v ω)))
        (hω t) Bad3C
        (fun u hu => ?_)
      rw [Finset.mem_filter] at hu
      rw [Finset.mem_filter]
      rcases hu.2 with ⟨hloc, hbad⟩
      have h_mem_cand : (Sum.inr (Sum.inl u.val.2.2) : LLLVertex B) ∈ lllCandV B t := by
        rw [h_cand_eq]
        exact Finset.mem_erase.mpr ⟨fun h => hbad.1.2.2.2.2 (Sum.inl.inj (Sum.inr.inj h)).symm,
          Finset.mem_erase.mpr ⟨fun h => hbad.1.2.1.2.2 (Sum.inl.inj (Sum.inr.inj h)).symm,
            Finset.mem_erase.mpr ⟨fun h => hbad.1.1.2.2 (Sum.inl.inj (Sum.inr.inj h)).symm,
              Finset.mem_map.mpr ⟨u.val.2.2, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hloc.2.2⟩, rfl⟩⟩⟩⟩
      refine ⟨h_mem_cand, u, rfl, ?_⟩
      have hs1_ev : lllSimplexPts B (evalAssign (lllSupport B t) (lllCandV B t) (Sum.inr (Sum.inl u.val.2.2)) ω) s1 =
          lllSimplexPts B ω s1 := by
        rw [h_supp_eq]
        exact lllSimplexPts_evalAssign_fixed B _ ω s1
          ⟨hs1_supp.1, fun h => not_mem_candZ_inr_inr B _ _ (h_sub_cand h)⟩
          ⟨hs1_supp.2.1, fun h => not_mem_candZ_inl B _ _ (h_sub_cand h)⟩
          ⟨hs1_supp.2.2, by rw [h_cand_eq]; intro h; exact Finset.notMem_erase _ _ (Finset.mem_of_mem_erase (Finset.mem_of_mem_erase h))⟩
      have hs2_ev : lllSimplexPts B (evalAssign (lllSupport B t) (lllCandV B t) (Sum.inr (Sum.inl u.val.2.2)) ω) s2 =
          lllSimplexPts B ω s2 := by
        rw [h_supp_eq]
        exact lllSimplexPts_evalAssign_fixed B _ ω s2
          ⟨hs2_supp.1, fun h => not_mem_candZ_inr_inr B _ _ (h_sub_cand h)⟩
          ⟨hs2_supp.2.1, fun h => not_mem_candZ_inl B _ _ (h_sub_cand h)⟩
          ⟨hs2_supp.2.2, by rw [h_cand_eq]; intro h; exact Finset.notMem_erase _ _ (Finset.mem_of_mem_erase h)⟩
      have hs3_ev : lllSimplexPts B (evalAssign (lllSupport B t) (lllCandV B t) (Sum.inr (Sum.inl u.val.2.2)) ω) s3 =
          lllSimplexPts B ω s3 := by
        rw [h_supp_eq]
        exact lllSimplexPts_evalAssign_fixed B _ ω s3
          ⟨hs3_supp.1, fun h => not_mem_candZ_inr_inr B _ _ (h_sub_cand h)⟩
          ⟨hs3_supp.2.1, fun h => not_mem_candZ_inl B _ _ (h_sub_cand h)⟩
          ⟨hs3_supp.2.2, by rw [h_cand_eq]; exact Finset.notMem_erase _ _⟩
      have hu_ev : lllSimplexPts B (evalAssign (lllSupport B t) (lllCandV B t) (Sum.inr (Sum.inl u.val.2.2)) ω) u =
          lllSimplexPts B ω u := by
        rw [h_supp_eq]; exact lllSimplexPts_evalAssign_candZ B s1 u h_sub_cand hloc ω
      rw [hs1_ev, hs2_ev, hs3_ev, hu_ev]; exact hbad
    have h_sub3 : Finset.univ.filter (fun u : ActiveSimplex2 B.code =>
        VertexDisjointSimplex2 s1.val u.val ∧
        VertexDisjointSimplex2 s2.val u.val ∧
        VertexDisjointSimplex2 s3.val u.val ∧
        SimplexInLocalBox B s1 u ∧
        FourSimplicesDominantCramerCompatible _pcode s1 s2 s3 u) ⊆ (Bad3A ∪ Bad3B) ∪ Bad3C := by
      intro u hu
      rw [Finset.mem_filter] at hu
      rcases hu.2 with ⟨hd1u, hd2u, hd3u, hloc, h_compat⟩
      rcases stage3_dominant_type_trichotomy_pts B h8 ω s1 s2 s3 u ⟨hd1u, hd2u, hd3u⟩ hD4 h_compat with hA | hB | hC
      · exact Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨Finset.mem_univ u, hloc, hA⟩))
      · exact Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨Finset.mem_univ u, hloc, hB⟩))
      · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨Finset.mem_univ u, hloc, hC⟩)
    have h_u1 := Finset.card_le_card h_sub3
    have h_u2 := Finset.card_union_le (Bad3A ∪ Bad3B) Bad3C
    have h_u3 := Finset.card_union_le Bad3A Bad3B
    omega

end WeldedHierarchy
