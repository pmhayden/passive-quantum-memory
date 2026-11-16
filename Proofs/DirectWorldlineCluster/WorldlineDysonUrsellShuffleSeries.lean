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

import Proofs.DirectWorldlineCluster.WorldlineDysonUrsellShuffle

/-!
# Shuffle Bijection and Infinite-Series Equivalence for Multi-Polymer Dyson Weights

Proves commutation of jump-monomer operator lists across disjoint RCA collars and establishes the exact finite-cutoff shuffle bijection between single-sector Dyson jump weights and compatible multi-polymer cluster sums (`sum_validClusterFinset_raw_eq_sum_singleSector`). Passes to the convergent infinite series to obtain `tsum_singleSectorWorldlineDysonJumpWeight_eq_tsum_dysonMultiPolymerClusterWeight`.

## References

* Part II, Section 3.5 (`subsec:worldline-expansion`), Lemma 3.9 (`lem:worldline-factorization-time-reversal`)
* Part II, Section 3.5 (`subsec:worldline-expansion`), Proposition 3.10 (`prop:tube-local-ursell-erasure`)
-/

noncomputable section

open scoped Classical BigOperators InnerProduct ComplexConjugate
open Filter Topology Asymptotics ContinuousLinearMap KMSPinchedGibbs PerturbedThermalBarrier
open SpacetimeWorldlineKP

set_option linter.unusedVariables false
set_option maxRecDepth 10000
set_option maxHeartbeats 1600000

namespace DirectWorldlineCluster

local notation "SiteCSS[" L ", " q_code "]" => UniformSite3D L (CodeSlotConfig q_code)
local notation "ℋ_CSS[" L ", " q_code "]" => ManyBodyHilbertSpace (SiteCSS[L, q_code])
local notation "ℬ_CSS[" L ", " q_code "]" => ℋ_CSS[L, q_code] →L[ℂ] ℋ_CSS[L, q_code]
local notation "IdxCSS[" L ", " q_code ", " m_max "]" => StaticCSSCheckIdx L q_code m_max
local notation "SysCSS[" L ", " q_code ", " m_max "]" =>
  IndexedCommutingProjectorHamiltonian 3 L (SiteCSS[L, q_code]) (IdxCSS[L, q_code, m_max])

local instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

/-! ## 1. Shuffle Operator Commutation on Realizable Syndrome Sectors -/

private lemma commute_worldlineSyndromeShiftBlockOp_list_prod_reverse_of_disjoint
    {L q_code r_0 m_max : ℕ} [NeZero L]
    (D_field : Box3D L → LocalCSSDescriptor q_code r_0 m_max)
    (sys : SysCSS[L, q_code, m_max])
    (h_sys_checks : ∀ idx, sys.checkProj idx = staticCSSCheckProj D_field idx ∧
      sys.support idx = staticCSSCheckSupport D_field idx ∧ sys.weight idx = 1)
    {C_RCA : ℝ} (hC_RCA : 1 ≤ C_RCA)
    (V : QuasiLocalPerturbation 3 L (SiteCSS[L, q_code]))
    (ξ₀ : WorldlineJumpMonomer L q_code)
    (hA₀ : ξ₀.1.2 ∈ boxCubes 3 L ξ₀.1.1)
    (hV₀ : IsSupportedOn (SiteCSS[L, q_code]) ξ₀.1.2 (V.term ξ₀.1.1 ξ₀.1.2))
    (h_ne₀ : staticCSSPauliFlip D_field ξ₀.2.1 ξ₀.2.2 ≠ (fun _ => false))
    (l : List (WorldlineJumpMonomer L q_code))
    (hl : ∀ ξ ∈ l, ξ.1.2 ∈ boxCubes 3 L ξ.1.1 ∧
      IsSupportedOn (SiteCSS[L, q_code]) ξ.1.2 (V.term ξ.1.1 ξ.1.2) ∧
      staticCSSPauliFlip D_field ξ.2.1 ξ.2.2 ≠ (fun _ => false) ∧
      Disjoint (rcaCollarChecks sys C_RCA ξ₀.1.1 ξ₀.1.2)
        (rcaCollarChecks sys C_RCA ξ.1.1 ξ.1.2)) :
    ∀ {σ₀ : IdxCSS[L, q_code, m_max] → Bool}, σ₀ ∈ realizableSyndromes D_field →
      worldlineSyndromeShiftBlockOp D_field sys V ξ₀ *
        ((l.reverse.map (worldlineSyndromeShiftBlockOp D_field sys V)).prod *
          sys.syndromeProjector σ₀) =
      (l.reverse.map (worldlineSyndromeShiftBlockOp D_field sys V)).prod *
        (worldlineSyndromeShiftBlockOp D_field sys V ξ₀ * sys.syndromeProjector σ₀) := by
  induction l with
  | nil =>
    intro σ₀ _
    simp
  | cons hd tl ih =>
    intro σ₀ hσ₀
    rcases hl hd List.mem_cons_self with ⟨hA_hd, hV_hd, h_ne_hd, h_disj_hd⟩
    have h_tl_prop : ∀ ξ ∈ tl, ξ.1.2 ∈ boxCubes 3 L ξ.1.1 ∧
        IsSupportedOn (SiteCSS[L, q_code]) ξ.1.2 (V.term ξ.1.1 ξ.1.2) ∧
        staticCSSPauliFlip D_field ξ.2.1 ξ.2.2 ≠ (fun _ => false) ∧
        Disjoint (rcaCollarChecks sys C_RCA ξ₀.1.1 ξ₀.1.2)
          (rcaCollarChecks sys C_RCA ξ.1.1 ξ.1.2) :=
      fun ξ hξ => hl ξ (List.mem_cons_of_mem hd hξ)
    let B := worldlineSyndromeShiftBlockOp D_field sys V
    let δ_hd := staticCSSPauliFlip D_field hd.2.1 hd.2.2
    have hσ_hd : syndromeXor δ_hd σ₀ ∈ realizableSyndromes D_field :=
      syndromeXor_staticCSSPauliFlip_mem_realizableSyndromes D_field hd.2.1 hd.2.2 σ₀ hσ₀
    have h_abs_hd :
        sys.syndromeProjector (syndromeXor δ_hd σ₀) * (B hd * sys.syndromeProjector σ₀) =
          B hd * sys.syndromeProjector σ₀ :=
      (worldlineSyndromeShiftBlockOp_mul_syndromeProjector D_field sys V hd σ₀).2
    have h_prod_rev : ((hd :: tl).reverse.map B).prod = (tl.reverse.map B).prod * B hd := by
      rw [List.reverse_cons, List.map_append, List.prod_append, List.map_cons,
        List.map_nil, List.prod_cons, List.prod_nil, mul_one]
    have h_comm_hd :
        B ξ₀ * (B hd * sys.syndromeProjector σ₀) = B hd * (B ξ₀ * sys.syndromeProjector σ₀) :=
      commute_worldlineSyndromeShiftBlockOp_mul_syndromeProjector_of_disjoint_rcaCollarChecks
        D_field sys h_sys_checks hC_RCA V ξ₀ hd hA₀ hA_hd hV₀ hV_hd h_ne₀ h_ne_hd h_disj_hd hσ₀
    have h_ih :
        B ξ₀ * ((tl.reverse.map B).prod * sys.syndromeProjector (syndromeXor δ_hd σ₀)) =
          (tl.reverse.map B).prod * (B ξ₀ * sys.syndromeProjector (syndromeXor δ_hd σ₀)) :=
      ih h_tl_prop hσ_hd
    change B ξ₀ * (((hd :: tl).reverse.map B).prod * sys.syndromeProjector σ₀) =
      ((hd :: tl).reverse.map B).prod * (B ξ₀ * sys.syndromeProjector σ₀)
    calc B ξ₀ * (((hd :: tl).reverse.map B).prod * sys.syndromeProjector σ₀)
      _ = B ξ₀ * ((tl.reverse.map B).prod *
            (sys.syndromeProjector (syndromeXor δ_hd σ₀) * (B hd * sys.syndromeProjector σ₀))) := by
          rw [h_prod_rev, mul_assoc (tl.reverse.map B).prod, h_abs_hd]
      _ = (B ξ₀ * ((tl.reverse.map B).prod * sys.syndromeProjector (syndromeXor δ_hd σ₀))) *
            (B hd * sys.syndromeProjector σ₀) := by
          simp only [mul_assoc]
      _ = ((tl.reverse.map B).prod * (B ξ₀ * sys.syndromeProjector (syndromeXor δ_hd σ₀))) *
            (B hd * sys.syndromeProjector σ₀) := by
          rw [h_ih]
      _ = (tl.reverse.map B).prod *
            (B ξ₀ * (sys.syndromeProjector (syndromeXor δ_hd σ₀) * (B hd * sys.syndromeProjector σ₀))) := by
          simp only [mul_assoc]
      _ = (tl.reverse.map B).prod * (B ξ₀ * (B hd * sys.syndromeProjector σ₀)) := by
          rw [h_abs_hd]
      _ = (tl.reverse.map B).prod * (B hd * (B ξ₀ * sys.syndromeProjector σ₀)) := by
          rw [h_comm_hd]
      _ = ((hd :: tl).reverse.map B).prod * (B ξ₀ * sys.syndromeProjector σ₀) := by
          rw [h_prod_rev, mul_assoc]

private lemma list_prod_reverse_worldlineSyndromeShiftBlockOp_mul_syndromeProjector_absorb
    {L q_code r_0 m_max : ℕ}
    (D_field : Box3D L → LocalCSSDescriptor q_code r_0 m_max)
    (sys : SysCSS[L, q_code, m_max])
    (V : QuasiLocalPerturbation 3 L (SiteCSS[L, q_code]))
    (l : List (WorldlineJumpMonomer L q_code)) :
    ∀ σ₀ : IdxCSS[L, q_code, m_max] → Bool,
      ∃ σ' : IdxCSS[L, q_code, m_max] → Bool,
        (σ₀ ∈ realizableSyndromes D_field → σ' ∈ realizableSyndromes D_field) ∧
        sys.syndromeProjector σ' *
          ((l.reverse.map (worldlineSyndromeShiftBlockOp D_field sys V)).prod *
            sys.syndromeProjector σ₀) =
        (l.reverse.map (worldlineSyndromeShiftBlockOp D_field sys V)).prod *
          sys.syndromeProjector σ₀ := by
  induction l with
  | nil =>
    intro σ₀
    refine ⟨σ₀, id, ?_⟩
    simp only [List.reverse_nil, List.map_nil, List.prod_nil, one_mul]
    exact ((PerturbedThermalBarrier.syndrome_resolution_indexed sys).2.1 σ₀).1
  | cons hd tl ih =>
    intro σ₀
    let B := worldlineSyndromeShiftBlockOp D_field sys V
    let δ_hd := staticCSSPauliFlip D_field hd.2.1 hd.2.2
    rcases ih (syndromeXor δ_hd σ₀) with ⟨σ', hσ'_mem, hσ'_eq⟩
    refine ⟨σ', fun hσ₀ => hσ'_mem
      (syndromeXor_staticCSSPauliFlip_mem_realizableSyndromes D_field hd.2.1 hd.2.2 σ₀ hσ₀), ?_⟩
    have h_abs_hd :
        sys.syndromeProjector (syndromeXor δ_hd σ₀) * (B hd * sys.syndromeProjector σ₀) =
          B hd * sys.syndromeProjector σ₀ :=
      (worldlineSyndromeShiftBlockOp_mul_syndromeProjector D_field sys V hd σ₀).2
    have hσ'_eq' :
        sys.syndromeProjector σ' *
          ((tl.reverse.map B).prod * sys.syndromeProjector (syndromeXor δ_hd σ₀)) =
        (tl.reverse.map B).prod * sys.syndromeProjector (syndromeXor δ_hd σ₀) := hσ'_eq
    have h_prod_rev : ((hd :: tl).reverse.map B).prod = (tl.reverse.map B).prod * B hd := by
      rw [List.reverse_cons, List.map_append, List.prod_append, List.map_cons,
        List.map_nil, List.prod_cons, List.prod_nil, mul_one]
    change sys.syndromeProjector σ' * (((hd :: tl).reverse.map B).prod * sys.syndromeProjector σ₀) =
      ((hd :: tl).reverse.map B).prod * sys.syndromeProjector σ₀
    calc sys.syndromeProjector σ' * (((hd :: tl).reverse.map B).prod * sys.syndromeProjector σ₀)
      _ = (sys.syndromeProjector σ' *
            ((tl.reverse.map B).prod * sys.syndromeProjector (syndromeXor δ_hd σ₀))) *
            (B hd * sys.syndromeProjector σ₀) := by
          rw [h_prod_rev]
          simp only [mul_assoc]
          rw [h_abs_hd]
      _ = ((tl.reverse.map B).prod * sys.syndromeProjector (syndromeXor δ_hd σ₀)) *
            (B hd * sys.syndromeProjector σ₀) := by
          rw [hσ'_eq']
      _ = ((hd :: tl).reverse.map B).prod * sys.syndromeProjector σ₀ := by
          rw [mul_assoc (tl.reverse.map B).prod, h_abs_hd, ← mul_assoc (tl.reverse.map B).prod,
            ← h_prod_rev]

private lemma list_of_jumpLists_mul_syndromeProjector_absorb
    {L q_code r_0 m_max : ℕ}
    (D_field : Box3D L → LocalCSSDescriptor q_code r_0 m_max)
    (sys : SysCSS[L, q_code, m_max])
    (V : QuasiLocalPerturbation 3 L (SiteCSS[L, q_code]))
    (J : List (List (WorldlineJumpMonomer L q_code))) :
    ∀ σ : IdxCSS[L, q_code, m_max] → Bool,
      ∃ σ' : IdxCSS[L, q_code, m_max] → Bool,
        (σ ∈ realizableSyndromes D_field → σ' ∈ realizableSyndromes D_field) ∧
        sys.syndromeProjector σ' *
          ((J.map (fun l => (l.reverse.map (worldlineSyndromeShiftBlockOp D_field sys V)).prod)).prod *
            sys.syndromeProjector σ) =
        (J.map (fun l => (l.reverse.map (worldlineSyndromeShiftBlockOp D_field sys V)).prod)).prod *
          sys.syndromeProjector σ := by
  induction J with
  | nil =>
    intro σ
    refine ⟨σ, id, ?_⟩
    simp only [List.map_nil, List.prod_nil, one_mul]
    exact ((PerturbedThermalBarrier.syndrome_resolution_indexed sys).2.1 σ).1
  | cons l₁ Js ih_J =>
    intro σ
    let B := worldlineSyndromeShiftBlockOp D_field sys V
    let P_Js := (Js.map (fun l => (l.reverse.map B).prod)).prod
    rcases ih_J σ with ⟨σ₁, hσ₁_mem, hσ₁_eq⟩
    rcases list_prod_reverse_worldlineSyndromeShiftBlockOp_mul_syndromeProjector_absorb
      D_field sys V l₁ σ₁ with ⟨σ₂, hσ₂_mem, hσ₂_eq⟩
    refine ⟨σ₂, fun hσ => hσ₂_mem (hσ₁_mem hσ), ?_⟩
    have hσ₁_eq' : sys.syndromeProjector σ₁ * (P_Js * sys.syndromeProjector σ) =
        P_Js * sys.syndromeProjector σ := hσ₁_eq
    have hσ₂_eq' : sys.syndromeProjector σ₂ * ((l₁.reverse.map B).prod * sys.syndromeProjector σ₁) =
        (l₁.reverse.map B).prod * sys.syndromeProjector σ₁ := hσ₂_eq
    change sys.syndromeProjector σ₂ * (((l₁.reverse.map B).prod * P_Js) * sys.syndromeProjector σ) =
      ((l₁.reverse.map B).prod * P_Js) * sys.syndromeProjector σ
    calc sys.syndromeProjector σ₂ * (((l₁.reverse.map B).prod * P_Js) * sys.syndromeProjector σ)
      _ = (sys.syndromeProjector σ₂ * ((l₁.reverse.map B).prod * sys.syndromeProjector σ₁)) *
            (P_Js * sys.syndromeProjector σ) := by
          simp only [mul_assoc]
          rw [hσ₁_eq']
      _ = ((l₁.reverse.map B).prod * sys.syndromeProjector σ₁) *
            (P_Js * sys.syndromeProjector σ) := by
          rw [hσ₂_eq']
      _ = ((l₁.reverse.map B).prod * P_Js) * sys.syndromeProjector σ := by
          rw [mul_assoc (l₁.reverse.map B).prod, hσ₁_eq', ← mul_assoc (l₁.reverse.map B).prod]

private lemma commute_worldlineSyndromeShiftBlockOp_list_of_jumpLists_of_disjoint
    {L q_code r_0 m_max : ℕ} [NeZero L]
    (D_field : Box3D L → LocalCSSDescriptor q_code r_0 m_max)
    (sys : SysCSS[L, q_code, m_max])
    (h_sys_checks : ∀ idx, sys.checkProj idx = staticCSSCheckProj D_field idx ∧
      sys.support idx = staticCSSCheckSupport D_field idx ∧ sys.weight idx = 1)
    {C_RCA : ℝ} (hC_RCA : 1 ≤ C_RCA)
    (V : QuasiLocalPerturbation 3 L (SiteCSS[L, q_code]))
    (ξ₀ : WorldlineJumpMonomer L q_code)
    (hA₀ : ξ₀.1.2 ∈ boxCubes 3 L ξ₀.1.1)
    (hV₀ : IsSupportedOn (SiteCSS[L, q_code]) ξ₀.1.2 (V.term ξ₀.1.1 ξ₀.1.2))
    (h_ne₀ : staticCSSPauliFlip D_field ξ₀.2.1 ξ₀.2.2 ≠ (fun _ => false))
    (J : List (List (WorldlineJumpMonomer L q_code)))
    (hJ : ∀ l ∈ J, ∀ ξ ∈ l, ξ.1.2 ∈ boxCubes 3 L ξ.1.1 ∧
      IsSupportedOn (SiteCSS[L, q_code]) ξ.1.2 (V.term ξ.1.1 ξ.1.2) ∧
      staticCSSPauliFlip D_field ξ.2.1 ξ.2.2 ≠ (fun _ => false) ∧
      Disjoint (rcaCollarChecks sys C_RCA ξ₀.1.1 ξ₀.1.2)
        (rcaCollarChecks sys C_RCA ξ.1.1 ξ.1.2)) :
    ∀ {σ₀ : IdxCSS[L, q_code, m_max] → Bool}, σ₀ ∈ realizableSyndromes D_field →
      worldlineSyndromeShiftBlockOp D_field sys V ξ₀ *
        ((J.map (fun l => (l.reverse.map (worldlineSyndromeShiftBlockOp D_field sys V)).prod)).prod *
          sys.syndromeProjector σ₀) =
      (J.map (fun l => (l.reverse.map (worldlineSyndromeShiftBlockOp D_field sys V)).prod)).prod *
        (worldlineSyndromeShiftBlockOp D_field sys V ξ₀ * sys.syndromeProjector σ₀) := by
  induction J with
  | nil =>
    intro σ₀ _
    simp
  | cons l_hd J_tl ih =>
    intro σ₀ hσ₀
    let B := worldlineSyndromeShiftBlockOp D_field sys V
    let P_tl := (J_tl.map (fun l => (l.reverse.map B).prod)).prod
    rcases list_of_jumpLists_mul_syndromeProjector_absorb D_field sys V J_tl σ₀ with
      ⟨σ', hσ'_mem, hσ'_eq⟩
    have hσ' := hσ'_mem hσ₀
    have hσ'_eq' : sys.syndromeProjector σ' * (P_tl * sys.syndromeProjector σ₀) =
        P_tl * sys.syndromeProjector σ₀ := hσ'_eq
    have h_comm_hd : B ξ₀ * ((l_hd.reverse.map B).prod * sys.syndromeProjector σ') =
        (l_hd.reverse.map B).prod * (B ξ₀ * sys.syndromeProjector σ') :=
      commute_worldlineSyndromeShiftBlockOp_list_prod_reverse_of_disjoint
        D_field sys h_sys_checks hC_RCA V ξ₀ hA₀ hV₀ h_ne₀ l_hd (hJ l_hd List.mem_cons_self) hσ'
    have h_comm_tl : B ξ₀ * (P_tl * sys.syndromeProjector σ₀) =
        P_tl * (B ξ₀ * sys.syndromeProjector σ₀) :=
      ih (fun l hl => hJ l (List.mem_cons_of_mem l_hd hl)) hσ₀
    change B ξ₀ * (((l_hd.reverse.map B).prod * P_tl) * sys.syndromeProjector σ₀) =
      ((l_hd.reverse.map B).prod * P_tl) * (B ξ₀ * sys.syndromeProjector σ₀)
    calc B ξ₀ * (((l_hd.reverse.map B).prod * P_tl) * sys.syndromeProjector σ₀)
      _ = (B ξ₀ * ((l_hd.reverse.map B).prod * sys.syndromeProjector σ')) *
            (P_tl * sys.syndromeProjector σ₀) := by
          simp only [mul_assoc]
          rw [hσ'_eq']
      _ = (l_hd.reverse.map B).prod *
            (B ξ₀ * (sys.syndromeProjector σ' * (P_tl * sys.syndromeProjector σ₀))) := by
          rw [h_comm_hd]
          simp only [mul_assoc]
      _ = (l_hd.reverse.map B).prod * (B ξ₀ * (P_tl * sys.syndromeProjector σ₀)) := by
          rw [hσ'_eq']
      _ = ((l_hd.reverse.map B).prod * P_tl) * (B ξ₀ * sys.syndromeProjector σ₀) := by
          rw [h_comm_tl, mul_assoc]

private lemma prodJumpLists_set_cons_mul_syndromeProjector_eq
    {L q_code r_0 m_max : ℕ} [NeZero L]
    (D_field : Box3D L → LocalCSSDescriptor q_code r_0 m_max)
    (sys : SysCSS[L, q_code, m_max])
    (h_sys_checks : ∀ idx, sys.checkProj idx = staticCSSCheckProj D_field idx ∧
      sys.support idx = staticCSSCheckSupport D_field idx ∧ sys.weight idx = 1)
    {C_RCA : ℝ} (hC_RCA : 1 ≤ C_RCA)
    (V : QuasiLocalPerturbation 3 L (SiteCSS[L, q_code]))
    (ξ₀ : WorldlineJumpMonomer L q_code)
    (hA₀ : ξ₀.1.2 ∈ boxCubes 3 L ξ₀.1.1)
    (hV₀ : IsSupportedOn (SiteCSS[L, q_code]) ξ₀.1.2 (V.term ξ₀.1.1 ξ₀.1.2))
    (h_ne₀ : staticCSSPauliFlip D_field ξ₀.2.1 ξ₀.2.2 ≠ (fun _ => false))
    (J : List (List (WorldlineJumpMonomer L q_code)))
    (idx : ℕ) (h_idx : idx < J.length)
    (hJ : ∀ l ∈ J.drop (idx + 1), ∀ ξ ∈ l, ξ.1.2 ∈ boxCubes 3 L ξ.1.1 ∧
      IsSupportedOn (SiteCSS[L, q_code]) ξ.1.2 (V.term ξ.1.1 ξ.1.2) ∧
      staticCSSPauliFlip D_field ξ.2.1 ξ.2.2 ≠ (fun _ => false) ∧
      Disjoint (rcaCollarChecks sys C_RCA ξ₀.1.1 ξ₀.1.2)
        (rcaCollarChecks sys C_RCA ξ.1.1 ξ.1.2))
    {σ₀ : IdxCSS[L, q_code, m_max] → Bool} (hσ₀ : σ₀ ∈ realizableSyndromes D_field) :
    ((J.set idx (ξ₀ :: J[idx])).map
      (fun l => (l.reverse.map (worldlineSyndromeShiftBlockOp D_field sys V)).prod)).prod *
      sys.syndromeProjector σ₀ =
    (J.map (fun l => (l.reverse.map (worldlineSyndromeShiftBlockOp D_field sys V)).prod)).prod *
      (worldlineSyndromeShiftBlockOp D_field sys V ξ₀ * sys.syndromeProjector σ₀) := by
  induction J generalizing idx with
  | nil =>
    cases h_idx
  | cons l_hd J_tl ih =>
    let B := worldlineSyndromeShiftBlockOp D_field sys V
    let P_tl := (J_tl.map (fun l => (l.reverse.map B).prod)).prod
    cases idx with
    | zero =>
      simp only [List.getElem_cons_zero, List.set_cons_zero, List.map_cons, List.prod_cons]
      simp only [List.drop_succ_cons, List.drop_zero] at hJ
      have h_prod_rev : ((ξ₀ :: l_hd).reverse.map B).prod = (l_hd.reverse.map B).prod * B ξ₀ := by
        rw [List.reverse_cons, List.map_append, List.prod_append, List.map_cons,
          List.map_nil, List.prod_cons, List.prod_nil, mul_one]
      have h_comm : B ξ₀ * (P_tl * sys.syndromeProjector σ₀) =
          P_tl * (B ξ₀ * sys.syndromeProjector σ₀) :=
        commute_worldlineSyndromeShiftBlockOp_list_of_jumpLists_of_disjoint
          D_field sys h_sys_checks hC_RCA V ξ₀ hA₀ hV₀ h_ne₀ J_tl hJ hσ₀
      change ((ξ₀ :: l_hd).reverse.map B).prod * P_tl * sys.syndromeProjector σ₀ =
        (l_hd.reverse.map B).prod * P_tl * (B ξ₀ * sys.syndromeProjector σ₀)
      calc ((ξ₀ :: l_hd).reverse.map B).prod * P_tl * sys.syndromeProjector σ₀
        _ = (l_hd.reverse.map B).prod * (B ξ₀ * (P_tl * sys.syndromeProjector σ₀)) := by
            rw [h_prod_rev]
            simp only [mul_assoc]
        _ = (l_hd.reverse.map B).prod * P_tl * (B ξ₀ * sys.syndromeProjector σ₀) := by
            rw [h_comm, ← mul_assoc]
    | succ idx' =>
      have h_idx' : idx' < J_tl.length := Nat.lt_of_succ_lt_succ h_idx
      simp only [List.getElem_cons_succ, List.set_cons_succ, List.map_cons, List.prod_cons]
      simp only [List.drop_succ_cons] at hJ
      have h_ih :
          ((J_tl.set idx' (ξ₀ :: J_tl[idx'])).map (fun l => (l.reverse.map B).prod)).prod *
            sys.syndromeProjector σ₀ =
          P_tl * (B ξ₀ * sys.syndromeProjector σ₀) :=
        ih idx' h_idx' hJ
      change (l_hd.reverse.map B).prod *
          ((J_tl.set idx' (ξ₀ :: J_tl[idx'])).map (fun l => (l.reverse.map B).prod)).prod *
          sys.syndromeProjector σ₀ =
        (l_hd.reverse.map B).prod * P_tl * (B ξ₀ * sys.syndromeProjector σ₀)
      rw [mul_assoc, h_ih, ← mul_assoc]

private lemma prodJumpLists_of_filter_partition_eq
    {L q_code r_0 m_max : ℕ} [NeZero L]
    (D_field : Box3D L → LocalCSSDescriptor q_code r_0 m_max)
    (sys : SysCSS[L, q_code, m_max])
    (h_sys_checks : ∀ idx, sys.checkProj idx = staticCSSCheckProj D_field idx ∧
      sys.support idx = staticCSSCheckSupport D_field idx ∧ sys.weight idx = 1)
    {C_RCA : ℝ} (hC_RCA : 1 ≤ C_RCA)
    (V : QuasiLocalPerturbation 3 L (SiteCSS[L, q_code]))
    (n : ℕ) (P : Fin n → WorldlineJumpMonomer L q_code → Bool)
    (ξ_list : List (WorldlineJumpMonomer L q_code))
    (h_jumps : ∀ ξ ∈ ξ_list, ξ.1.2 ∈ boxCubes 3 L ξ.1.1 ∧
      IsSupportedOn (SiteCSS[L, q_code]) ξ.1.2 (V.term ξ.1.1 ξ.1.2) ∧
      staticCSSPauliFlip D_field ξ.2.1 ξ.2.2 ≠ (fun _ => false))
    (h_ex : ∀ ξ ∈ ξ_list, ∃ a : Fin n, P a ξ = true)
    (h_uniq : ∀ ξ ∈ ξ_list, ∀ a b : Fin n, P a ξ = true → P b ξ = true → a = b)
    (h_disj : ∀ ξ₁ ∈ ξ_list, ∀ ξ₂ ∈ ξ_list, ∀ a b : Fin n, a ≠ b →
      P a ξ₁ = true → P b ξ₂ = true →
      Disjoint (rcaCollarChecks sys C_RCA ξ₁.1.1 ξ₁.1.2)
        (rcaCollarChecks sys C_RCA ξ₂.1.1 ξ₂.1.2)) :
    ∀ {σ₀ : IdxCSS[L, q_code, m_max] → Bool}, σ₀ ∈ realizableSyndromes D_field →
      (((List.ofFn (fun a : Fin n => ξ_list.filter (P a))).map
        (fun l => (l.reverse.map (worldlineSyndromeShiftBlockOp D_field sys V)).prod)).prod) *
        sys.syndromeProjector σ₀ =
      (ξ_list.reverse.map (worldlineSyndromeShiftBlockOp D_field sys V)).prod *
        sys.syndromeProjector σ₀ := by
  induction ξ_list with
  | nil =>
    intro σ₀ _
    have h_one : (((List.ofFn (fun a : Fin n => ([] : List (WorldlineJumpMonomer L q_code)).filter (P a))).map
        (fun l => (l.reverse.map (worldlineSyndromeShiftBlockOp D_field sys V)).prod)).prod) = 1 := by
      refine List.prod_eq_one fun x hx => ?_
      rcases List.mem_map.mp hx with ⟨l, hl, rfl⟩
      rcases List.mem_ofFn.mp hl with ⟨a, rfl⟩
      simp
    rw [h_one, List.reverse_nil, List.map_nil, List.prod_nil]
  | cons ξ₀ tl ih =>
    intro σ₀ hσ₀
    let B := worldlineSyndromeShiftBlockOp D_field sys V
    let δ₀ := staticCSSPauliFlip D_field ξ₀.2.1 ξ₀.2.2
    let J_tl := List.ofFn (fun a : Fin n => tl.filter (P a))
    rcases h_jumps ξ₀ List.mem_cons_self with ⟨hA₀, hV₀, h_ne₀⟩
    rcases h_ex ξ₀ List.mem_cons_self with ⟨a₀, ha₀⟩
    have ha₀_lt : a₀.1 < J_tl.length := by simp [J_tl]
    have h_set_eq : List.ofFn (fun a : Fin n => (ξ₀ :: tl).filter (P a)) =
        J_tl.set a₀.1 (ξ₀ :: J_tl[a₀.1]'ha₀_lt) := by
      refine List.ext_getElem (by simp [J_tl]) fun i hi₁ hi₂ => ?_
      have hi_n : i < n := by simpa using hi₁
      rw [List.getElem_ofFn, List.getElem_set]
      split_ifs with h_eq
      · have ha_eq : (⟨i, hi_n⟩ : Fin n) = a₀ := Fin.ext h_eq.symm
        rw [ha_eq, List.filter_cons_of_pos ha₀, List.getElem_ofFn]
      · have ha_ne : (⟨i, hi_n⟩ : Fin n) ≠ a₀ := fun h => h_eq (congrArg Fin.val h).symm
        have h_false : P ⟨i, hi_n⟩ ξ₀ = false := by
          cases hP : P ⟨i, hi_n⟩ ξ₀
          · rfl
          · exact False.elim (ha_ne (h_uniq ξ₀ List.mem_cons_self ⟨i, hi_n⟩ a₀ hP ha₀))
        rw [List.filter_cons_of_neg (by simp [h_false])]
        simp [J_tl]
    have hJ_drop : ∀ l ∈ J_tl.drop (a₀.1 + 1), ∀ ξ ∈ l,
        ξ.1.2 ∈ boxCubes 3 L ξ.1.1 ∧
        IsSupportedOn (SiteCSS[L, q_code]) ξ.1.2 (V.term ξ.1.1 ξ.1.2) ∧
        staticCSSPauliFlip D_field ξ.2.1 ξ.2.2 ≠ (fun _ => false) ∧
        Disjoint (rcaCollarChecks sys C_RCA ξ₀.1.1 ξ₀.1.2)
          (rcaCollarChecks sys C_RCA ξ.1.1 ξ.1.2) := by
      intro l hl ξ hξ
      rcases List.mem_iff_getElem.mp hl with ⟨k, hk, rfl⟩
      rw [List.getElem_drop] at hξ
      have hk_lt : a₀.1 + 1 + k < n := by
        have h_len : (J_tl.drop (a₀.1 + 1)).length = n - (a₀.1 + 1) := by simp [J_tl]
        omega
      have h_get : J_tl[a₀.1 + 1 + k]'(by simp [J_tl, hk_lt]) = tl.filter (P ⟨a₀.1 + 1 + k, hk_lt⟩) := by
        simp [J_tl]
      rw [h_get] at hξ
      rcases List.mem_filter.mp hξ with ⟨hξ_tl, hP_b⟩
      have hξ_mem : ξ ∈ ξ₀ :: tl := List.mem_cons_of_mem ξ₀ hξ_tl
      rcases h_jumps ξ hξ_mem with ⟨hA, hV, h_ne⟩
      have hb_ne : a₀ ≠ ⟨a₀.1 + 1 + k, hk_lt⟩ := by
        intro h_eq
        have : a₀.1 = a₀.1 + 1 + k := congrArg Fin.val h_eq
        omega
      exact ⟨hA, hV, h_ne, h_disj ξ₀ List.mem_cons_self ξ hξ_mem a₀ ⟨a₀.1 + 1 + k, hk_lt⟩ hb_ne ha₀ hP_b⟩
    have h_step1 := prodJumpLists_set_cons_mul_syndromeProjector_eq
      D_field sys h_sys_checks hC_RCA V ξ₀ hA₀ hV₀ h_ne₀ J_tl a₀.1 ha₀_lt hJ_drop hσ₀
    have hσ_δ₀ : syndromeXor δ₀ σ₀ ∈ realizableSyndromes D_field :=
      syndromeXor_staticCSSPauliFlip_mem_realizableSyndromes D_field ξ₀.2.1 ξ₀.2.2 σ₀ hσ₀
    have h_abs_ξ₀ :
        sys.syndromeProjector (syndromeXor δ₀ σ₀) * (B ξ₀ * sys.syndromeProjector σ₀) =
          B ξ₀ * sys.syndromeProjector σ₀ :=
      (worldlineSyndromeShiftBlockOp_mul_syndromeProjector D_field sys V ξ₀ σ₀).2
    have h_ih :
        (J_tl.map (fun l => (l.reverse.map B).prod)).prod * sys.syndromeProjector (syndromeXor δ₀ σ₀) =
          (tl.reverse.map B).prod * sys.syndromeProjector (syndromeXor δ₀ σ₀) :=
      ih (fun ξ hξ => h_jumps ξ (List.mem_cons_of_mem ξ₀ hξ))
        (fun ξ hξ => h_ex ξ (List.mem_cons_of_mem ξ₀ hξ))
        (fun ξ hξ => h_uniq ξ (List.mem_cons_of_mem ξ₀ hξ))
        (fun ξ₁ hξ₁ ξ₂ hξ₂ => h_disj ξ₁ (List.mem_cons_of_mem ξ₀ hξ₁) ξ₂ (List.mem_cons_of_mem ξ₀ hξ₂))
        hσ_δ₀
    have h_prod_rev : ((ξ₀ :: tl).reverse.map B).prod = (tl.reverse.map B).prod * B ξ₀ := by
      rw [List.reverse_cons, List.map_append, List.prod_append, List.map_cons,
        List.map_nil, List.prod_cons, List.prod_nil, mul_one]
    rw [h_set_eq, h_step1]
    change (J_tl.map (fun l => (l.reverse.map B).prod)).prod * (B ξ₀ * sys.syndromeProjector σ₀) =
      ((ξ₀ :: tl).reverse.map B).prod * sys.syndromeProjector σ₀
    calc (J_tl.map (fun l => (l.reverse.map B).prod)).prod * (B ξ₀ * sys.syndromeProjector σ₀)
      _ = ((J_tl.map (fun l => (l.reverse.map B).prod)).prod *
            sys.syndromeProjector (syndromeXor δ₀ σ₀)) * (B ξ₀ * sys.syndromeProjector σ₀) := by
          rw [mul_assoc, h_abs_ξ₀]
      _ = ((tl.reverse.map B).prod * sys.syndromeProjector (syndromeXor δ₀ σ₀)) *
            (B ξ₀ * sys.syndromeProjector σ₀) := by
          rw [h_ih]
      _ = ((ξ₀ :: tl).reverse.map B).prod * sys.syndromeProjector σ₀ := by
          rw [mul_assoc (tl.reverse.map B).prod, h_abs_ξ₀, ← mul_assoc, ← h_prod_rev]

private lemma filter_eq_of_strictMono_surj {α : Type*} (p : α → Bool)
    (l : List α) :
    ∀ (r : List α) (idx : Fin l.length → ℕ),
      (∀ j : Fin l.length, p l[j.1] = true →
        ∃ h_lt : idx j < r.length, l[j.1] = r[idx j]'h_lt) →
      (∀ j₁ j₂ : Fin l.length, j₁ < j₂ → p l[j₁.1] = true → p l[j₂.1] = true →
        idx j₁ < idx j₂) →
      (∀ i : Fin r.length, ∃ j : Fin l.length, p l[j.1] = true ∧ idx j = i.1) →
      l.filter p = r := by
  induction l with
  | nil =>
    intro r _ _ _ h_surj
    cases r with
    | nil => rfl
    | cons _ _ =>
      rcases h_surj ⟨0, Nat.succ_pos _⟩ with ⟨j, _⟩
      exact Fin.elim0 j
  | cons hd tl ih =>
    intro r idx h_get h_mono h_surj
    cases hp : p hd with
    | false =>
      rw [List.filter_cons_of_neg (by simp [hp])]
      refine ih r (fun j => idx j.succ)
        (fun j hj => h_get j.succ hj)
        (fun j₁ j₂ h_lt hj₁ hj₂ => h_mono j₁.succ j₂.succ (Fin.succ_lt_succ_iff.mpr h_lt) hj₁ hj₂)
        (fun i => ?_)
      rcases h_surj i with ⟨j, hj_p, hj_eq⟩
      cases j using Fin.cases with
      | zero => simp [hp] at hj_p
      | succ j' => exact ⟨j', hj_p, hj_eq⟩
    | true =>
      rw [List.filter_cons_of_pos hp]
      let z0 : Fin (hd :: tl).length := ⟨0, Nat.succ_pos _⟩
      have h0_p : p (hd :: tl)[z0.1] = true := hp
      rcases h_get z0 h0_p with ⟨h0_lt, h0_eq⟩
      cases r with
      | nil => cases h0_lt
      | cons r_hd r_tl =>
        have h_idx0 : idx z0 = 0 := by
          rcases h_surj ⟨0, Nat.succ_pos _⟩ with ⟨j, hj_p, hj_eq⟩
          by_contra h_ne
          cases j using Fin.cases with
          | zero => exact h_ne hj_eq
          | succ j' =>
            have h_lt := h_mono z0 j'.succ (Fin.succ_pos j') h0_p hj_p
            have hj_eq' : idx j'.succ = 0 := hj_eq
            omega
        have h_hd_eq : hd = r_hd := by
          have h0_eq' : hd = (r_hd :: r_tl)[idx z0]'h0_lt := h0_eq
          simpa [h_idx0] using h0_eq'
        rw [h_hd_eq, List.cons.injEq]
        refine ⟨rfl, ?_⟩
        have h_succ_pos : ∀ j : Fin tl.length, p tl[j.1] = true → 0 < idx j.succ := fun j hj => by
          rw [← h_idx0]; exact h_mono z0 j.succ (Fin.succ_pos j) h0_p hj
        refine ih r_tl (fun j => idx j.succ - 1)
          (fun j hj => ?_) (fun j₁ j₂ h_lt hj₁ hj₂ => ?_) (fun i => ?_)
        · rcases h_get j.succ hj with ⟨h_lt, h_eq⟩
          have h_pos := h_succ_pos j hj
          have h_lt' : idx j.succ - 1 < r_tl.length := by simp at h_lt; omega
          refine ⟨h_lt', ?_⟩
          let k0 := idx j.succ - 1
          have h_idx_eq : idx j.succ = k0 + 1 := by omega
          have h_eq' : (hd :: tl)[(j.succ).1] = (r_hd :: r_tl)[idx j.succ]'h_lt := h_eq
          simpa [h_idx_eq] using h_eq'
        · (try dsimp only)
          have h_m := h_mono j₁.succ j₂.succ (Fin.succ_lt_succ_iff.mpr h_lt) hj₁ hj₂
          have h_p1 := h_succ_pos j₁ hj₁
          omega
        · rcases h_surj i.succ with ⟨j, hj_p, hj_eq⟩
          cases j using Fin.cases with
          | zero =>
            have hj_eq' : idx z0 = i.1 + 1 := hj_eq
            omega
          | succ j' =>
            refine ⟨j', hj_p, ?_⟩
            (try dsimp only)
            have hj_eq' : idx j'.succ = i.1 + 1 := hj_eq
            omega

/-!
## 2. Connected-Component Decomposition of Active Mayer Configurations
-/

private def worldlineDysonRawClusterWeight
    {L q_code r_0 m_max : ℕ} [NeZero L]
    (D_field : Box3D L → LocalCSSDescriptor q_code r_0 m_max)
    (sys : SysCSS[L, q_code, m_max]) (C_RCA : ℝ) (R_cut : ℕ) (β : ℝ)
    (V : QuasiLocalPerturbation 3 L (SiteCSS[L, q_code]))
    (d_loc : ℕ → Finset (Box3D L) → (IdxCSS[L, q_code, m_max] → Bool) → ℝ)
    (σ₀ : IdxCSS[L, q_code, m_max] → Bool)
    (K : WorldlineUrsellCluster L q_code) : ℝ :=
  if (∀ γ ∈ K, IsValidWorldlinePolymer D_field sys C_RCA R_cut γ) ∧
      K.Pairwise (fun γ₁ γ₂ => ¬ArePolymersIncompatible sys C_RCA γ₁ γ₂) then
    ((Nat.factorial K.length : ℝ)⁻¹) *
      (hilbertTrace (sys.syndromeProjector σ₀ *
        (K.map (worldlinePolymerWeightedLoopOp D_field sys V)).prod) /
        hilbertTrace (sys.syndromeProjector σ₀)) *
      (K.map (fun γ =>
        ((-1 : ℝ) ^ γ.1.length) *
          ∫ τ : Fin γ.1.length → ℝ,
            if InOrderedDysonSimplex β τ then
              Real.exp (-worldlineBareAction D_field sys γ.1 σ₀ β τ) *
                ∏ ϑ ∈ γ.2, worldlineMayerBondFactor D_field γ.1 d_loc σ₀ β ϑ τ
            else 0)).prod
  else 0

private def validClusterFinsetOfLenAndTotalJump
    {L q_code r_0 m_max : ℕ} [NeZero L]
    (D_field : Box3D L → LocalCSSDescriptor q_code r_0 m_max)
    (sys : SysCSS[L, q_code, m_max]) (C_RCA : ℝ) (R_cut m p : ℕ) :
    Finset (WorldlineUrsellCluster L q_code) :=
  let P_le := (Finset.range (m + 1)).biUnion (worldlinePolymerFinsetOfLength D_field R_cut)
  ((Fintype.piFinset (fun _ : Fin p => P_le)).image List.ofFn).filter (fun K =>
    (K.map (fun γ => γ.1.length)).sum = m ∧
    (∀ γ ∈ K, IsValidWorldlinePolymer D_field sys C_RCA R_cut γ) ∧
    K.Pairwise (fun γ₁ γ₂ => ¬ArePolymersIncompatible sys C_RCA γ₁ γ₂))

private lemma length_le_sum_jump_length_of_valid
    {L q_code r_0 m_max R_cut : ℕ} [NeZero L] {C_RCA : ℝ}
    (D_field : Box3D L → LocalCSSDescriptor q_code r_0 m_max)
    (sys : SysCSS[L, q_code, m_max])
    (K : WorldlineUrsellCluster L q_code)
    (hK : ∀ γ ∈ K, IsValidWorldlinePolymer D_field sys C_RCA R_cut γ) :
    K.length ≤ (K.map (fun γ => γ.1.length)).sum := by
  induction K with
  | nil => simp
  | cons hd tl ih =>
    have h_hd : 2 ≤ hd.1.length := (hK hd List.mem_cons_self).2.2.1.1
    have h_tl := ih (fun γ hγ => hK γ (List.mem_cons_of_mem hd hγ))
    simp only [List.length_cons, List.map_cons, List.sum_cons]
    omega

private lemma mem_validClusterFinsetOfLenAndTotalJump_iff
    {L q_code r_0 m_max : ℕ} [NeZero L]
    (D_field : Box3D L → LocalCSSDescriptor q_code r_0 m_max)
    (sys : SysCSS[L, q_code, m_max]) (C_RCA : ℝ) (R_cut m p : ℕ)
    (K : WorldlineUrsellCluster L q_code) :
    K ∈ validClusterFinsetOfLenAndTotalJump D_field sys C_RCA R_cut m p ↔
      K.length = p ∧
      (K.map (fun γ => γ.1.length)).sum = m ∧
      (∀ γ ∈ K, IsValidWorldlinePolymer D_field sys C_RCA R_cut γ) ∧
      K.Pairwise (fun γ₁ γ₂ => ¬ArePolymersIncompatible sys C_RCA γ₁ γ₂) := by
  unfold validClusterFinsetOfLenAndTotalJump
  rw [Finset.mem_filter, Finset.mem_image]
  constructor
  · rintro ⟨⟨g, _, rfl⟩, h_sum, h_val, h_pw⟩
    exact ⟨List.length_ofFn, h_sum, h_val, h_pw⟩
  · rintro ⟨h_len, h_sum, h_val, h_pw⟩
    refine ⟨⟨fun i : Fin p => K.get (i.cast h_len.symm), Fintype.mem_piFinset.mpr fun i => ?_, ?_⟩,
      h_sum, h_val, h_pw⟩
    · let γ := K.get (i.cast h_len.symm)
      have hγ_in : γ ∈ K := List.get_mem K (i.cast h_len.symm)
      have hγ_le : γ.1.length ≤ m := by
        rw [← h_sum]
        exact List.le_sum_of_mem (List.mem_map_of_mem hγ_in)
      exact Finset.mem_biUnion.mpr ⟨γ.1.length, Finset.mem_range.mpr (Nat.lt_succ_of_le hγ_le),
        mem_worldlinePolymerFinsetOfLength_of_isValidWorldlinePolymer D_field sys (h_val γ hγ_in)⟩
    · refine List.ext_getElem (by simp [h_len]) fun i h1 h2 => ?_
      simp

private lemma sum_validClusterFinset_multiPolymer_eq_raw
    {L q_code r_0 m_max L_star R_cut m p : ℕ} [NeZero L]
    {C_RCA β : ℝ} (hC_RCA : 1 ≤ C_RCA) (hβ_nn : 0 ≤ β) (hR_le : R_cut ≤ L_star)
    (D_field : Box3D L → LocalCSSDescriptor q_code r_0 m_max) (h_valid : ValidDescriptorField D_field)
    (sys : SysCSS[L, q_code, m_max])
    (h_sys_checks : ∀ idx, sys.checkProj idx = staticCSSCheckProj D_field idx ∧
      sys.support idx = staticCSSCheckSupport D_field idx ∧ sys.weight idx = 1)
    (h_tqo1 : SatisfiesTQO1 sys L_star)
    (h_tqo2 : SatisfiesSectorFilteredLinearTQO2 sys 1 L_star C_RCA)
    (V : QuasiLocalPerturbation 3 L (SiteCSS[L, q_code]))
    (d_loc : ℕ → Finset (Box3D L) → (IdxCSS[L, q_code, m_max] → Bool) → ℝ)
    {σ₀ : IdxCSS[L, q_code, m_max] → Bool} (hσ₀ : σ₀ ∈ realizableSyndromes D_field) :
    (∑ K ∈ validClusterFinsetOfLenAndTotalJump D_field sys C_RCA R_cut m p,
      worldlineDysonMultiPolymerClusterWeight D_field sys C_RCA R_cut β V d_loc σ₀ K) =
    (∑ K ∈ validClusterFinsetOfLenAndTotalJump D_field sys C_RCA R_cut m p,
      worldlineDysonRawClusterWeight D_field sys C_RCA R_cut β V d_loc σ₀ K) ∧
    (∑ K ∈ validClusterFinsetOfLenAndTotalJump D_field sys C_RCA R_cut m p,
      |worldlineDysonMultiPolymerClusterWeight D_field sys C_RCA R_cut β V d_loc σ₀ K|) ≤
    ∑ K ∈ validClusterFinsetOfLenAndTotalJump D_field sys C_RCA R_cut m p,
      |worldlineDysonRawClusterWeight D_field sys C_RCA R_cut β V d_loc σ₀ K| := by
  let S_cl := validClusterFinsetOfLenAndTotalJump D_field sys C_RCA R_cut m p
  have h_flip_mem : ∀ (b : Fin p → Bool) {K : WorldlineUrsellCluster L q_code},
      K ∈ S_cl → flipCluster b K ∈ S_cl := by
    intro b K hK
    rcases (mem_validClusterFinsetOfLenAndTotalJump_iff D_field sys C_RCA R_cut m p K).mp hK with
      ⟨h_len, h_sum, h_val, h_pw⟩
    rcases flipCluster_invariants hβ_nn D_field sys d_loc σ₀ b K h_len with ⟨h_flen, _, h_fsum, _, h_frest⟩
    rcases h_frest h_val with ⟨h_fval, h_fpw_iff, _⟩
    exact (mem_validClusterFinsetOfLenAndTotalJump_iff D_field sys C_RCA R_cut m p _).mpr
      ⟨h_flen, h_fsum.trans h_sum, h_fval, h_fpw_iff.mpr h_pw⟩
  have h_pt : ∀ K ∈ S_cl,
      (worldlineDysonMultiPolymerClusterWeight D_field sys C_RCA R_cut β V d_loc σ₀ K =
        ∑ b : Fin p → Bool,
          ((2 : ℝ) ^ p)⁻¹ * worldlineDysonRawClusterWeight D_field sys C_RCA R_cut β V d_loc σ₀ (flipCluster b K)) ∧
      (|worldlineDysonMultiPolymerClusterWeight D_field sys C_RCA R_cut β V d_loc σ₀ K| ≤
        ∑ b : Fin p → Bool,
          ((2 : ℝ) ^ p)⁻¹ * |worldlineDysonRawClusterWeight D_field sys C_RCA R_cut β V d_loc σ₀ (flipCluster b K)|) := by
    intro K hK
    rcases (mem_validClusterFinsetOfLenAndTotalJump_iff D_field sys C_RCA R_cut m p K).mp hK with ⟨h_len, _, h_val, h_pw⟩
    let I_prod := (K.map (fun γ =>
      ((-1 : ℝ) ^ γ.1.length) * ∫ τ : Fin γ.1.length → ℝ,
        if InOrderedDysonSimplex β τ then
          Real.exp (-worldlineBareAction D_field sys γ.1 σ₀ β τ) *
            ∏ ϑ ∈ γ.2, worldlineMayerBondFactor D_field γ.1 d_loc σ₀ β ϑ τ
        else 0)).prod
    have h_raw_b : ∀ b : Fin p → Bool,
        worldlineDysonRawClusterWeight D_field sys C_RCA R_cut β V d_loc σ₀ (flipCluster b K) =
          ((Nat.factorial p : ℝ)⁻¹) *
            (hilbertTrace (sys.syndromeProjector σ₀ *
              ((flipCluster b K).map (worldlinePolymerWeightedLoopOp D_field sys V)).prod) /
              hilbertTrace (sys.syndromeProjector σ₀)) * I_prod := by
      intro b
      rcases flipCluster_invariants hβ_nn D_field sys d_loc σ₀ b K h_len with ⟨h_flen, _, _, _, h_frest⟩
      rcases h_frest h_val with ⟨h_fval, h_fpw_iff, h_fint⟩
      unfold worldlineDysonRawClusterWeight
      rw [if_pos ⟨h_fval, h_fpw_iff.mpr h_pw⟩, h_flen, h_fint]
    unfold worldlineDysonMultiPolymerClusterWeight
    rw [if_pos ⟨h_val, h_pw⟩]
    by_cases h_comm : ∀ ν ∈ syndromeClosedPauliFinset D_field,
        symplecticPauliSign ν (K.map (fun γ => (worldlinePolymerLoopX γ, worldlinePolymerLoopZ γ))).sum = 1
    · rw [if_pos h_comm, h_len]
      have h_idem := ((PerturbedThermalBarrier.syndrome_resolution_indexed sys).2.1 σ₀).1
      have h_avg_prod := list_prod_avg_weightedLoopOp_mul_syndromeProjector_eq_symmetrized
        hC_RCA D_field h_valid sys h_sys_checks h_tqo1 h_tqo2 hR_le V K h_val h_pw h_comm hσ₀
      have h_tr_sym :
          hilbertTrace (sys.syndromeProjector σ₀ *
            (K.map (worldlinePolymerSymmetrizedWeightedLoopOp D_field sys C_RCA V)).prod) =
          hilbertTrace (sys.syndromeProjector σ₀ *
            (K.map (fun γ => (1 / 2 : ℂ) •
              (worldlinePolymerWeightedLoopOp D_field sys V γ +
                worldlinePolymerWeightedLoopOp D_field sys V (γ.1.reverse, γ.2)))).prod) := by
        rw [← h_idem, mul_assoc, hilbertTrace_mul_comm_aux (sys.syndromeProjector σ₀) _, mul_assoc,
          ← h_avg_prod, ← mul_assoc (sys.syndromeProjector σ₀),
          hilbertTrace_mul_comm_aux _ (sys.syndromeProjector σ₀), ← mul_assoc]
      let f₀ : Fin p → ℬ_CSS[L, q_code] := fun i => worldlinePolymerWeightedLoopOp D_field sys V (K.get (i.cast h_len.symm))
      let f₁ : Fin p → ℬ_CSS[L, q_code] := fun i => worldlinePolymerWeightedLoopOp D_field sys V
        ((K.get (i.cast h_len.symm)).1.reverse, (K.get (i.cast h_len.symm)).2)
      have h_map_ofFn :
          K.map (fun γ => (1 / 2 : ℂ) • (worldlinePolymerWeightedLoopOp D_field sys V γ +
            worldlinePolymerWeightedLoopOp D_field sys V (γ.1.reverse, γ.2))) =
          List.ofFn (fun i : Fin p => (1 / 2 : ℂ) • (f₀ i + f₁ i)) := by
        refine List.ext_getElem (by simp [h_len]) fun i h1 h2 => ?_; simp [f₀, f₁]
      have h_flip_map : ∀ b : Fin p → Bool,
          List.ofFn (fun i : Fin p => if b i then f₁ i else f₀ i) =
            (flipCluster b K).map (worldlinePolymerWeightedLoopOp D_field sys V) := by
        intro b; dsimp [flipCluster]
        refine List.ext_getElem (by simp) fun i h1 h2 => ?_
        let idx : Fin p := ⟨i, by simpa using h1⟩
        rw [List.getElem_ofFn, List.getElem_map, List.getElem_ofFn]; dsimp [f₀, f₁]
        rw [dif_pos (h_len.symm ▸ idx.2)]; cases b idx <;> rfl
      have h_tr_sum :
          hilbertTrace (sys.syndromeProjector σ₀ *
            (K.map (worldlinePolymerSymmetrizedWeightedLoopOp D_field sys C_RCA V)).prod) =
          ∑ b : Fin p → Bool, ((2 : ℝ) ^ p)⁻¹ *
            hilbertTrace (sys.syndromeProjector σ₀ *
              ((flipCluster b K).map (worldlinePolymerWeightedLoopOp D_field sys V)).prod) := by
        rw [h_tr_sym, h_map_ofFn, list_ofFn_prod_avg_eq_sum_bool_tuple p f₀ f₁,
          Finset.mul_sum, hilbertTrace_sum]
        refine Finset.sum_congr rfl fun b _ => ?_
        rw [h_flip_map b, clm_mul_smul,
          (hilbertTrace_add_and_complex_smul_decomp _ 0 0 0 (((2 : ℝ) ^ p)⁻¹) 0).2.1]
      have h_eq : ((Nat.factorial p : ℝ)⁻¹) *
          (hilbertTrace (sys.syndromeProjector σ₀ *
            (K.map (worldlinePolymerSymmetrizedWeightedLoopOp D_field sys C_RCA V)).prod) /
            hilbertTrace (sys.syndromeProjector σ₀)) * I_prod =
          ∑ b : Fin p → Bool, ((2 : ℝ) ^ p)⁻¹ *
            worldlineDysonRawClusterWeight D_field sys C_RCA R_cut β V d_loc σ₀ (flipCluster b K) := by
        rw [h_tr_sum, Finset.sum_div, Finset.mul_sum, Finset.sum_mul]
        refine Finset.sum_congr rfl fun b _ => ?_
        rw [h_raw_b b]; ring
      refine ⟨h_eq, ?_⟩
      change |((Nat.factorial p : ℝ)⁻¹) *
          (hilbertTrace (sys.syndromeProjector σ₀ *
            (K.map (worldlinePolymerSymmetrizedWeightedLoopOp D_field sys C_RCA V)).prod) /
            hilbertTrace (sys.syndromeProjector σ₀)) * I_prod| ≤ _
      rw [h_eq]
      refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun b _ => ?_)
      rw [abs_mul, abs_of_pos (by positivity)]
    · rw [if_neg h_comm, abs_zero]
      refine ⟨?_, Finset.sum_nonneg fun _ _ => mul_nonneg (by positivity) (abs_nonneg _)⟩
      symm; refine Finset.sum_eq_zero fun b _ => ?_
      rcases flipCluster_invariants hβ_nn D_field sys d_loc σ₀ b K h_len with ⟨_, _, _, h_floop, h_frest⟩
      rcases h_frest h_val with ⟨h_fval, _, _⟩
      have h_not_comm_b : ¬∀ ν ∈ syndromeClosedPauliFinset D_field,
          symplecticPauliSign ν
            ((flipCluster b K).map (fun γ => (worldlinePolymerLoopX γ, worldlinePolymerLoopZ γ))).sum = 1 := by
        rwa [h_floop]
      have h_tr0 := (multiPolymer_trace_and_character_average_eq_zero_of_anticomm (β := β)
        D_field h_valid sys h_sys_checks h_tqo1 h_tqo2 hR_le V d_loc (flipCluster b K) h_fval hσ₀ h_not_comm_b).1
      rw [h_raw_b b, h_tr0, zero_div, mul_zero, zero_mul, mul_zero]
  have h_bij_sum : ∀ (g : WorldlineUrsellCluster L q_code → ℝ),
      (∑ b : Fin p → Bool, ∑ K ∈ S_cl, ((2 : ℝ) ^ p)⁻¹ * g (flipCluster b K)) =
      ∑ K ∈ S_cl, g K := by
    intro g
    have h_bij_b : ∀ b : Fin p → Bool,
        (∑ K ∈ S_cl, ((2 : ℝ) ^ p)⁻¹ * g (flipCluster b K)) = ((2 : ℝ) ^ p)⁻¹ * ∑ K ∈ S_cl, g K := by
      intro b; rw [← Finset.mul_sum]; congr 1
      refine Finset.sum_bij (fun K _ => flipCluster b K) (fun K hK => h_flip_mem b hK)
        (fun K₁ hK₁ K₂ hK₂ h_eq => ?_) (fun K hK => ?_) (fun _ _ => rfl)
      · have h_len₁ := ((mem_validClusterFinsetOfLenAndTotalJump_iff D_field sys C_RCA R_cut m p K₁).mp hK₁).1
        have h_len₂ := ((mem_validClusterFinsetOfLenAndTotalJump_iff D_field sys C_RCA R_cut m p K₂).mp hK₂).1
        have h_inv₁ := (flipCluster_invariants (C_RCA := C_RCA) (R_cut := R_cut) hβ_nn D_field sys d_loc σ₀ b K₁ h_len₁).2.1
        have h_inv₂ := (flipCluster_invariants (C_RCA := C_RCA) (R_cut := R_cut) hβ_nn D_field sys d_loc σ₀ b K₂ h_len₂).2.1
        exact h_inv₁.symm.trans ((congrArg (flipCluster b) h_eq).trans h_inv₂)
      · have h_len := ((mem_validClusterFinsetOfLenAndTotalJump_iff D_field sys C_RCA R_cut m p K).mp hK).1
        exact ⟨flipCluster b K, h_flip_mem b hK,
          (flipCluster_invariants (C_RCA := C_RCA) (R_cut := R_cut) hβ_nn D_field sys d_loc σ₀ b K h_len).2.1⟩
    rw [Finset.sum_congr rfl (fun b _ => h_bij_b b), ← Finset.sum_mul,
      Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_fin, Fintype.card_bool, nsmul_eq_mul]
    push_cast
    rw [mul_inv_cancel₀ (pow_ne_zero p (by norm_num)), one_mul]
  refine ⟨?_, ?_⟩
  · rw [Finset.sum_congr rfl (fun K hK => (h_pt K hK).1), Finset.sum_comm, h_bij_sum]
  · refine (Finset.sum_le_sum fun K hK => (h_pt K hK).2).trans ?_
    rw [Finset.sum_comm, h_bij_sum (fun K => |worldlineDysonRawClusterWeight D_field sys C_RCA R_cut β V d_loc σ₀ K|)]

private lemma list_prod_mul_eq_prod_mul_prod {α β_m : Type*} [CommMonoid β_m]
    (l : List α) (f g : α → β_m) :
    (l.map (fun x => f x * g x)).prod = (l.map f).prod * (l.map g).prod := by
  induction l with
  | nil => simp
  | cons hd tl ih =>
    rw [List.map_cons, List.prod_cons, ih, List.map_cons, List.prod_cons,
      List.map_cons, List.prod_cons]
    simp only [mul_assoc, mul_left_comm (g hd)]

private lemma worldlineDysonRawClusterWeight_eq_sum_multiPolymerShuffleFinset
    {L q_code r_0 m_max w_0 R_cut : ℕ} [NeZero L]
    {C_RCA β : ℝ} (hr0_le : 1 + 4 * (r_0 : ℝ) ≤ C_RCA) (hC_RCA : 1 ≤ C_RCA)
    (D_field : Box3D L → LocalCSSDescriptor q_code r_0 m_max)
    (sys : SysCSS[L, q_code, m_max])
    (h_sys_checks : ∀ idx, sys.checkProj idx = staticCSSCheckProj D_field idx ∧
      sys.support idx = staticCSSCheckSupport D_field idx ∧ sys.weight idx = 1)
    (h_geom : sys.IsGeometricallyLocal r_0 w_0)
    (V : QuasiLocalPerturbation 3 L (SiteCSS[L, q_code]))
    (d_loc : ℕ → Finset (Box3D L) → (IdxCSS[L, q_code, m_max] → Bool) → ℝ)
    (hd_collar : ∀ r ∈ Finset.Icc 1 (min R_cut L), ∀ A ∈ boxCubes 3 L r,
      ∀ σ₁ σ₂, restrictSyndromeToCollar (rcaCollarChecks sys C_RCA r A) σ₁ =
        restrictSyndromeToCollar (rcaCollarChecks sys C_RCA r A) σ₂ →
        d_loc r A σ₁ = d_loc r A σ₂)
    {σ₀ : IdxCSS[L, q_code, m_max] → Bool} (hσ₀ : σ₀ ∈ realizableSyndromes D_field)
    (K : WorldlineUrsellCluster L q_code)
    (hK_valid : ∀ γ ∈ K, IsValidWorldlinePolymer D_field sys C_RCA R_cut γ)
    (hK_pw : K.Pairwise (fun γ₁ γ₂ => ¬ArePolymersIncompatible sys C_RCA γ₁ γ₂)) :
    worldlineDysonRawClusterWeight D_field sys C_RCA R_cut β V d_loc σ₀ K =
      ((Nat.factorial K.length : ℝ)⁻¹) *
        ∑ ξ_list ∈ multiPolymerShuffleFinset D_field R_cut K,
          ((-1 : ℝ) ^ ξ_list.length) *
            (hilbertTrace (sys.syndromeProjector σ₀ *
              worldlinePolymerWeightedLoopOp D_field sys V
                (ξ_list, K.foldr (fun γ acc => γ.2 ∪ acc) ∅)) /
              hilbertTrace (sys.syndromeProjector σ₀)) *
            ∫ τ : Fin ξ_list.length → ℝ,
              if InOrderedDysonSimplex β τ then
                Real.exp (-worldlineBareAction D_field sys ξ_list σ₀ β τ) *
                  ∏ ϑ ∈ K.foldr (fun γ acc => γ.2 ∪ acc) ∅,
                    worldlineMayerBondFactor D_field ξ_list d_loc σ₀ β ϑ τ
              else 0 := by
  let P : Fin K.length → WorldlineJumpMonomer L q_code → Bool :=
    fun a ξ => decide (ξ ∈ (K.get a).1)
  have h_pw_get := List.pairwise_iff_get.mp hK_pw
  have h_disj_col : ∀ a b : Fin K.length, a ≠ b →
      Disjoint (worldlinePolymerNativeCollar sys C_RCA (K.get a))
        (worldlinePolymerNativeCollar sys C_RCA (K.get b)) := by
    intro a b hab
    rcases lt_or_gt_of_ne hab with h_lt | h_gt
    · exact not_not.mp (h_pw_get a b h_lt)
    · exact (not_not.mp (h_pw_get b a h_gt)).symm
  have h_disj_rca : ∀ a b : Fin K.length, a ≠ b →
      ∀ ξ₁ ∈ (K.get a).1, ∀ ξ₂ ∈ (K.get b).1,
        Disjoint (rcaCollarChecks sys C_RCA ξ₁.1.1 ξ₁.1.2)
          (rcaCollarChecks sys C_RCA ξ₂.1.1 ξ₂.1.2) := by
    intro a b hab ξ₁ hξ₁ ξ₂ hξ₂
    have hp₁ : ξ₁.1 ∈ worldlinePolymerMonomers (K.get a) :=
      Finset.mem_union_left _ (List.mem_toFinset.mpr (List.mem_map_of_mem hξ₁))
    have hp₂ : ξ₂.1 ∈ worldlinePolymerMonomers (K.get b) :=
      Finset.mem_union_left _ (List.mem_toFinset.mpr (List.mem_map_of_mem hξ₂))
    exact Finset.disjoint_left.mpr fun c hc₁ hc₂ =>
      Finset.disjoint_left.mp (h_disj_col a b hab)
        (Finset.mem_biUnion.mpr ⟨ξ₁.1, hp₁, hc₁⟩)
        (Finset.mem_biUnion.mpr ⟨ξ₂.1, hp₂, hc₂⟩)
  have h_uniq_comp : ∀ a b : Fin K.length, ∀ ξ,
      ξ ∈ (K.get a).1 → ξ ∈ (K.get b).1 → a = b := by
    intro a b ξ hξa hξb
    by_contra hab
    have h_self_disj := h_disj_rca a b hab ξ hξa ξ hξb
    have hγ_a := hK_valid (K.get a) (List.get_mem K a)
    have h_flip_ne := (hγ_a.2.1 ξ hξa).2.1
    have h_ex_c : ∃ c : IdxCSS[L, q_code, m_max],
        staticCSSPauliFlip D_field ξ.2.1 ξ.2.2 c = true := by
      by_contra! h_all
      apply h_flip_ne
      funext c
      cases h_val : staticCSSPauliFlip D_field ξ.2.1 ξ.2.2 c
      · rfl
      · exact False.elim (h_all c h_val)
    rcases h_ex_c with ⟨c, hc⟩
    have hp_a : ξ.1 ∈ worldlinePolymerMonomers (K.get a) :=
      Finset.mem_union_left _ (List.mem_toFinset.mpr (List.mem_map_of_mem hξa))
    rcases mem_scaleCubeFinset_iff.mp (hγ_a.1 ξ.1 hp_a) with ⟨hr, hA⟩
    have hc_int := staticCSSPauliFlip_mem_cubeIntersectingChecks
      D_field sys (fun idx => (h_sys_checks idx).2.1) ξ.1.2 ξ.2.1 ξ.2.2
      (hγ_a.2.1 ξ hξa).1 c hc
    have hc_rca := cubeIntersectingChecks_subset_rcaCollarChecks sys h_geom hr0_le
      (Finset.mem_Icc.mp hr).1 hA hc_int
    exact Finset.disjoint_left.mp h_self_disj hc_rca hc_rca
  have h_tr_eq : ∀ ξ_list ∈ multiPolymerShuffleFinset D_field R_cut K,
      hilbertTrace (sys.syndromeProjector σ₀ *
        worldlinePolymerWeightedLoopOp D_field sys V
          (ξ_list, K.foldr (fun γ acc => γ.2 ∪ acc) ∅)) =
      hilbertTrace (sys.syndromeProjector σ₀ *
        (K.map (worldlinePolymerWeightedLoopOp D_field sys V)).prod) := by
    intro ξ_list hξ
    rcases Finset.mem_filter.mp hξ with ⟨h_mem_len, owner, idx, h_mono, h_surj, h_getD⟩
    have h_len_ξ : ξ_list.length = (K.map (fun γ => γ.1.length)).sum := by
      rcases Finset.mem_image.mp h_mem_len with ⟨f_ξ, _, rfl⟩
      simp
    let owner' : Fin ξ_list.length → Fin K.length := fun j => owner (j.cast h_len_ξ)
    let idx' : ∀ j : Fin ξ_list.length, Fin (K.get (owner' j)).1.length :=
      fun j => idx (j.cast h_len_ξ)
    have h_elem : ∀ j : Fin ξ_list.length,
        ξ_list[j.1] = (K.get (owner' j)).1[(idx' j).1]'(idx' j).2 := by
      intro j
      have hj := h_getD (j.cast h_len_ξ)
      change ξ_list.getD j.1 _ = (K.get (owner' j)).1[(idx' j).1]'(idx' j).2 at hj
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem j.2, Option.getD_some] at hj
      exact hj
    have hP_iff : ∀ (a : Fin K.length) (j : Fin ξ_list.length),
        P a (ξ_list[j.1]) = true ↔ owner' j = a := by
      intro a j
      dsimp [P]
      rw [decide_eq_true_iff]
      constructor
      · intro h_in
        exact (h_uniq_comp a (owner' j) (ξ_list[j.1]) h_in
          (h_elem j ▸ List.getElem_mem (idx' j).2)).symm
      · rintro rfl
        rw [h_elem j]
        exact List.getElem_mem (idx' j).2
    have h_flt_a : ∀ a : Fin K.length, ξ_list.filter (P a) = (K.get a).1 := by
      intro a
      refine filter_eq_of_strictMono_surj (P a) ξ_list (K.get a).1 (fun j => (idx' j).1)
        (fun j hj => ?_) (fun j₁ j₂ h_lt hj₁ hj₂ => ?_) (fun i => ?_)
      · have h_own : owner' j = a := (hP_iff a j).mp hj
        refine ⟨h_own ▸ (idx' j).2, ?_⟩
        cases h_own
        exact h_elem j
      · exact h_mono (j₁.cast h_len_ξ) (j₂.cast h_len_ξ) h_lt
          (((hP_iff a j₁).mp hj₁).trans ((hP_iff a j₂).mp hj₂).symm)
      · rcases h_surj a i with ⟨j, hj_own, hj_idx⟩
        let j' : Fin ξ_list.length := j.cast h_len_ξ.symm
        exact ⟨j', (hP_iff a j').mpr hj_own, hj_idx⟩
    have h_ofFn_map :
        ((List.ofFn (fun a : Fin K.length => ξ_list.filter (P a))).map
          (fun l => (l.reverse.map (worldlineSyndromeShiftBlockOp D_field sys V)).prod)) =
        K.map (worldlinePolymerWeightedLoopOp D_field sys V) := by
      refine List.ext_getElem (by simp) fun i h1 h2 => ?_
      rw [List.getElem_map, List.getElem_ofFn, List.getElem_map, h_flt_a ⟨i, by simpa using h2⟩]
      rfl
    have h_mem_comp : ∀ ξ ∈ ξ_list, ∃ a : Fin K.length, ξ ∈ (K.get a).1 := by
      intro ξ hξ_in
      rcases List.mem_iff_getElem.mp hξ_in with ⟨n, hn, rfl⟩
      exact ⟨owner' ⟨n, hn⟩, h_elem ⟨n, hn⟩ ▸ List.getElem_mem (idx' ⟨n, hn⟩).2⟩
    have h_jumps : ∀ ξ ∈ ξ_list, ξ.1.2 ∈ boxCubes 3 L ξ.1.1 ∧
        IsSupportedOn (SiteCSS[L, q_code]) ξ.1.2 (V.term ξ.1.1 ξ.1.2) ∧
        staticCSSPauliFlip D_field ξ.2.1 ξ.2.2 ≠ (fun _ => false) := by
      intro ξ hξ_in
      rcases h_mem_comp ξ hξ_in with ⟨a, hξa⟩
      have hγ_a := hK_valid (K.get a) (List.get_mem K a)
      have hp_a : ξ.1 ∈ worldlinePolymerMonomers (K.get a) :=
        Finset.mem_union_left _ (List.mem_toFinset.mpr (List.mem_map_of_mem hξa))
      rcases mem_scaleCubeFinset_iff.mp (hγ_a.1 ξ.1 hp_a) with ⟨hr, hA⟩
      have hV_supp : IsSupportedOn (SiteCSS[L, q_code]) ξ.1.2 (V.term ξ.1.1 ξ.1.2) :=
        V.is_supported ξ.1.1 (Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp hr).1,
          le_trans (Finset.mem_Icc.mp hr).2 (Nat.min_le_right R_cut L)⟩) ξ.1.2 hA
      exact ⟨hA, hV_supp, (hγ_a.2.1 ξ hξa).2.1⟩
    have h_op_eq := prodJumpLists_of_filter_partition_eq D_field sys h_sys_checks hC_RCA V
      K.length P ξ_list h_jumps
      (fun ξ hξ_in => by
        rcases h_mem_comp ξ hξ_in with ⟨a, hξa⟩
        exact ⟨a, decide_eq_true hξa⟩)
      (fun ξ _ a b ha hb => h_uniq_comp a b ξ (of_decide_eq_true ha) (of_decide_eq_true hb))
      (fun ξ₁ _ ξ₂ _ a b hab ha hb =>
        h_disj_rca a b hab ξ₁ (of_decide_eq_true ha) ξ₂ (of_decide_eq_true hb))
      hσ₀
    rw [h_ofFn_map] at h_op_eq
    have h_idem := ((PerturbedThermalBarrier.syndrome_resolution_indexed sys).2.1 σ₀).1
    change hilbertTrace (sys.syndromeProjector σ₀ *
        (ξ_list.reverse.map (worldlineSyndromeShiftBlockOp D_field sys V)).prod) =
      hilbertTrace (sys.syndromeProjector σ₀ *
        (K.map (worldlinePolymerWeightedLoopOp D_field sys V)).prod)
    calc hilbertTrace (sys.syndromeProjector σ₀ *
          (ξ_list.reverse.map (worldlineSyndromeShiftBlockOp D_field sys V)).prod)
      _ = hilbertTrace ((sys.syndromeProjector σ₀ * sys.syndromeProjector σ₀) *
            (ξ_list.reverse.map (worldlineSyndromeShiftBlockOp D_field sys V)).prod) := by rw [h_idem]
      _ = hilbertTrace (sys.syndromeProjector σ₀ *
            ((ξ_list.reverse.map (worldlineSyndromeShiftBlockOp D_field sys V)).prod *
              sys.syndromeProjector σ₀)) := by
          rw [mul_assoc, hilbertTrace_mul_comm_aux (sys.syndromeProjector σ₀) _, mul_assoc]
      _ = hilbertTrace (sys.syndromeProjector σ₀ *
            ((K.map (worldlinePolymerWeightedLoopOp D_field sys V)).prod *
              sys.syndromeProjector σ₀)) := by rw [← h_op_eq]
      _ = hilbertTrace ((sys.syndromeProjector σ₀ * sys.syndromeProjector σ₀) *
            (K.map (worldlinePolymerWeightedLoopOp D_field sys V)).prod) := by
          rw [← mul_assoc (sys.syndromeProjector σ₀),
            hilbertTrace_mul_comm_aux _ (sys.syndromeProjector σ₀), ← mul_assoc]
      _ = hilbertTrace (sys.syndromeProjector σ₀ *
            (K.map (worldlinePolymerWeightedLoopOp D_field sys V)).prod) := by rw [h_idem]
  rcases multiPolymer_shuffle_simplex_integral_factorization_of_compatible
      D_field sys h_sys_checks h_geom hr0_le hC_RCA d_loc hd_collar K hK_valid hK_pw σ₀ with
    ⟨h_sign_eq, h_int_eq⟩
  unfold worldlineDysonRawClusterWeight
  rw [if_pos ⟨hK_valid, hK_pw⟩]
  have h_prod_split := list_prod_mul_eq_prod_mul_prod K
    (fun γ => (-1 : ℝ) ^ γ.1.length)
    (fun γ => ∫ τ : Fin γ.1.length → ℝ,
      if InOrderedDysonSimplex β τ then
        Real.exp (-worldlineBareAction D_field sys γ.1 σ₀ β τ) *
          ∏ ϑ ∈ γ.2, worldlineMayerBondFactor D_field γ.1 d_loc σ₀ β ϑ τ
      else 0)
  rw [h_prod_split, ← h_int_eq, mul_assoc ((Nat.factorial K.length : ℝ)⁻¹),
    ← mul_assoc _ ((K.map (fun γ => (-1 : ℝ) ^ γ.1.length)).prod), Finset.mul_sum]
  congr 1
  refine Finset.sum_congr rfl fun ξ_list hξ => ?_
  rw [h_sign_eq ξ_list hξ, h_tr_eq ξ_list hξ]
  ring

private lemma mem_foldr_union_iff_exists_get {L q_code : ℕ}
    (K : WorldlineUrsellCluster L q_code) (ϑ : ℕ × Finset (Box3D L)) :
    ϑ ∈ K.foldr (fun γ acc => γ.2 ∪ acc) ∅ ↔ ∃ a : Fin K.length, ϑ ∈ (K.get a).2 := by
  induction K with
  | nil => simp
  | cons hd tl ih =>
    simp only [List.foldr_cons, Finset.mem_union, ih, List.length_cons]
    exact ⟨by rintro (h0 | ⟨a, ha⟩)
              · exact ⟨0, h0⟩
              · exact ⟨a.succ, ha⟩,
           by rintro ⟨a, ha⟩
              exact Fin.cases (fun h0 => Or.inl h0) (fun a' ha' => Or.inr ⟨a', ha'⟩) a ha⟩

private lemma cluster_shuffle_invariants
    {L q_code r_0 m_max w_0 R_cut m p : ℕ} [NeZero L] {C_RCA : ℝ}
    (D_field : Box3D L → LocalCSSDescriptor q_code r_0 m_max)
    (sys : SysCSS[L, q_code, m_max])
    (h_sys_supp : ∀ idx, sys.support idx = staticCSSCheckSupport D_field idx)
    (h_geom : sys.IsGeometricallyLocal r_0 w_0)
    (hr0_le : 1 + 4 * (r_0 : ℝ) ≤ C_RCA)
    (hm : 1 ≤ m)
    {K : WorldlineUrsellCluster L q_code}
    (hK : K ∈ validClusterFinsetOfLenAndTotalJump D_field sys C_RCA R_cut m p)
    {ξ_list : List (WorldlineJumpMonomer L q_code)}
    (hξ : ξ_list ∈ multiPolymerShuffleFinset D_field R_cut K) :
    let Θ := K.foldr (fun γ acc => γ.2 ∪ acc) ∅
    let M := (ξ_list.map Prod.fst).toFinset ∪ Θ
    ξ_list ∈ validClosedJumpListFinset D_field R_cut m ∧
    Θ ∈ connMayerFinset sys C_RCA R_cut ξ_list ∧
    (monomerComponents sys C_RCA M).card = p ∧
    ∃ f : Fin p → monomerComponents sys C_RCA M,
      Function.Bijective f ∧
      K = List.ofFn (fun a : Fin p => componentPolymer ξ_list Θ (f a).1) := by
  intro Θ M
  rcases (mem_validClusterFinsetOfLenAndTotalJump_iff D_field sys C_RCA R_cut m p K).mp hK with
    ⟨h_len, h_sum, hK_val, hK_pw⟩
  rcases Finset.mem_filter.mp hξ with ⟨h_mem_len, owner, idx, h_mono, h_surj, h_getD⟩
  have hξ_mem_m : ξ_list ∈ worldlineJumpListFinsetOfLength D_field R_cut m := h_sum ▸ h_mem_len
  have h_len_ξ : ξ_list.length = (K.map (fun γ => γ.1.length)).sum :=
    ((mem_worldlineJumpListFinsetOfLength_iff_local D_field R_cut m ξ_list).mp hξ_mem_m).1.trans h_sum.symm
  have h_pw_get := List.pairwise_iff_get.mp hK_pw
  have h_disj_col : ∀ a b : Fin K.length, a ≠ b →
      Disjoint (worldlinePolymerNativeCollar sys C_RCA (K.get a))
        (worldlinePolymerNativeCollar sys C_RCA (K.get b)) := by
    intro a b hab
    rcases lt_or_gt_of_ne hab with h_lt | h_gt
    · exact not_not.mp (h_pw_get a b h_lt)
    · exact (not_not.mp (h_pw_get b a h_gt)).symm
  have h_disj_mon : ∀ a b : Fin K.length, a ≠ b →
      Disjoint (worldlinePolymerMonomers (K.get a)) (worldlinePolymerMonomers (K.get b)) := by
    intro a b hab
    refine Finset.disjoint_left.mpr fun u hua hub => ?_
    rcases rcaCollarChecks_nonempty_of_mem_worldlinePolymerMonomers D_field sys h_sys_supp h_geom hr0_le
      (hK_val (K.get a) (List.get_mem K a)) hua with ⟨c, hc⟩
    exact Finset.disjoint_left.mp (h_disj_col a b hab)
      (Finset.mem_biUnion.mpr ⟨u, hua, hc⟩)
      (Finset.mem_biUnion.mpr ⟨u, hub, hc⟩)
  let owner' : Fin ξ_list.length → Fin K.length := fun j => owner (j.cast h_len_ξ)
  let idx' : ∀ j : Fin ξ_list.length, Fin (K.get (owner' j)).1.length :=
    fun j => idx (j.cast h_len_ξ)
  have h_elem : ∀ j : Fin ξ_list.length,
      ξ_list[j.1] = (K.get (owner' j)).1[(idx' j).1]'(idx' j).2 := by
    intro j
    have hj := h_getD (j.cast h_len_ξ)
    change ξ_list.getD j.1 _ = (K.get (owner' j)).1[(idx' j).1]'(idx' j).2 at hj
    rwa [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem j.2, Option.getD_some] at hj
  have h_mem_ξ_of_mem_a : ∀ (a : Fin K.length) {ξ}, ξ ∈ (K.get a).1 → ξ ∈ ξ_list := by
    intro a ξ hξa
    rcases List.mem_iff_getElem.mp hξa with ⟨i, hi, rfl⟩
    rcases h_surj a ⟨i, hi⟩ with ⟨j, hj_own, hj_idx⟩
    let j' : Fin ξ_list.length := j.cast h_len_ξ.symm
    have h_eq := h_elem j'
    have h_own' : owner' j' = a := hj_own
    have h_idx' : (idx' j').1 = i := hj_idx
    have h_get_eq : (K.get (owner' j')).1[(idx' j').1]'(idx' j').2 = (K.get a).1[i]'hi := by
      cases h_own'; congr 1
    rw [← h_get_eq, ← h_eq]
    exact List.getElem_mem j'.2
  let P : Fin K.length → WorldlineJumpMonomer L q_code → Bool :=
    fun a ξ => decide (ξ.1 ∈ worldlinePolymerMonomers (K.get a))
  have hP_iff : ∀ (a : Fin K.length) (j : Fin ξ_list.length),
      P a (ξ_list[j.1]) = true ↔ owner' j = a := by
    intro a j
    dsimp [P]; rw [decide_eq_true_iff]
    have hj_mem : (ξ_list[j.1]).1 ∈ worldlinePolymerMonomers (K.get (owner' j)) := by
      rw [h_elem j]
      exact Finset.mem_union_left _ (List.mem_toFinset.mpr (List.mem_map_of_mem (List.getElem_mem (idx' j).2)))
    refine ⟨fun h_in => ?_, by rintro rfl; exact hj_mem⟩
    by_contra h_ne
    exact Finset.disjoint_left.mp (h_disj_mon (owner' j) a h_ne) hj_mem h_in
  have h_flt_a : ∀ a : Fin K.length, (K.get a).1 = ξ_list.filter (P a) := by
    intro a; symm
    refine filter_eq_of_strictMono_surj (P a) ξ_list (K.get a).1 (fun j => (idx' j).1)
      (fun j hj => ?_) (fun j₁ j₂ h_lt hj₁ hj₂ => ?_) (fun i => ?_)
    · have h_own : owner' j = a := (hP_iff a j).mp hj
      refine ⟨h_own ▸ (idx' j).2, ?_⟩; cases h_own; exact h_elem j
    · exact h_mono (j₁.cast h_len_ξ) (j₂.cast h_len_ξ) h_lt
        (((hP_iff a j₁).mp hj₁).trans ((hP_iff a j₂).mp hj₂).symm)
    · rcases h_surj a i with ⟨j, hj_own, hj_idx⟩
      let j' : Fin ξ_list.length := j.cast h_len_ξ.symm
      exact ⟨j', (hP_iff a j').mpr hj_own, hj_idx⟩
  have h_mayer_a : ∀ a : Fin K.length,
      (K.get a).2 = Θ ∩ worldlinePolymerMonomers (K.get a) := by
    intro a; ext ϑ
    simp only [Finset.mem_inter, Θ, mem_foldr_union_iff_exists_get]
    refine ⟨fun hϑ => ⟨⟨a, hϑ⟩, Finset.mem_union_right _ hϑ⟩, ?_⟩
    rintro ⟨⟨b, hϑb⟩, hϑ_mon_a⟩
    have hϑ_mon_b : ϑ ∈ worldlinePolymerMonomers (K.get b) := Finset.mem_union_right _ hϑb
    have h_ab : a = b := by
      by_contra hab
      exact Finset.disjoint_left.mp (h_disj_mon a b hab) hϑ_mon_a hϑ_mon_b
    exact h_ab ▸ hϑb
  have h_comp_a : ∀ a : Fin K.length,
      K.get a = componentPolymer ξ_list Θ (worldlinePolymerMonomers (K.get a)) :=
    fun a => Prod.ext (h_flt_a a) (h_mayer_a a)
  have hM_iff : ∀ u, u ∈ M ↔ ∃ a : Fin K.length, u ∈ worldlinePolymerMonomers (K.get a) := by
    intro u
    simp only [M, Θ, Finset.mem_union, List.mem_toFinset, List.mem_map, mem_foldr_union_iff_exists_get]
    constructor
    · rintro (⟨ξ, hξ_in, rfl⟩ | ⟨a, hu_a⟩)
      · rcases List.mem_iff_getElem.mp hξ_in with ⟨j, hj, rfl⟩
        refine ⟨owner' ⟨j, hj⟩, ?_⟩
        rw [h_elem ⟨j, hj⟩]
        exact Finset.mem_union_left _ (List.mem_toFinset.mpr (List.mem_map_of_mem (List.getElem_mem _)))
      · exact ⟨a, Finset.mem_union_right _ hu_a⟩
    · rintro ⟨a, hu_a⟩
      rcases Finset.mem_union.mp hu_a with hu_j | hu_m
      · rcases List.mem_map.mp (List.mem_toFinset.mp hu_j) with ⟨ξ, hξa, rfl⟩
        exact Or.inl ⟨ξ, h_mem_ξ_of_mem_a a hξa, rfl⟩
      · exact Or.inr ⟨a, hu_m⟩
  have h_conn_a : ∀ (a : Fin K.length) {u},
      u ∈ worldlinePolymerMonomers (K.get a) →
      monomerConnComp sys C_RCA M u = worldlinePolymerMonomers (K.get a) := by
    intro a u hu
    have hγ_a := hK_val (K.get a) (List.get_mem K a)
    ext v
    simp only [monomerConnComp, Finset.mem_filter]
    constructor
    · rintro ⟨-, h_path⟩
      induction h_path with
      | refl => exact hu
      | tail _ h_step ih =>
        rcases (hM_iff _).mp h_step.2.1 with ⟨b, hvb⟩
        have h_ab : a = b := by
          by_contra hab
          apply h_step.2.2.2
          refine Finset.disjoint_left.mpr fun c hcx hcy =>
            Finset.disjoint_left.mp (h_disj_col a b hab)
              (Finset.mem_biUnion.mpr ⟨_, ih, hcx⟩)
              (Finset.mem_biUnion.mpr ⟨_, hvb, hcy⟩)
        exact h_ab ▸ hvb
    · intro hv
      refine ⟨(hM_iff v).mpr ⟨a, hv⟩, ?_⟩
      have h_path_C := hγ_a.2.2.2.2 u hu v hv
      clear hv
      induction h_path_C with
      | refl => exact Relation.ReflTransGen.refl
      | tail _ h_step ih =>
        exact Relation.ReflTransGen.tail ih
          ⟨(hM_iff _).mpr ⟨a, h_step.1⟩, (hM_iff _).mpr ⟨a, h_step.2.1⟩, h_step.2.2.1, h_step.2.2.2⟩
  have h_mon_mem : ∀ a : Fin K.length,
      worldlinePolymerMonomers (K.get a) ∈ monomerComponents sys C_RCA M := by
    intro a
    have hγ_a := hK_val (K.get a) (List.get_mem K a)
    rcases hγ_a.2.2.2.1 with ⟨u, hu⟩
    exact Finset.mem_image.mpr ⟨u, (hM_iff u).mpr ⟨a, hu⟩, h_conn_a a hu⟩
  let f : Fin p → monomerComponents sys C_RCA M :=
    fun a => ⟨worldlinePolymerMonomers (K.get (a.cast h_len.symm)), h_mon_mem (a.cast h_len.symm)⟩
  have hf_bij : Function.Bijective f := by
    refine ⟨fun a₁ a₂ h_eq => ?_, fun C => ?_⟩
    · by_contra h_ne
      have h_ne' : a₁.cast h_len.symm ≠ a₂.cast h_len.symm :=
        fun h => h_ne (Fin.ext (by simpa using congrArg Fin.val h))
      have hγ₁ := hK_val (K.get (a₁.cast h_len.symm)) (List.get_mem K _)
      rcases hγ₁.2.2.2.1 with ⟨u, hu₁⟩
      have h_val_eq : worldlinePolymerMonomers (K.get (a₁.cast h_len.symm)) =
          worldlinePolymerMonomers (K.get (a₂.cast h_len.symm)) := congrArg Subtype.val h_eq
      have hu₂ : u ∈ worldlinePolymerMonomers (K.get (a₂.cast h_len.symm)) := h_val_eq ▸ hu₁
      exact Finset.disjoint_left.mp (h_disj_mon _ _ h_ne') hu₁ hu₂
    · rcases Finset.mem_image.mp C.2 with ⟨u, huM, hC_eq⟩
      rcases (hM_iff u).mp huM with ⟨a, hua⟩
      refine ⟨a.cast h_len, Subtype.ext ?_⟩
      change worldlinePolymerMonomers (K.get a) = C.1
      rw [← h_conn_a a hua, hC_eq]
  have h_card : (monomerComponents sys C_RCA M).card = p := by
    have := Fintype.card_of_bijective hf_bij
    rw [Fintype.card_fin, Fintype.card_coe] at this
    exact this.symm
  refine ⟨Finset.mem_filter.mpr ⟨hξ_mem_m, ?_, ?_⟩, Finset.mem_filter.mpr ⟨?_, ?_⟩,
    h_card, f, hf_bij, ?_⟩
  · have hK_ne : K ≠ [] := by
      rintro rfl; simp at h_sum; omega
    have h0_lt : 0 < K.length := List.length_pos_of_ne_nil hK_ne
    have hγ₀ := hK_val (K.get ⟨0, h0_lt⟩) (List.get_mem K ⟨0, h0_lt⟩)
    have h_le : (K.get ⟨0, h0_lt⟩).1.length ≤ (K.map (fun γ => γ.1.length)).sum :=
      List.le_sum_of_mem (List.mem_map_of_mem (List.get_mem K ⟨0, h0_lt⟩))
    linarith [hγ₀.2.2.1.1, h_len_ξ]
  · rw [← worldlineJumpListFlip_eq_staticCSSPauliFlip_loop D_field (ξ_list, ∅)]
    funext c
    by_cases hc_in : ∃ a : Fin K.length, c ∈ worldlinePolymerNativeCollar sys C_RCA (K.get a)
    · rcases hc_in with ⟨a, hc_a⟩
      have hγ_a := hK_val (K.get a) (List.get_mem K a)
      have ha_closed : worldlineJumpListFlip D_field (K.get a).1 = (fun _ => false) :=
        (worldlineJumpListFlip_eq_staticCSSPauliFlip_loop D_field (K.get a)).trans hγ_a.2.2.1.2
      have h_eq_flt := worldlineJumpListFlip_filter_eq_of_false_outside D_field ξ_list (P a) c
        (fun ξ hξ_in hPa_f => by
          rcases List.mem_iff_getElem.mp hξ_in with ⟨j, hj, rfl⟩
          let b := owner' ⟨j, hj⟩
          have hb_ne : a ≠ b := by
            rintro rfl
            have h_true := (hP_iff (owner' ⟨j, hj⟩) ⟨j, hj⟩).mpr rfl
            exact Bool.noConfusion (hPa_f.symm.trans h_true)
          have hξ_b : ξ_list[j] ∈ (K.get b).1 := by
            rw [h_elem ⟨j, hj⟩]; exact List.getElem_mem _
          have hγ_b := hK_val (K.get b) (List.get_mem K b)
          have hp_b : (ξ_list[j]).1 ∈ worldlinePolymerMonomers (K.get b) :=
            Finset.mem_union_left _ (List.mem_toFinset.mpr (List.mem_map_of_mem hξ_b))
          rcases mem_scaleCubeFinset_iff.mp (hγ_b.1 _ hp_b) with ⟨hr, hA⟩
          by_contra h_not_f
          have hc_b : c ∈ worldlinePolymerNativeCollar sys C_RCA (K.get b) :=
            Finset.mem_biUnion.mpr ⟨(ξ_list[j]).1, hp_b,
              cubeIntersectingChecks_subset_rcaCollarChecks sys h_geom hr0_le
                (Finset.mem_Icc.mp hr).1 hA
                (staticCSSPauliFlip_mem_cubeIntersectingChecks D_field sys h_sys_supp _ _ _
                  (hγ_b.2.1 _ hξ_b).1 c (Bool.eq_true_of_not_eq_false h_not_f))⟩
          exact Finset.disjoint_left.mp (h_disj_col a b hb_ne) hc_a hc_b)
      rw [← h_eq_flt, ← h_flt_a a, congrFun ha_closed c]
    · push_neg at hc_in
      have h_all_f : ∀ l : List (WorldlineJumpMonomer L q_code),
          (∀ ξ ∈ l, staticCSSPauliFlip D_field ξ.2.1 ξ.2.2 c = false) →
          worldlineJumpListFlip D_field l c = false := by
        intro l; induction l with
        | nil => intro _; rfl
        | cons hd tl ih =>
          intro h_l
          change bne (staticCSSPauliFlip D_field hd.2.1 hd.2.2 c) (worldlineJumpListFlip D_field tl c) = false
          rw [h_l hd List.mem_cons_self, ih (fun ξ hξ => h_l ξ (List.mem_cons_of_mem hd hξ)), Bool.false_bne]
      refine h_all_f _ (fun ξ hξ_in => ?_)
      rcases List.mem_iff_getElem.mp hξ_in with ⟨j, hj, rfl⟩
      let a := owner' ⟨j, hj⟩
      have hξ_a : ξ_list[j] ∈ (K.get a).1 := by rw [h_elem ⟨j, hj⟩]; exact List.getElem_mem _
      have hγ_a := hK_val (K.get a) (List.get_mem K a)
      have hp_a : (ξ_list[j]).1 ∈ worldlinePolymerMonomers (K.get a) :=
        Finset.mem_union_left _ (List.mem_toFinset.mpr (List.mem_map_of_mem hξ_a))
      rcases mem_scaleCubeFinset_iff.mp (hγ_a.1 _ hp_a) with ⟨hr, hA⟩
      by_contra h_not_f
      exact hc_in a (Finset.mem_biUnion.mpr ⟨(ξ_list[j]).1, hp_a,
        cubeIntersectingChecks_subset_rcaCollarChecks sys h_geom hr0_le
          (Finset.mem_Icc.mp hr).1 hA
          (staticCSSPauliFlip_mem_cubeIntersectingChecks D_field sys h_sys_supp _ _ _
            (hγ_a.2.1 _ hξ_a).1 c (Bool.eq_true_of_not_eq_false h_not_f))⟩)
  · rw [Finset.mem_powerset]
    intro ϑ hϑ
    rcases (mem_foldr_union_iff_exists_get K ϑ).mp hϑ with ⟨a, hϑa⟩
    exact (hK_val (K.get a) (List.get_mem K a)).1 ϑ (Finset.mem_union_right _ hϑa)
  · intro C hC
    rcases hf_bij.2 ⟨C, hC⟩ with ⟨a, ha⟩
    have hC_eq : C = worldlinePolymerMonomers (K.get (a.cast h_len.symm)) :=
      (congrArg Subtype.val ha).symm
    have hγ_a := hK_val (K.get (a.cast h_len.symm)) (List.get_mem K _)
    have h_len2 : 2 ≤ (K.get (a.cast h_len.symm)).1.length := hγ_a.2.2.1.1
    let ξ₀ := (K.get (a.cast h_len.symm)).1[0]'(by omega)
    have hξ₀_a : ξ₀ ∈ (K.get (a.cast h_len.symm)).1 := List.getElem_mem (by omega)
    exact ⟨ξ₀, h_mem_ξ_of_mem_a _ hξ₀_a,
      hC_eq ▸ Finset.mem_union_left _ (List.mem_toFinset.mpr (List.mem_map_of_mem hξ₀_a))⟩
  · refine List.ext_getElem (by simp [h_len]) fun i h1 h2 => ?_
    rw [List.getElem_ofFn]
    exact h_comp_a ⟨i, h1⟩

private lemma ofFn_componentPolymer_mem_cluster_shuffle
    {L q_code r_0 m_max w_0 R_cut m : ℕ} [NeZero L] {C_RCA : ℝ}
    (D_field : Box3D L → LocalCSSDescriptor q_code r_0 m_max)
    (sys : SysCSS[L, q_code, m_max])
    (h_sys_supp : ∀ idx, sys.support idx = staticCSSCheckSupport D_field idx)
    (h_geom : sys.IsGeometricallyLocal r_0 w_0)
    (hr0_le : 1 + 4 * (r_0 : ℝ) ≤ C_RCA)
    {ξ_list : List (WorldlineJumpMonomer L q_code)}
    (hξ_list : ξ_list ∈ validClosedJumpListFinset D_field R_cut m)
    {Θ : Finset (ℕ × Finset (Box3D L))}
    (hΘ : Θ ∈ connMayerFinset sys C_RCA R_cut ξ_list) :
    let M := (ξ_list.map Prod.fst).toFinset ∪ Θ
    let S_comp := monomerComponents sys C_RCA M
    S_comp.card ∈ Finset.Icc 1 m ∧
    ∀ (p : ℕ) (f : Fin p → S_comp), Function.Bijective f →
      let K := List.ofFn (fun a : Fin p => componentPolymer ξ_list Θ (f a).1)
      K ∈ validClusterFinsetOfLenAndTotalJump D_field sys C_RCA R_cut m p ∧
      ξ_list ∈ multiPolymerShuffleFinset D_field R_cut K ∧
      K.foldr (fun γ acc => γ.2 ∪ acc) ∅ = Θ := by
  intro M S_comp
  rcases Finset.mem_filter.mp hξ_list with ⟨hξ_mem, hξ_ge2, _⟩
  have hξ_len := (mem_worldlineJumpListFinsetOfLength_iff_local D_field R_cut m ξ_list).mp hξ_mem |>.1
  rcases monomerConnComp_properties sys C_RCA M with
    ⟨hM_self, hM_sub, hM_eq, h_comp_props, h_comp_disj⟩
  have h_valid_C : ∀ C ∈ S_comp,
      worldlinePolymerMonomers (componentPolymer ξ_list Θ C) = C ∧
      IsValidWorldlinePolymer D_field sys C_RCA R_cut (componentPolymer ξ_list Θ C) :=
    fun C hC => componentPolymer_monomers_and_valid D_field sys h_sys_supp h_geom hr0_le hξ_list hΘ hC
  have h_mem_for_bij : ∀ (p : ℕ) (f : Fin p → S_comp), Function.Bijective f →
      let K := List.ofFn (fun a : Fin p => componentPolymer ξ_list Θ (f a).1)
      K ∈ validClusterFinsetOfLenAndTotalJump D_field sys C_RCA R_cut m p ∧
      ξ_list ∈ multiPolymerShuffleFinset D_field R_cut K ∧
      K.foldr (fun γ acc => γ.2 ∪ acc) ∅ = Θ := by
    intro p f hf_bij K
    have hK_len : K.length = p := List.length_ofFn
    let P : Fin K.length → WorldlineJumpMonomer L q_code → Bool :=
      fun a ξ => decide (ξ.1 ∈ (f (a.cast hK_len)).1)
    have h_ex : ∀ ξ ∈ ξ_list, ∃ a : Fin K.length, P a ξ = true := by
      intro ξ hξ_in
      have hξ_M : ξ.1 ∈ M :=
        Finset.mem_union_left _ (List.mem_toFinset.mpr (List.mem_map_of_mem hξ_in))
      let C := monomerConnComp sys C_RCA M ξ.1
      have hC_mem : C ∈ S_comp := Finset.mem_image.mpr ⟨ξ.1, hξ_M, rfl⟩
      rcases hf_bij.2 ⟨C, hC_mem⟩ with ⟨a₀, ha₀⟩
      refine ⟨a₀.cast hK_len.symm, ?_⟩
      dsimp [P]; rw [decide_eq_true_iff, congrArg Subtype.val ha₀]
      exact hM_self ξ.1 hξ_M
    have h_uniq : ∀ ξ ∈ ξ_list, ∀ a b : Fin K.length, P a ξ = true → P b ξ = true → a = b := by
      intro ξ _ a b ha hb
      by_contra hab
      have h_ne_f : (f (a.cast hK_len)).1 ≠ (f (b.cast hK_len)).1 := by
        intro h_eq
        exact hab (Fin.ext (by simpa using congrArg Fin.val (hf_bij.1 (Subtype.ext h_eq))))
      exact Finset.disjoint_left.mp
        ((h_comp_disj _ (f (a.cast hK_len)).2 _ (f (b.cast hK_len)).2 h_ne_f).1)
        (of_decide_eq_true ha) (of_decide_eq_true hb)
    have h_flt : ∀ a : Fin K.length, (K.get a).1 = ξ_list.filter (P a) := by
      intro a; rw [List.get_ofFn]; rfl
    rcases mem_multiPolymerShuffleFinset_of_filter_partition D_field K ξ_list hξ_mem P h_ex h_uniq h_flt with
      ⟨h_sum_len, h_shuf⟩
    have hK_val : ∀ γ ∈ K, IsValidWorldlinePolymer D_field sys C_RCA R_cut γ := by
      intro γ hγ
      rcases List.mem_ofFn.mp hγ with ⟨a, rfl⟩
      exact (h_valid_C (f a).1 (f a).2).2
    have hK_pw : K.Pairwise (fun γ₁ γ₂ => ¬ArePolymersIncompatible sys C_RCA γ₁ γ₂) := by
      rw [List.pairwise_iff_get]
      intro a b h_lt
      unfold ArePolymersIncompatible
      rw [not_not]
      have h_ne_f : (f (a.cast hK_len)).1 ≠ (f (b.cast hK_len)).1 := by
        intro h_eq
        exact ne_of_lt h_lt (Fin.ext (by simpa using congrArg Fin.val (hf_bij.1 (Subtype.ext h_eq))))
      have h_get_a : K.get a = componentPolymer ξ_list Θ (f (a.cast hK_len)).1 := List.get_ofFn _ _
      have h_get_b : K.get b = componentPolymer ξ_list Θ (f (b.cast hK_len)).1 := List.get_ofFn _ _
      rw [h_get_a, h_get_b]
      unfold worldlinePolymerNativeCollar
      rw [(h_valid_C _ (f (a.cast hK_len)).2).1, (h_valid_C _ (f (b.cast hK_len)).2).1]
      refine Finset.disjoint_left.mpr fun c hca hcb => ?_
      rcases Finset.mem_biUnion.mp hca with ⟨u, hu, hcu⟩
      rcases Finset.mem_biUnion.mp hcb with ⟨v, hv, hcv⟩
      exact Finset.disjoint_left.mp
        ((h_comp_disj _ (f (a.cast hK_len)).2 _ (f (b.cast hK_len)).2 h_ne_f).2 u hu v hv) hcu hcv
    have h_foldr : K.foldr (fun γ acc => γ.2 ∪ acc) ∅ = Θ := by
      ext ϑ
      rw [mem_foldr_union_iff_exists_get]
      constructor
      · rintro ⟨a, hϑa⟩
        have h_get_a : K.get a = componentPolymer ξ_list Θ (f (a.cast hK_len)).1 := List.get_ofFn _ _
        rw [h_get_a] at hϑa
        exact (Finset.mem_inter.mp hϑa).1
      · intro hϑ
        have hϑ_M : ϑ ∈ M := Finset.mem_union_right _ hϑ
        let C := monomerConnComp sys C_RCA M ϑ
        have hC_mem : C ∈ S_comp := Finset.mem_image.mpr ⟨ϑ, hϑ_M, rfl⟩
        rcases hf_bij.2 ⟨C, hC_mem⟩ with ⟨a₀, ha₀⟩
        refine ⟨a₀.cast hK_len.symm, ?_⟩
        have h_get_a : K.get (a₀.cast hK_len.symm) = componentPolymer ξ_list Θ (f a₀).1 := by
          rw [List.get_ofFn]; rfl
        rw [h_get_a]
        exact Finset.mem_inter.mpr ⟨hϑ, congrArg Subtype.val ha₀ ▸ hM_self ϑ hϑ_M⟩
    exact ⟨(mem_validClusterFinsetOfLenAndTotalJump_iff D_field sys C_RCA R_cut m p K).mpr
      ⟨hK_len, h_sum_len, hK_val, hK_pw⟩, h_shuf, h_foldr⟩
  refine ⟨Finset.mem_Icc.mpr ⟨?_, ?_⟩, h_mem_for_bij⟩
  · have h_ne_ξ : 0 < ξ_list.length := by omega
    let ξ₀ := ξ_list[0]'h_ne_ξ
    have hξ₀_M : ξ₀.1 ∈ M :=
      Finset.mem_union_left _ (List.mem_toFinset.mpr (List.mem_map_of_mem (List.getElem_mem h_ne_ξ)))
    exact Finset.card_pos.mpr ⟨monomerConnComp sys C_RCA M ξ₀.1,
      Finset.mem_image.mpr ⟨ξ₀.1, hξ₀_M, rfl⟩⟩
  · let e₀ : Fin S_comp.card ≃ S_comp := (Fintype.equivFinOfCardEq (Fintype.card_coe S_comp)).symm
    rcases h_mem_for_bij S_comp.card e₀ e₀.bijective with ⟨hK_mem, _, _⟩
    rcases (mem_validClusterFinsetOfLenAndTotalJump_iff D_field sys C_RCA R_cut m S_comp.card _).mp hK_mem with
      ⟨hK_len, hK_sum, hK_val, _⟩
    have h_le := length_le_sum_jump_length_of_valid D_field sys _ hK_val
    omega

private lemma sum_validClusterFinset_multiPolymerShuffleFinset_eq_sum_validClosedJumpList
    {L q_code r_0 m_max w_0 R_cut m : ℕ} [NeZero L] {C_RCA : ℝ}
    (D_field : Box3D L → LocalCSSDescriptor q_code r_0 m_max)
    (sys : SysCSS[L, q_code, m_max])
    (h_sys_supp : ∀ idx, sys.support idx = staticCSSCheckSupport D_field idx)
    (h_geom : sys.IsGeometricallyLocal r_0 w_0)
    (hr0_le : 1 + 4 * (r_0 : ℝ) ≤ C_RCA)
    (hm : 1 ≤ m)
    (F : List (WorldlineJumpMonomer L q_code) → Finset (ℕ × Finset (Box3D L)) → ℝ) :
    (∑ p ∈ Finset.Icc 1 m,
      ∑ K ∈ validClusterFinsetOfLenAndTotalJump D_field sys C_RCA R_cut m p,
        ((Nat.factorial p : ℝ)⁻¹) *
          ∑ ξ_list ∈ multiPolymerShuffleFinset D_field R_cut K,
            F ξ_list (K.foldr (fun γ acc => γ.2 ∪ acc) ∅)) =
    ∑ ξ_list ∈ validClosedJumpListFinset D_field R_cut m,
      ∑ Θ ∈ connMayerFinset sys C_RCA R_cut ξ_list,
        F ξ_list Θ := by
  let S_ξ := validClosedJumpListFinset D_field R_cut m
  let S_Θ (ξ_list : List (WorldlineJumpMonomer L q_code)) := connMayerFinset sys C_RCA R_cut ξ_list
  have h_inner_K : ∀ p ∈ Finset.Icc 1 m,
      ∀ K ∈ validClusterFinsetOfLenAndTotalJump D_field sys C_RCA R_cut m p,
      ((Nat.factorial p : ℝ)⁻¹) *
        (∑ ξ_list ∈ multiPolymerShuffleFinset D_field R_cut K,
          F ξ_list (K.foldr (fun γ acc => γ.2 ∪ acc) ∅)) =
      ∑ ξ_list ∈ S_ξ, ∑ Θ ∈ S_Θ ξ_list,
        if ξ_list ∈ multiPolymerShuffleFinset D_field R_cut K ∧
            K.foldr (fun γ acc => γ.2 ∪ acc) ∅ = Θ then
          ((Nat.factorial p : ℝ)⁻¹) * F ξ_list Θ
        else 0 := by
    intro p _ K hK
    rw [Finset.mul_sum]
    have h_sub : multiPolymerShuffleFinset D_field R_cut K ⊆ S_ξ := fun ξ_list hξ =>
      (cluster_shuffle_invariants D_field sys h_sys_supp h_geom hr0_le hm hK hξ).1
    rw [← Finset.sum_subset h_sub (fun ξ_list _ h_not => by
      refine Finset.sum_eq_zero fun Θ _ => if_neg (fun h => h_not h.1))]
    refine Finset.sum_congr rfl fun ξ_list hξ => ?_
    have hΘ_mem : K.foldr (fun γ acc => γ.2 ∪ acc) ∅ ∈ S_Θ ξ_list :=
      (cluster_shuffle_invariants D_field sys h_sys_supp h_geom hr0_le hm hK hξ).2.1
    have h_ite_congr : ∀ Θ ∈ S_Θ ξ_list,
        (if ξ_list ∈ multiPolymerShuffleFinset D_field R_cut K ∧
            K.foldr (fun γ acc => γ.2 ∪ acc) ∅ = Θ then
          ((Nat.factorial p : ℝ)⁻¹) * F ξ_list Θ
        else 0) =
        if K.foldr (fun γ acc => γ.2 ∪ acc) ∅ = Θ then
          ((Nat.factorial p : ℝ)⁻¹) * F ξ_list Θ
        else 0 := fun Θ _ => by simp [hξ]
    rw [Finset.sum_congr rfl h_ite_congr,
      Finset.sum_ite_eq (S_Θ ξ_list) (K.foldr (fun γ acc => γ.2 ∪ acc) ∅)
        (fun Θ => ((Nat.factorial p : ℝ)⁻¹) * F ξ_list Θ),
      if_pos hΘ_mem]
  rw [Finset.sum_congr rfl (fun p hp => Finset.sum_congr rfl (fun K hK => h_inner_K p hp K hK))]
  simp_rw [Finset.sum_comm (s := validClusterFinsetOfLenAndTotalJump D_field sys C_RCA R_cut m _)]
  rw [Finset.sum_comm (s := Finset.Icc 1 m)]
  refine Finset.sum_congr rfl fun ξ_list hξ_list => ?_
  rw [Finset.sum_comm (s := Finset.Icc 1 m)]
  refine Finset.sum_congr rfl fun Θ hΘ => ?_
  let M := (ξ_list.map Prod.fst).toFinset ∪ Θ
  let S_comp := monomerComponents sys C_RCA M
  let p₀ := S_comp.card
  rcases ofFn_componentPolymer_mem_cluster_shuffle D_field sys h_sys_supp h_geom hr0_le hξ_list hΘ with
    ⟨hp₀_mem, h_ofFn_mem⟩
  rw [Finset.sum_eq_single p₀
    (fun p hp h_ne => Finset.sum_eq_zero fun K hK => if_neg fun ⟨h_shuf, h_fold⟩ => h_ne (by
      have h_card := (cluster_shuffle_invariants D_field sys h_sys_supp h_geom hr0_le hm hK h_shuf).2.2.1
      dsimp [p₀, S_comp, M]; rw [← h_fold]; exact h_card.symm))
    (fun h_abs => False.elim (h_abs hp₀_mem))]
  rw [← Finset.sum_filter]
  let T := (validClusterFinsetOfLenAndTotalJump D_field sys C_RCA R_cut m p₀).filter
    (fun K => ξ_list ∈ multiPolymerShuffleFinset D_field R_cut K ∧
      K.foldr (fun γ acc => γ.2 ∪ acc) ∅ = Θ)
  let e₀ : Fin p₀ ≃ S_comp := (Fintype.equivFinOfCardEq (Fintype.card_coe S_comp)).symm
  let Φ : Equiv.Perm (Fin p₀) → WorldlineUrsellCluster L q_code :=
    fun π => List.ofFn (fun a : Fin p₀ => componentPolymer ξ_list Θ (e₀ (π a)).1)
  have hT_eq : T = (Finset.univ : Finset (Equiv.Perm (Fin p₀))).image Φ := by
    ext K
    simp only [T, Finset.mem_filter, Finset.mem_image, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨hK, h_shuf, h_fold⟩
      rcases (cluster_shuffle_invariants D_field sys h_sys_supp h_geom hr0_le hm hK h_shuf).2.2.2 with
        ⟨f_K, hf_bij, hK_eq⟩
      have h_comp_eq : monomerComponents sys C_RCA
          ((ξ_list.map Prod.fst).toFinset ∪ K.foldr (fun γ acc => γ.2 ∪ acc) ∅) = S_comp := by
        dsimp [S_comp, M]; rw [h_fold]
      let f' : Fin p₀ → S_comp := fun a => ⟨(f_K a).1, h_comp_eq ▸ (f_K a).2⟩
      have hf'_bij : Function.Bijective f' := by
        refine ⟨fun a₁ a₂ h_eq => hf_bij.1 (Subtype.ext (by simpa [f'] using congrArg Subtype.val h_eq)), fun C => ?_⟩
        rcases hf_bij.2 ⟨C.1, h_comp_eq.symm ▸ C.2⟩ with ⟨a, ha⟩
        exact ⟨a, Subtype.ext (by simpa [f'] using congrArg Subtype.val ha)⟩
      let π : Equiv.Perm (Fin p₀) := Equiv.ofBijective (e₀.symm ∘ f') (e₀.symm.bijective.comp hf'_bij)
      refine ⟨π, ?_⟩
      dsimp [Φ, π]; rw [hK_eq]
      refine List.ext_getElem (by simp) fun i h1 h2 => ?_
      rw [List.getElem_ofFn, List.getElem_ofFn]
      let C_i : Finset (ℕ × Finset (Box3D L)) := (f_K ⟨i, by simpa using h2⟩).1
      have h_lhs : (e₀ (e₀.symm (f' ⟨i, by simpa using h1⟩))).1 = C_i := by simp [f', C_i]
      have h_rhs : (f_K ⟨i, by simpa using h2⟩).1 = C_i := rfl
      rw [h_lhs, h_rhs, h_fold]
    · rintro ⟨π, rfl⟩
      exact h_ofFn_mem p₀ (e₀ ∘ π) (e₀.bijective.comp π.bijective)
  have hΦ_inj : ∀ π₁ ∈ (Finset.univ : Finset (Equiv.Perm (Fin p₀))),
      ∀ π₂ ∈ (Finset.univ : Finset (Equiv.Perm (Fin p₀))),
      Φ π₁ = Φ π₂ → π₁ = π₂ := by
    intro π₁ _ π₂ _ h_eq
    ext a
    have h_get : (Φ π₁)[a.1]'(by simp [Φ]) = (Φ π₂)[a.1]'(by simp [Φ]) := by simp [h_eq]
    dsimp [Φ] at h_get
    rw [List.getElem_ofFn, List.getElem_ofFn] at h_get
    have h_mon := congrArg worldlinePolymerMonomers h_get
    rw [(componentPolymer_monomers_and_valid D_field sys h_sys_supp h_geom hr0_le hξ_list hΘ (e₀ (π₁ a)).2).1,
      (componentPolymer_monomers_and_valid D_field sys h_sys_supp h_geom hr0_le hξ_list hΘ (e₀ (π₂ a)).2).1] at h_mon
    exact congrArg Fin.val (e₀.injective (Subtype.ext h_mon))
  change (∑ K ∈ T, ((Nat.factorial p₀ : ℝ)⁻¹) * F ξ_list Θ) = F ξ_list Θ
  rw [Finset.sum_const, hT_eq, Finset.card_image_of_injOn hΦ_inj, Finset.card_univ,
    Fintype.card_perm, Fintype.card_fin, nsmul_eq_mul,
    mul_inv_cancel_left₀ (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero p₀))]

private lemma sum_validClusterFinset_raw_eq_sum_singleSector
    {L q_code r_0 m_max w_0 R_cut m : ℕ} [NeZero L]
    {C_RCA β : ℝ} (hr0_le : 1 + 4 * (r_0 : ℝ) ≤ C_RCA) (hC_RCA : 1 ≤ C_RCA)
    (D_field : Box3D L → LocalCSSDescriptor q_code r_0 m_max)
    (sys : SysCSS[L, q_code, m_max])
    (h_sys_checks : ∀ idx, sys.checkProj idx = staticCSSCheckProj D_field idx ∧
      sys.support idx = staticCSSCheckSupport D_field idx ∧ sys.weight idx = 1)
    (h_geom : sys.IsGeometricallyLocal r_0 w_0)
    (V : QuasiLocalPerturbation 3 L (SiteCSS[L, q_code]))
    (d_loc : ℕ → Finset (Box3D L) → (IdxCSS[L, q_code, m_max] → Bool) → ℝ)
    (hd_collar : ∀ r ∈ Finset.Icc 1 (min R_cut L), ∀ A ∈ boxCubes 3 L r,
      ∀ σ₁ σ₂, restrictSyndromeToCollar (rcaCollarChecks sys C_RCA r A) σ₁ =
        restrictSyndromeToCollar (rcaCollarChecks sys C_RCA r A) σ₂ →
        d_loc r A σ₁ = d_loc r A σ₂)
    {σ₀ : IdxCSS[L, q_code, m_max] → Bool} (hσ₀ : σ₀ ∈ realizableSyndromes D_field)
    (hm : 1 ≤ m) :
    (∑ p ∈ Finset.Icc 1 m,
      ∑ K ∈ validClusterFinsetOfLenAndTotalJump D_field sys C_RCA R_cut m p,
        worldlineDysonRawClusterWeight D_field sys C_RCA R_cut β V d_loc σ₀ K) =
    ∑ ξ_list ∈ worldlineJumpListFinsetOfLength D_field R_cut m,
      singleSectorWorldlineDysonJumpWeight D_field sys R_cut β V d_loc σ₀ ξ_list := by
  let F (ξ_list : List (WorldlineJumpMonomer L q_code)) (Θ : Finset (ℕ × Finset (Box3D L))) : ℝ :=
    ((-1 : ℝ) ^ ξ_list.length) *
      (hilbertTrace (sys.syndromeProjector σ₀ *
        worldlinePolymerWeightedLoopOp D_field sys V (ξ_list, Θ)) /
        hilbertTrace (sys.syndromeProjector σ₀)) *
      ∫ τ : Fin ξ_list.length → ℝ,
        if InOrderedDysonSimplex β τ then
          Real.exp (-worldlineBareAction D_field sys ξ_list σ₀ β τ) *
            ∏ ϑ ∈ Θ, worldlineMayerBondFactor D_field ξ_list d_loc σ₀ β ϑ τ
        else 0
  have h_raw_sum : ∀ p ∈ Finset.Icc 1 m,
      ∀ K ∈ validClusterFinsetOfLenAndTotalJump D_field sys C_RCA R_cut m p,
      worldlineDysonRawClusterWeight D_field sys C_RCA R_cut β V d_loc σ₀ K =
        ((Nat.factorial p : ℝ)⁻¹) *
          ∑ ξ_list ∈ multiPolymerShuffleFinset D_field R_cut K,
            F ξ_list (K.foldr (fun γ acc => γ.2 ∪ acc) ∅) := by
    intro p _ K hK
    rcases (mem_validClusterFinsetOfLenAndTotalJump_iff D_field sys C_RCA R_cut m p K).mp hK with
      ⟨h_len, _, h_val, h_pw⟩
    rw [worldlineDysonRawClusterWeight_eq_sum_multiPolymerShuffleFinset
      hr0_le hC_RCA D_field sys h_sys_checks h_geom V d_loc hd_collar hσ₀ K h_val h_pw, h_len]
  rw [Finset.sum_congr rfl (fun p hp => Finset.sum_congr rfl (fun K hK => h_raw_sum p hp K hK)),
    sum_validClusterFinset_multiPolymerShuffleFinset_eq_sum_validClosedJumpList
      D_field sys (fun idx => (h_sys_checks idx).2.1) h_geom hr0_le hm F]
  symm
  have h_sub_valid : validClosedJumpListFinset D_field R_cut m ⊆
      worldlineJumpListFinsetOfLength D_field R_cut m := Finset.filter_subset _ _
  rw [← Finset.sum_subset h_sub_valid
    (fun ξ_list hξ_mem hξ_not => by
      rcases (mem_worldlineJumpListFinsetOfLength_iff_local D_field R_cut m ξ_list).mp hξ_mem with ⟨h_len, h_all⟩
      have h_ne_nil : ξ_list ≠ [] := by rintro rfl; simp at h_len; omega
      unfold singleSectorWorldlineDysonJumpWeight
      rw [if_neg h_ne_nil, if_neg]
      rintro ⟨_, h_ge2, h_cl⟩
      exact hξ_not (Finset.mem_filter.mpr ⟨hξ_mem, h_ge2, h_cl⟩))]
  refine Finset.sum_congr rfl fun ξ_list hξ_list => ?_
  rcases Finset.mem_filter.mp hξ_list with ⟨hξ_mem, hξ_ge2, hξ_cl⟩
  rcases (mem_worldlineJumpListFinsetOfLength_iff_local D_field R_cut m ξ_list).mp hξ_mem with ⟨hξ_len, hξ_all⟩
  have hξ_ne_nil : ξ_list ≠ [] := by rintro rfl; simp at hξ_ge2
  rw [singleSectorWorldlineDysonJumpWeight_eq_sum_activeMayerSubsets D_field sys
    (fun idx => (h_sys_checks idx).2.1) h_geom hr0_le R_cut V d_loc hd_collar σ₀ ξ_list hξ_ne_nil,
    if_pos ⟨hξ_all, hξ_ge2, hξ_cl⟩]
  let S_act := (worldlineScaleCubeFinset L R_cut).powerset.filter (fun Θ =>
    ∀ ϑ ∈ Θ, ∃ ξ ∈ ξ_list,
      ¬Disjoint (rcaCollarChecks sys C_RCA ϑ.1 ϑ.2) (rcaCollarChecks sys C_RCA ξ.1.1 ξ.1.2))
  have h_sub_act : S_act ⊆ connMayerFinset sys C_RCA R_cut ξ_list := by
    intro Θ hΘ
    rcases Finset.mem_filter.mp hΘ with ⟨hΘ_pow, hΘ_act⟩
    refine Finset.mem_filter.mpr ⟨hΘ_pow, fun C hC => ?_⟩
    let M := (ξ_list.map Prod.fst).toFinset ∪ Θ
    rcases Finset.mem_image.mp hC with ⟨p, hp_M, rfl⟩
    rcases Finset.mem_union.mp hp_M with hp_j | hp_m
    · rcases List.mem_map.mp (List.mem_toFinset.mp hp_j) with ⟨ξ, hξ_in, rfl⟩
      exact ⟨ξ, hξ_in, (monomerConnComp_properties sys C_RCA M).1 ξ.1 hp_M⟩
    · rcases hΘ_act p hp_m with ⟨ξ, hξ_in, h_nd⟩
      have hξ_M : ξ.1 ∈ M :=
        Finset.mem_union_left _ (List.mem_toFinset.mpr (List.mem_map_of_mem hξ_in))
      refine ⟨ξ, hξ_in, Finset.mem_filter.mpr ⟨hξ_M, ?_⟩⟩
      by_cases h_eq : p = ξ.1
      · subst h_eq; exact Relation.ReflTransGen.refl
      · exact Relation.ReflTransGen.single ⟨hp_M, hξ_M, h_eq, h_nd⟩
  refine Finset.sum_subset h_sub_act fun Θ hΘ_conn hΘ_not_act => ?_
  have hΘ_pow : Θ ∈ (worldlineScaleCubeFinset L R_cut).powerset := (Finset.mem_filter.mp hΘ_conn).1
  (try dsimp [S_act] at hΘ_not_act)
  rw [Finset.mem_filter] at hΘ_not_act; push_neg at hΘ_not_act
  rcases hΘ_not_act hΘ_pow with ⟨ϑ, hϑ_in, hϑ_disj⟩
  (try dsimp [F])
  have h_int_zero : (∫ τ : Fin ξ_list.length → ℝ,
      if InOrderedDysonSimplex β τ then
        Real.exp (-worldlineBareAction D_field sys ξ_list σ₀ β τ) *
          ∏ ϑ' ∈ Θ, worldlineMayerBondFactor D_field ξ_list d_loc σ₀ β ϑ' τ
      else 0) = 0 := by
    have h_fn : (fun τ : Fin ξ_list.length → ℝ =>
        if InOrderedDysonSimplex β τ then
          Real.exp (-worldlineBareAction D_field sys ξ_list σ₀ β τ) *
            ∏ ϑ' ∈ Θ, worldlineMayerBondFactor D_field ξ_list d_loc σ₀ β ϑ' τ
        else 0) = (fun _ => 0) := by
      funext τ; split_ifs with h_s
      · have h0 := worldlineMayerBondFactor_eq_zero_of_disjoint_collar (β := β) D_field sys
          (fun idx => (h_sys_checks idx).2.1) h_geom hr0_le R_cut d_loc hd_collar σ₀ ξ_list hξ_all
          ϑ (Finset.mem_powerset.mp hΘ_pow hϑ_in) hϑ_disj τ
        rw [Finset.prod_eq_zero hϑ_in h0, mul_zero]
      · rfl
    rw [h_fn, MeasureTheory.integral_zero]
  rw [h_int_zero, mul_zero]

/-- **Connected-Component Decomposition and Time-Reversal Symmetrization (`tsum_singleSectorWorldlineDysonJumpWeight_eq_tsum_dysonMultiPolymerClusterWeight`)** -/
lemma tsum_singleSectorWorldlineDysonJumpWeight_eq_tsum_dysonMultiPolymerClusterWeight
    {L q_code r_0 m_max w_0 L_star R_cut : ℕ} [NeZero L]
    {C_RCA β Δ_RCA C_wl c_wl J : ℝ}
    (D_field : Box3D L → LocalCSSDescriptor q_code r_0 m_max) (h_valid : ValidDescriptorField D_field)
    (sys : SysCSS[L, q_code, m_max])
    (h_sys_checks : ∀ idx, sys.checkProj idx = staticCSSCheckProj D_field idx ∧
      sys.support idx = staticCSSCheckSupport D_field idx ∧ sys.weight idx = 1)
    (h_geom : sys.IsGeometricallyLocal r_0 w_0)
    (h_tqo1 : SatisfiesTQO1 sys L_star) (h_tqo2 : SatisfiesSectorFilteredLinearTQO2 sys 1 L_star C_RCA)
    (V : QuasiLocalPerturbation 3 L (SiteCSS[L, q_code])) (f : ℕ → ℝ)
    (hf_nn : ∀ r, 0 ≤ f r) (hf_le_one : ∀ r, f r ≤ 1)
    (hV_norm : ∀ r ∈ Finset.Icc 1 (min R_cut L), ∀ A ∈ boxCubes 3 L r, ‖V.term r A‖ ≤ J * f r)
    (e_loc : ℕ → Finset (Box3D L) → ℝ)
    (d_loc : ℕ → Finset (Box3D L) → (IdxCSS[L, q_code, m_max] → Bool) → ℝ)
    (hd_scale : ∀ r ∈ Finset.Icc 1 (min R_cut L), ∀ A ∈ boxCubes 3 L r,
      ∀ σ, |d_loc r A σ| ≤ 2 * (J * f r))
    (h_scalar : IsLocalCollarScalarFamily D_field sys R_cut C_RCA J V e_loc d_loc)
    (hR_cut : 1 ≤ R_cut) (hR_le : R_cut ≤ L_star)
    (h_scale_cal : SatisfiesWorldlineScaleCalibration L L_star R_cut r_0 C_RCA) (hC_RCA : 0 ≤ C_RCA)
    (hC_wl_cal : (kpCollarMaxCheckCard R_cut r_0 w_0 C_RCA : ℝ) ≤ C_wl)
    (hc_wl_cal : (kpCollarMaxCheckCard R_cut r_0 w_0 C_RCA : ℝ) ≤ c_wl)
    (hβ : 16 < β) (hJ_pos : 0 < J)
    (h_sum_pos : 0 < worldlineNativeKPSum f C_wl c_wl β R_cut)
    (h_thresh : J ≤ worldlineSpanningThreshold Δ_RCA C_wl c_wl β f R_cut)
    {σ : IdxCSS[L, q_code, m_max] → Bool}
    (hσ : σ ∈ realizableSyndromes D_field) :
    (∑' ξ_list : List (WorldlineJumpMonomer L q_code),
      singleSectorWorldlineDysonJumpWeight D_field sys R_cut β V d_loc σ ξ_list) =
    ∑' K : WorldlineUrsellCluster L q_code,
      worldlineDysonMultiPolymerClusterWeight D_field sys C_RCA R_cut β V d_loc σ K := by
  have hβ_nn : 0 ≤ β := by linarith
  have hr0_le : 1 + 4 * (r_0 : ℝ) ≤ C_RCA := h_scale_cal.2.1
  have hC_RCA_ge_one : 1 ≤ C_RCA := by
    have : (0 : ℝ) ≤ r_0 := Nat.cast_nonneg r_0
    linarith
  have hd_collar : ∀ r ∈ Finset.Icc 1 (min R_cut L), ∀ A ∈ boxCubes 3 L r,
      ∀ σ₁ σ₂, restrictSyndromeToCollar (rcaCollarChecks sys C_RCA r A) σ₁ =
        restrictSyndromeToCollar (rcaCollarChecks sys C_RCA r A) σ₂ →
        d_loc r A σ₁ = d_loc r A σ₂ :=
    fun r hr A hA σ₁ σ₂ h_eq => (h_scalar r hr A hA).2.2 σ₁ σ₂ fun c hc => by
      have hc' := congrFun h_eq c; simpa [restrictSyndromeToCollar, hc] using hc'
  rcases summable_and_tsum_singleSectorWorldlineDysonJumpWeight hβ_nn D_field sys V d_loc σ with
    ⟨_, h_sum_single_m, h_tsum_single⟩
  let S_cl_m (m : ℕ) : Finset (WorldlineUrsellCluster L q_code) :=
    if m = 0 then {[]}
    else (Finset.Icc 1 m).biUnion (validClusterFinsetOfLenAndTotalJump D_field sys C_RCA R_cut m)
  let totalJump (K : WorldlineUrsellCluster L q_code) : ℕ :=
    (K.map (fun γ => γ.1.length)).sum
  let w_cl (K : WorldlineUrsellCluster L q_code) : ℝ :=
    worldlineDysonMultiPolymerClusterWeight D_field sys C_RCA R_cut β V d_loc σ K
  let w_raw (K : WorldlineUrsellCluster L q_code) : ℝ :=
    worldlineDysonRawClusterWeight D_field sys C_RCA R_cut β V d_loc σ K
  have h_mem_S_cl_m : ∀ K : WorldlineUrsellCluster L q_code,
      (∀ γ ∈ K, IsValidWorldlinePolymer D_field sys C_RCA R_cut γ) →
      K.Pairwise (fun γ₁ γ₂ => ¬ArePolymersIncompatible sys C_RCA γ₁ γ₂) →
      K ∈ S_cl_m (totalJump K) := by
    intro K h_val h_pw
    dsimp [S_cl_m]
    by_cases hm0 : totalJump K = 0
    · rw [if_pos hm0, Finset.mem_singleton]
      have h_le := length_le_sum_jump_length_of_valid D_field sys K h_val
      change K.length ≤ totalJump K at h_le
      rw [hm0, Nat.le_zero, List.length_eq_zero_iff] at h_le
      exact h_le
    · rw [if_neg hm0, Finset.mem_biUnion]
      have h_ne_nil : K ≠ [] := by rintro rfl; exact hm0 rfl
      have h_ge1 : 1 ≤ K.length := Nat.succ_le_of_lt (List.length_pos_of_ne_nil h_ne_nil)
      have h_le_m : K.length ≤ totalJump K := length_le_sum_jump_length_of_valid D_field sys K h_val
      exact ⟨K.length, Finset.mem_Icc.mpr ⟨h_ge1, h_le_m⟩,
        (mem_validClusterFinsetOfLenAndTotalJump_iff D_field sys C_RCA R_cut (totalJump K) K.length K).mpr
          ⟨rfl, rfl, h_val, h_pw⟩⟩
  have h_zero_outside_cl : ∀ (m : ℕ) (K : WorldlineUrsellCluster L q_code),
      totalJump K = m → K ∉ S_cl_m m → w_cl K = 0 := by
    intro m K h_tot h_not
    dsimp [w_cl, worldlineDysonMultiPolymerClusterWeight]
    rw [if_neg]
    rintro ⟨h_val, h_pw⟩
    exact h_not (h_tot ▸ h_mem_S_cl_m K h_val h_pw)
  have h_disj_p : ∀ m : ℕ, (↑(Finset.Icc 1 m) : Set ℕ).PairwiseDisjoint
      (validClusterFinsetOfLenAndTotalJump D_field sys C_RCA R_cut m) := by
    intro m p₁ _ p₂ _ h_ne
    rw [Function.onFun, Finset.disjoint_left]
    intro K hK₁ hK₂
    have h₁ := ((mem_validClusterFinsetOfLenAndTotalJump_iff D_field sys C_RCA R_cut m p₁ K).mp hK₁).1
    have h₂ := ((mem_validClusterFinsetOfLenAndTotalJump_iff D_field sys C_RCA R_cut m p₂ K).mp hK₂).1
    exact h_ne (h₁.symm.trans h₂)
  have h_sum_m_eq : ∀ m : ℕ,
      (∑ K ∈ S_cl_m m, w_cl K) =
      ∑ ξ_list ∈ worldlineJumpListFinsetOfLength D_field R_cut m,
        singleSectorWorldlineDysonJumpWeight D_field sys R_cut β V d_loc σ ξ_list := by
    intro m
    dsimp [S_cl_m, w_cl]
    by_cases hm0 : m = 0
    · subst hm0
      rw [if_pos rfl, (worldlineJumpListFinsetOfLength_zero_and_succ D_field R_cut).1,
        Finset.sum_singleton, Finset.sum_singleton]
      unfold singleSectorWorldlineDysonJumpWeight worldlineDysonMultiPolymerClusterWeight
      rw [if_pos rfl, if_pos ⟨fun _ h => False.elim (List.not_mem_nil h), List.Pairwise.nil⟩,
        if_pos (fun ν _ => by simp [symplecticPauliSign])]
      obtain ⟨_, h_tr_pos⟩ :=
        hilbertTrace_syndromeProjector_eq_P0_of_realizableSyndromes D_field h_valid sys h_sys_checks hσ
      simp [ne_of_gt h_tr_pos]
    · rw [if_neg hm0, Finset.sum_biUnion (h_disj_p m)]
      have hm1 : 1 ≤ m := Nat.pos_of_ne_zero hm0
      calc (∑ p ∈ Finset.Icc 1 m,
            ∑ K ∈ validClusterFinsetOfLenAndTotalJump D_field sys C_RCA R_cut m p,
              worldlineDysonMultiPolymerClusterWeight D_field sys C_RCA R_cut β V d_loc σ K)
        _ = ∑ p ∈ Finset.Icc 1 m,
            ∑ K ∈ validClusterFinsetOfLenAndTotalJump D_field sys C_RCA R_cut m p,
              worldlineDysonRawClusterWeight D_field sys C_RCA R_cut β V d_loc σ K :=
          Finset.sum_congr rfl fun p _ =>
            (sum_validClusterFinset_multiPolymer_eq_raw hC_RCA_ge_one hβ_nn hR_le
              D_field h_valid sys h_sys_checks h_tqo1 h_tqo2 V d_loc hσ).1
        _ = ∑ ξ_list ∈ worldlineJumpListFinsetOfLength D_field R_cut m,
            singleSectorWorldlineDysonJumpWeight D_field sys R_cut β V d_loc σ ξ_list :=
          sum_validClusterFinset_raw_eq_sum_singleSector hr0_le hC_RCA_ge_one D_field sys
            h_sys_checks h_geom V d_loc hd_collar hσ hm1
  let S_mon := worldlineAllJumpMonomerFinset D_field R_cut
  obtain ⟨M_op, hM_op_def⟩ : ∃ x : ℝ, x = ∑ ξ ∈ S_mon, ‖worldlineSyndromeShiftBlockOp D_field sys V ξ‖ := ⟨_, rfl⟩
  have hM_op_nn : 0 ≤ M_op := by rw [hM_op_def]; exact Finset.sum_nonneg (fun _ _ => norm_nonneg _)
  obtain ⟨E_max, hE_max_def⟩ : ∃ x : ℝ,
      x = ∑ η : IdxCSS[L, q_code, m_max] → Bool, |sys.syndromeEnergy η - sys.syndromeEnergy σ| := ⟨_, rfl⟩
  have hE_max_nn : 0 ≤ E_max := by rw [hE_max_def]; exact Finset.sum_nonneg (fun _ _ => abs_nonneg _)
  obtain ⟨D_ϑ, hD_ϑ_def⟩ : ∃ g : (ℕ × Finset (Box3D L)) → ℝ,
      ∀ ϑ, g ϑ = ∑ η : IdxCSS[L, q_code, m_max] → Bool, |d_loc ϑ.1 ϑ.2 η - d_loc ϑ.1 ϑ.2 σ| := ⟨_, fun _ => rfl⟩
  have hD_ϑ_nn : ∀ ϑ, 0 ≤ D_ϑ ϑ := fun ϑ => by rw [hD_ϑ_def ϑ]; exact Finset.sum_nonneg (fun _ _ => abs_nonneg _)
  obtain ⟨B_pair, hB_pair_def⟩ : ∃ x : ℝ,
      x = Real.exp (β * E_max) * ∏ ϑ ∈ worldlineScaleCubeFinset L R_cut, (Real.exp (β * D_ϑ ϑ) + 1) := ⟨_, rfl⟩
  have hB_pair_ge_one : 1 ≤ B_pair := by
    rw [hB_pair_def]
    have h1 : 1 ≤ Real.exp (β * E_max) := Real.one_le_exp (mul_nonneg hβ_nn hE_max_nn)
    have h2 : 1 ≤ ∏ ϑ ∈ worldlineScaleCubeFinset L R_cut, (Real.exp (β * D_ϑ ϑ) + 1) :=
      Finset.prod_induction _ (fun x => 1 ≤ x)
        (fun _ _ ha hb => one_le_mul_of_one_le_of_one_le ha hb)
        le_rfl (fun ϑ _ => by linarith [Real.exp_pos (β * D_ϑ ϑ)])
    exact one_le_mul_of_one_le_of_one_le h1 h2
  have hB_pair_nn : 0 ≤ B_pair := le_trans zero_le_one hB_pair_ge_one
  obtain ⟨C_pow, hC_pow_def⟩ : ∃ x : ℝ,
      x = ((worldlineScaleCubeFinset L R_cut).powerset.card : ℝ) * B_pair := ⟨_, rfl⟩
  have hC_pow_nn : 0 ≤ C_pow := by rw [hC_pow_def]; exact mul_nonneg (Nat.cast_nonneg _) hB_pair_nn
  have h_abs_cl_le_raw : ∀ (m p : ℕ),
      (∑ K ∈ validClusterFinsetOfLenAndTotalJump D_field sys C_RCA R_cut m p, |w_cl K|) ≤
      ∑ K ∈ validClusterFinsetOfLenAndTotalJump D_field sys C_RCA R_cut m p, |w_raw K| :=
    fun m p => (sum_validClusterFinset_multiPolymer_eq_raw hC_RCA_ge_one hβ_nn hR_le
      D_field h_valid sys h_sys_checks h_tqo1 h_tqo2 V d_loc hσ).2
  have h_sum_abs_m_le : ∀ m : ℕ,
      (∑ K ∈ S_cl_m m, |w_cl K|) ≤
        C_pow * (((S_mon.card : ℝ) * (M_op * β)) ^ m / (m.factorial : ℝ)) := by
    intro m; dsimp [S_cl_m]
    by_cases hm0 : m = 0
    · subst hm0
      rw [if_pos rfl, Finset.sum_singleton, pow_zero, Nat.factorial_zero, Nat.cast_one, div_one, mul_one]
      have h_w0 := h_sum_m_eq 0; dsimp [S_cl_m] at h_w0
      rw [(worldlineJumpListFinsetOfLength_zero_and_succ D_field R_cut).1,
        Finset.sum_singleton, Finset.sum_singleton] at h_w0
      unfold singleSectorWorldlineDysonJumpWeight at h_w0
      rw [if_pos rfl] at h_w0; rw [h_w0, abs_one, hC_pow_def]
      have h_pow_ge1 : (1 : ℝ) ≤ ((worldlineScaleCubeFinset L R_cut).powerset.card : ℝ) := by
        rw [Finset.card_powerset]; exact_mod_cast Nat.one_le_two_pow
      exact one_le_mul_of_one_le_of_one_le h_pow_ge1 hB_pair_ge_one
    · rw [if_neg hm0, Finset.sum_biUnion (h_disj_p m)]
      have hm1 : 1 ≤ m := Nat.pos_of_ne_zero hm0
      obtain ⟨F_abs, hF_abs_def⟩ : ∃ G : List (WorldlineJumpMonomer L q_code) → Finset (ℕ × Finset (Box3D L)) → ℝ,
          ∀ ξ_list Θ, G ξ_list Θ =
            |hilbertTrace (sys.syndromeProjector σ *
              worldlinePolymerWeightedLoopOp D_field sys V (ξ_list, Θ)) /
              hilbertTrace (sys.syndromeProjector σ)| *
            |∫ τ : Fin ξ_list.length → ℝ,
              if InOrderedDysonSimplex β τ then
                Real.exp (-worldlineBareAction D_field sys ξ_list σ β τ) *
                  ∏ ϑ ∈ Θ, worldlineMayerBondFactor D_field ξ_list d_loc σ β ϑ τ
              else 0| := ⟨_, fun _ _ => rfl⟩
      have h_raw_abs_le : ∀ p ∈ Finset.Icc 1 m,
          ∀ K ∈ validClusterFinsetOfLenAndTotalJump D_field sys C_RCA R_cut m p,
          |w_raw K| ≤ ((Nat.factorial p : ℝ)⁻¹) *
            ∑ ξ_list ∈ multiPolymerShuffleFinset D_field R_cut K,
              F_abs ξ_list (K.foldr (fun γ acc => γ.2 ∪ acc) ∅) := by
        intro p _ K hK
        rcases (mem_validClusterFinsetOfLenAndTotalJump_iff D_field sys C_RCA R_cut m p K).mp hK with
          ⟨h_len, _, h_val, h_pw⟩
        have hp_inv_pos : 0 < ((Nat.factorial p : ℝ)⁻¹) :=
          inv_pos.mpr (Nat.cast_pos.mpr (Nat.factorial_pos p))
        dsimp [w_raw]
        rw [worldlineDysonRawClusterWeight_eq_sum_multiPolymerShuffleFinset
          hr0_le hC_RCA_ge_one D_field sys h_sys_checks h_geom V d_loc hd_collar hσ K h_val h_pw,
          h_len, abs_mul, abs_of_pos hp_inv_pos]
        refine mul_le_mul_of_nonneg_left ((Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun ξ_list _ => ?_))
          hp_inv_pos.le
        rw [hF_abs_def, abs_mul, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul]
      have h_F_abs_le : ∀ ξ_list ∈ validClosedJumpListFinset D_field R_cut m,
          ∀ Θ ∈ connMayerFinset sys C_RCA R_cut ξ_list,
          F_abs ξ_list Θ ≤ B_pair * ((M_op * β) ^ m / (m.factorial : ℝ)) := by
        intro ξ_list hξ_list Θ hΘ
        rcases (mem_worldlineJumpListFinsetOfLength_iff_local D_field R_cut m ξ_list).mp
          (Finset.mem_filter.mp hξ_list).1 with ⟨hξ_len, hξ_all⟩
        have hΘ_sub : Θ ⊆ worldlineScaleCubeFinset L R_cut :=
          Finset.mem_powerset.mp (Finset.mem_filter.mp hΘ).1
        have hP : IsStarProjection (sys.syndromeProjector σ) :=
          (PerturbedThermalBarrier.syndrome_resolution_indexed sys).2.1 σ
        have h_tr_le : |hilbertTrace (sys.syndromeProjector σ *
            worldlinePolymerWeightedLoopOp D_field sys V (ξ_list, Θ)) /
            hilbertTrace (sys.syndromeProjector σ)| ≤ M_op ^ ξ_list.length := by
          calc |hilbertTrace (sys.syndromeProjector σ *
                worldlinePolymerWeightedLoopOp D_field sys V (ξ_list, Θ)) /
                hilbertTrace (sys.syndromeProjector σ)|
            _ ≤ ‖worldlinePolymerWeightedLoopOp D_field sys V (ξ_list, Θ)‖ :=
                abs_hilbertTrace_isStarProjection_mul_div_le (sys.syndromeProjector σ) _ hP
            _ ≤ (ξ_list.map (fun ξ => ‖worldlineSyndromeShiftBlockOp D_field sys V ξ‖)).prod :=
                worldlinePolymerWeightedLoopOp_norm_le D_field sys V (ξ_list, Θ)
            _ ≤ (ξ_list.map (fun _ => M_op)).prod := by
                apply list_prod_le_prod_map _ _ _ (fun _ _ => norm_nonneg _)
                intro ξ hξ; rw [hM_op_def]; exact Finset.single_le_sum (fun _ _ => norm_nonneg _) (hξ_all ξ hξ)
            _ = M_op ^ ξ_list.length := by simp
        have h_int_le : |∫ τ : Fin ξ_list.length → ℝ,
            if InOrderedDysonSimplex β τ then
              Real.exp (-worldlineBareAction D_field sys ξ_list σ β τ) *
                ∏ ϑ ∈ Θ, worldlineMayerBondFactor D_field ξ_list d_loc σ β ϑ τ
            else 0| ≤ ((β ^ ξ_list.length) / (ξ_list.length.factorial : ℝ)) * B_pair := by
          apply SpacetimeWorldlineKP.abs_integral_kpOrderedDysonSimplex_le hβ_nn hB_pair_nn
          intro τ _
          have h_bare_le : -worldlineBareAction D_field sys ξ_list σ β τ ≤ β * E_max := by
            refine (neg_le_abs _).trans ?_
            apply SpacetimeWorldlineKP.abs_setIntegral_Icc_le_of_abs_le hβ_nn hE_max_nn
            intro t _; rw [hE_max_def]
            exact Finset.single_le_sum
              (f := fun η => |sys.syndromeEnergy η - sys.syndromeEnergy σ|)
              (fun η _ => abs_nonneg _) (Finset.mem_univ _)
          rw [abs_mul, abs_of_pos (Real.exp_pos _), Finset.abs_prod, hB_pair_def]
          refine mul_le_mul (Real.exp_le_exp.mpr h_bare_le) ?_
            (Finset.prod_nonneg (fun ϑ _ => abs_nonneg _)) (Real.exp_pos _).le
          calc (∏ ϑ ∈ Θ, |worldlineMayerBondFactor D_field ξ_list d_loc σ β ϑ τ|)
            _ ≤ ∏ ϑ ∈ Θ, (Real.exp (β * D_ϑ ϑ) + 1) := by
                refine Finset.prod_le_prod₀ (fun ϑ _ => abs_nonneg _) fun ϑ _ => ?_
                dsimp [worldlineMayerBondFactor]
                have h_d_le : -(∫ t in Set.Icc 0 β,
                    (d_loc ϑ.1 ϑ.2 (worldlineTrajectorySyndrome D_field ξ_list σ τ t) - d_loc ϑ.1 ϑ.2 σ)) ≤
                    β * D_ϑ ϑ := by
                  refine (neg_le_abs _).trans ?_
                  apply SpacetimeWorldlineKP.abs_setIntegral_Icc_le_of_abs_le hβ_nn (hD_ϑ_nn ϑ)
                  intro t _; rw [hD_ϑ_def ϑ]
                  exact Finset.single_le_sum
                    (f := fun η => |d_loc ϑ.1 ϑ.2 η - d_loc ϑ.1 ϑ.2 σ|)
                    (fun η _ => abs_nonneg _) (Finset.mem_univ _)
                calc |Real.exp (-(∫ t in Set.Icc 0 β,
                      (d_loc ϑ.1 ϑ.2 (worldlineTrajectorySyndrome D_field ξ_list σ τ t) - d_loc ϑ.1 ϑ.2 σ))) - 1|
                  _ ≤ Real.exp (-(∫ t in Set.Icc 0 β,
                        (d_loc ϑ.1 ϑ.2 (worldlineTrajectorySyndrome D_field ξ_list σ τ t) - d_loc ϑ.1 ϑ.2 σ))) + 1 := by
                      have := abs_sub (Real.exp (-(∫ t in Set.Icc 0 β,
                        (d_loc ϑ.1 ϑ.2 (worldlineTrajectorySyndrome D_field ξ_list σ τ t) - d_loc ϑ.1 ϑ.2 σ)))) 1
                      rwa [abs_of_pos (Real.exp_pos _), abs_one] at this
                  _ ≤ Real.exp (β * D_ϑ ϑ) + 1 := by linarith [Real.exp_le_exp.mpr h_d_le]
            _ ≤ ∏ ϑ ∈ worldlineScaleCubeFinset L R_cut, (Real.exp (β * D_ϑ ϑ) + 1) := by
                rw [← Finset.prod_sdiff hΘ_sub]
                exact le_mul_of_one_le_left
                  (Finset.prod_nonneg fun ϑ _ => by linarith [Real.exp_pos (β * D_ϑ ϑ)])
                  (Finset.prod_induction _ (fun x => 1 ≤ x)
                    (fun _ _ ha hb => one_le_mul_of_one_le_of_one_le ha hb)
                    le_rfl (fun ϑ _ => by linarith [Real.exp_pos (β * D_ϑ ϑ)]))
        rw [hF_abs_def]
        calc |hilbertTrace (sys.syndromeProjector σ *
              worldlinePolymerWeightedLoopOp D_field sys V (ξ_list, Θ)) /
              hilbertTrace (sys.syndromeProjector σ)| *
            |∫ τ : Fin ξ_list.length → ℝ,
              if InOrderedDysonSimplex β τ then
                Real.exp (-worldlineBareAction D_field sys ξ_list σ β τ) *
                  ∏ ϑ ∈ Θ, worldlineMayerBondFactor D_field ξ_list d_loc σ β ϑ τ
              else 0|
          _ ≤ (M_op ^ ξ_list.length) * (((β ^ ξ_list.length) / (ξ_list.length.factorial : ℝ)) * B_pair) :=
              mul_le_mul h_tr_le h_int_le (abs_nonneg _) (pow_nonneg hM_op_nn _)
          _ = B_pair * ((M_op * β) ^ m / (m.factorial : ℝ)) := by rw [hξ_len, mul_pow]; ring
      calc (∑ p ∈ Finset.Icc 1 m,
            ∑ K ∈ validClusterFinsetOfLenAndTotalJump D_field sys C_RCA R_cut m p, |w_cl K|)
        _ ≤ ∑ p ∈ Finset.Icc 1 m,
            ∑ K ∈ validClusterFinsetOfLenAndTotalJump D_field sys C_RCA R_cut m p, |w_raw K| :=
            Finset.sum_le_sum fun p _ => h_abs_cl_le_raw m p
        _ ≤ ∑ p ∈ Finset.Icc 1 m,
            ∑ K ∈ validClusterFinsetOfLenAndTotalJump D_field sys C_RCA R_cut m p,
              ((Nat.factorial p : ℝ)⁻¹) *
                ∑ ξ_list ∈ multiPolymerShuffleFinset D_field R_cut K,
                  F_abs ξ_list (K.foldr (fun γ acc => γ.2 ∪ acc) ∅) :=
            Finset.sum_le_sum fun p hp => Finset.sum_le_sum fun K hK => h_raw_abs_le p hp K hK
        _ = ∑ ξ_list ∈ validClosedJumpListFinset D_field R_cut m,
            ∑ Θ ∈ connMayerFinset sys C_RCA R_cut ξ_list, F_abs ξ_list Θ :=
            sum_validClusterFinset_multiPolymerShuffleFinset_eq_sum_validClosedJumpList
              D_field sys (fun idx => (h_sys_checks idx).2.1) h_geom hr0_le hm1 F_abs
        _ ≤ ∑ _ξ_list ∈ validClosedJumpListFinset D_field R_cut m,
            ∑ _Θ ∈ (worldlineScaleCubeFinset L R_cut).powerset,
              B_pair * ((M_op * β) ^ m / (m.factorial : ℝ)) := by
            refine Finset.sum_le_sum fun ξ_list hξ_list => ?_
            refine (Finset.sum_le_sum fun Θ hΘ => h_F_abs_le ξ_list hξ_list Θ hΘ).trans ?_
            exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
              (fun _ _ _ => mul_nonneg hB_pair_nn (div_nonneg (pow_nonneg (mul_nonneg hM_op_nn hβ_nn) _) (Nat.cast_nonneg _)))
        _ = ((validClosedJumpListFinset D_field R_cut m).card : ℝ) *
            (C_pow * ((M_op * β) ^ m / (m.factorial : ℝ))) := by
            simp only [Finset.sum_const, nsmul_eq_mul, hC_pow_def]; ring
        _ ≤ ((S_mon.card : ℝ) ^ m) * (C_pow * ((M_op * β) ^ m / (m.factorial : ℝ))) := by
            refine mul_le_mul_of_nonneg_right ?_
              (mul_nonneg hC_pow_nn (div_nonneg (pow_nonneg (mul_nonneg hM_op_nn hβ_nn) _) (Nat.cast_nonneg _)))
            have h_card_le : (validClosedJumpListFinset D_field R_cut m).card ≤ S_mon.card ^ m :=
              (Finset.card_le_card (Finset.filter_subset _ _)).trans
                (card_worldlineJumpListFinsetOfLength_le_pow D_field R_cut m)
            exact_mod_cast h_card_le
        _ = C_pow * (((S_mon.card : ℝ) * (M_op * β)) ^ m / (m.factorial : ℝ)) := by rw [mul_pow]; ring
  have h_sum_abs_m : Summable (fun m : ℕ => ∑ K ∈ S_cl_m m, |w_cl K|) :=
    Summable.of_nonneg_of_le (fun m => Finset.sum_nonneg fun K _ => abs_nonneg _) h_sum_abs_m_le
      ((Real.summable_pow_div_factorial ((S_mon.card : ℝ) * (M_op * β))).mul_left C_pow)
  have h_summable_cl : Summable w_cl := by
    rw [← summable_norm_iff]
    refine summable_of_sum_le (fun K => norm_nonneg (w_cl K))
      (c := ∑' m : ℕ, ∑ K ∈ S_cl_m m, |w_cl K|) fun u => ?_
    let N := u.sup totalJump
    have h_sub_sum : ∑ K ∈ u, ‖w_cl K‖ ≤ ∑ m ∈ Finset.range (N + 1), ∑ K ∈ S_cl_m m, |w_cl K| := by
      simp_rw [Real.norm_eq_abs]
      rw [← Finset.sum_biUnion, ← Finset.sum_filter_ne_zero]
      · refine Finset.sum_le_sum_of_subset_of_nonneg (fun K hK => ?_) (fun _ _ _ => abs_nonneg _)
        obtain ⟨hK_u, h_ne⟩ := Finset.mem_filter.mp hK
        have h_in : K ∈ S_cl_m (totalJump K) := by
          by_contra h_not
          exact h_ne (by rw [h_zero_outside_cl (totalJump K) K rfl h_not, abs_zero])
        exact Finset.mem_biUnion.mpr ⟨totalJump K,
          Finset.mem_range.mpr (Nat.lt_succ_of_le (Finset.le_sup hK_u)), h_in⟩
      · intro m₁ _ m₂ _ h_ne
        rw [Function.onFun, Finset.disjoint_left]
        intro K hK₁ hK₂
        have h_tot : ∀ m, K ∈ S_cl_m m → totalJump K = m := by
          intro m hKm; dsimp [S_cl_m] at hKm
          by_cases hm0 : m = 0
          · subst hm0; rw [if_pos rfl, Finset.mem_singleton] at hKm; subst hKm; rfl
          · rw [if_neg hm0, Finset.mem_biUnion] at hKm
            rcases hKm with ⟨p, _, hpK⟩
            exact ((mem_validClusterFinsetOfLenAndTotalJump_iff D_field sys C_RCA R_cut m p K).mp hpK).2.1
        exact h_ne ((h_tot m₁ hK₁).symm.trans (h_tot m₂ hK₂))
    exact h_sub_sum.trans (h_sum_abs_m.sum_le_tsum (Finset.range (N + 1))
      (fun m _ => Finset.sum_nonneg fun K _ => abs_nonneg _))
  let e_sigma : (Σ m : ℕ, {K : WorldlineUrsellCluster L q_code // totalJump K = m}) ≃
      WorldlineUrsellCluster L q_code := Equiv.sigmaFiberEquiv totalJump
  have h_summable_sigma : Summable (w_cl ∘ e_sigma) := (Equiv.summable_iff e_sigma).mpr h_summable_cl
  rw [h_tsum_single, ← Equiv.tsum_eq e_sigma w_cl]
  change (∑' m : ℕ, ∑ ξ_list ∈ worldlineJumpListFinsetOfLength D_field R_cut m,
      singleSectorWorldlineDysonJumpWeight D_field sys R_cut β V d_loc σ ξ_list) =
    ∑' p, (w_cl ∘ e_sigma) p
  rw [Summable.tsum_sigma h_summable_sigma]
  refine tsum_congr fun m => ?_
  rw [← h_sum_m_eq m, tsum_eq_sum (s := (S_cl_m m).subtype (fun K => totalJump K = m))]
  · symm
    refine Finset.sum_bij (fun (x : {K : WorldlineUrsellCluster L q_code // totalJump K = m}) _ => x.1)
      (fun x hx => Finset.mem_subtype.mp hx)
      (fun _ _ _ _ h => Subtype.ext h)
      (fun K hK => by
        have h_tot : totalJump K = m := by
          dsimp [S_cl_m] at hK
          by_cases hm0 : m = 0
          · subst hm0; rw [if_pos rfl, Finset.mem_singleton] at hK; subst hK; rfl
          · rw [if_neg hm0, Finset.mem_biUnion] at hK
            rcases hK with ⟨p, _, hpK⟩
            exact ((mem_validClusterFinsetOfLenAndTotalJump_iff D_field sys C_RCA R_cut m p K).mp hpK).2.1
        exact ⟨⟨K, h_tot⟩, Finset.mem_subtype.mpr hK, rfl⟩)
      (fun _ _ => rfl)
  · intro x hx
    rw [Finset.mem_subtype] at hx
    exact h_zero_outside_cl m x.1 x.2 hx

lemma hilbertTrace_gibbsBoltzmannOp_syndromeProjector_eq_tsum_dysonMultiPolymerClusterWeight_duhamel
    {L q_code r_0 m_max w_0 L_star R_cut : ℕ} [NeZero L]
    {C_RCA β Δ_RCA C_wl c_wl J : ℝ}
    (D_field : Box3D L → LocalCSSDescriptor q_code r_0 m_max) (h_valid : ValidDescriptorField D_field)
    (sys : SysCSS[L, q_code, m_max])
    (h_sys_checks : ∀ idx, sys.checkProj idx = staticCSSCheckProj D_field idx ∧
      sys.support idx = staticCSSCheckSupport D_field idx ∧ sys.weight idx = 1)
    (h_geom : sys.IsGeometricallyLocal r_0 w_0)
    (h_tqo1 : SatisfiesTQO1 sys L_star) (h_tqo2 : SatisfiesSectorFilteredLinearTQO2 sys 1 L_star C_RCA)
    (V : QuasiLocalPerturbation 3 L (SiteCSS[L, q_code])) (f : ℕ → ℝ)
    (hf_nn : ∀ r, 0 ≤ f r) (hf_le_one : ∀ r, f r ≤ 1)
    (hV_norm : ∀ r ∈ Finset.Icc 1 (min R_cut L), ∀ A ∈ boxCubes 3 L r, ‖V.term r A‖ ≤ J * f r)
    (e_loc : ℕ → Finset (Box3D L) → ℝ)
    (d_loc : ℕ → Finset (Box3D L) → (IdxCSS[L, q_code, m_max] → Bool) → ℝ)
    (hd_scale : ∀ r ∈ Finset.Icc 1 (min R_cut L), ∀ A ∈ boxCubes 3 L r,
      ∀ σ, |d_loc r A σ| ≤ 2 * (J * f r))
    (h_scalar : IsLocalCollarScalarFamily D_field sys R_cut C_RCA J V e_loc d_loc)
    (hH_trunc : IsSelfAdjoint (sys.H0 + scaleSplitTruncatedOp V R_cut))
    (hR_cut : 1 ≤ R_cut) (hR_le : R_cut ≤ L_star)
    (h_scale_cal : SatisfiesWorldlineScaleCalibration L L_star R_cut r_0 C_RCA) (hC_RCA : 0 ≤ C_RCA)
    (hC_wl_cal : (kpCollarMaxCheckCard R_cut r_0 w_0 C_RCA : ℝ) ≤ C_wl)
    (hc_wl_cal : (kpCollarMaxCheckCard R_cut r_0 w_0 C_RCA : ℝ) ≤ c_wl)
    (hβ : 16 < β) (hJ_pos : 0 < J)
    (h_sum_pos : 0 < worldlineNativeKPSum f C_wl c_wl β R_cut)
    (h_thresh : J ≤ worldlineSpanningThreshold Δ_RCA C_wl c_wl β f R_cut)
    {σ : IdxCSS[L, q_code, m_max] → Bool}
    (hσ : σ ∈ realizableSyndromes D_field) :
    let E_vac := ∑ r ∈ Finset.Icc 1 (min R_cut L), ∑ A ∈ boxCubes 3 L r, e_loc r A
    let K_norm := hilbertTrace sys.P0 * Real.exp (-β * E_vac)
    hilbertTrace (gibbsBoltzmannOp
      (opEigenbasis (sys.H0 + scaleSplitTruncatedOp V R_cut) hH_trunc)
      (opEigenvalues (sys.H0 + scaleSplitTruncatedOp V R_cut) hH_trunc) β *
        sys.syndromeProjector σ) =
      K_norm *
        (Real.exp (-β * pauliDiagonalSectorEnergy sys R_cut d_loc σ) *
          ∑' K : WorldlineUrsellCluster L q_code,
            worldlineDysonMultiPolymerClusterWeight D_field sys C_RCA R_cut β V d_loc σ K) := by
  (try dsimp only)
  rw [(hilbertTrace_gibbsBoltzmannOp_syndromeProjector_eq_tsum_singleSectorJumpWeight
    D_field h_valid sys h_sys_checks h_geom h_tqo1 h_tqo2 V f hf_nn hf_le_one hV_norm e_loc d_loc
    hd_scale h_scalar hH_trunc hR_cut hR_le h_scale_cal hC_RCA hC_wl_cal hc_wl_cal hβ hJ_pos
    h_sum_pos h_thresh hσ).2,
    tsum_singleSectorWorldlineDysonJumpWeight_eq_tsum_dysonMultiPolymerClusterWeight
    D_field h_valid sys h_sys_checks h_geom h_tqo1 h_tqo2 V f hf_nn hf_le_one hV_norm e_loc d_loc
    hd_scale h_scalar hR_cut hR_le h_scale_cal hC_RCA hC_wl_cal hc_wl_cal hβ hJ_pos h_sum_pos
    h_thresh hσ]

end DirectWorldlineCluster
end
