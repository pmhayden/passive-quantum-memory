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

import Proofs.DirectWorldlineCluster.WorldlineDysonUrsellMultiPolymer

/-!
# Global Spanning Check Surfaces, Time-Reversal Pairing, and Logical Coset Commutativity

Constructs global spanning check surfaces for closed commuting Pauli loops (`exists_global_spanning_surface_of_commute_syndromeClosed`) and relates stabilizer check parity to ground-space projection on `P0`. Establishes time-reversal symmetry of ordered Dyson simplex integrals (`integral_inOrderedDysonSimplex_reverse_polymer_eq`, `flipCluster_invariants`) ensuring real-valued symmetrized polymer weights.

## References

* Part II, Section 3.5 (`subsec:worldline-expansion`), Lemma 3.9 (`lem:worldline-factorization-time-reversal`)
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

/-!
## 1. Multi-Polymer Spanning Surface, CSS Stabilizer Orthogonality, and Time-Reversal Identities

Establishes multi-polymer spanning-surface parity sign identities, CSS stabilizer orthogonality on `sys.P0`, Mayer–Ursell subgraph decompositions, and time-reversal adjoint identities (Part II, Section 3.5 (`subsec:worldline-expansion`), Lemma 3.9 (`lem:worldline-factorization-time-reversal`) and Proposition 3.10 (`prop:tube-local-ursell-erasure`)).
-/

/-- Multi-polymer character average over $\nu \in \mathcal{G}_{\mathrm{closed}}$ of the product
of character-twisted polymer weights $\prod_{\gamma \in K} w_\nu(\gamma; \sigma)$ expressed via
the net loop bitstring sum $\sum_{\gamma \in K} (a(\gamma), b(\gamma))$ (Part II, Section 3.5 (`subsec:worldline-expansion`), Lemma 3.9 (`lem:worldline-factorization-time-reversal`)). -/
lemma multiPolymer_logical_character_average_eq_loop
    {L q_code r_0 m_max R_cut : ℕ} [NeZero L] {C_RCA β : ℝ}
    (D_field : Box3D L → LocalCSSDescriptor q_code r_0 m_max) (h_valid : ValidDescriptorField D_field)
    (sys : SysCSS[L, q_code, m_max])
    (h_sys_checks : ∀ idx, sys.checkProj idx = staticCSSCheckProj D_field idx ∧
      sys.support idx = staticCSSCheckSupport D_field idx ∧ sys.weight idx = 1)
    (V : QuasiLocalPerturbation 3 L (SiteCSS[L, q_code]))
    (d_loc : ℕ → Finset (Box3D L) → (IdxCSS[L, q_code, m_max] → Bool) → ℝ)
    (K : WorldlineUrsellCluster L q_code)
    (hK_valid : ∀ γ ∈ K, IsValidWorldlinePolymer D_field sys C_RCA R_cut γ)
    (σ : IdxCSS[L, q_code, m_max] → Bool) :
    (∑ ν ∈ syndromeClosedPauliFinset D_field,
      (((syndromeClosedPauliFinset D_field).card : ℝ))⁻¹ *
        (K.map (fun γ => worldlinePolymerWeight D_field sys C_RCA β V d_loc ν γ σ)).prod) =
    if ∀ ν ∈ syndromeClosedPauliFinset D_field,
        symplecticPauliSign ν (K.map (fun γ => (worldlinePolymerLoopX γ, worldlinePolymerLoopZ γ))).sum = 1 then
      (K.map (fun γ =>
        spanningSurfaceSign (worldlinePolymerSpanningSurface D_field sys C_RCA γ) σ *
          worldlinePolymerMicroWeight D_field sys C_RCA β V d_loc γ
            (restrictSyndromeToCollar (worldlinePolymerNativeCollar sys C_RCA γ) σ))).prod
    else 0 := by
  rw [multiPolymer_logical_character_average_eq D_field sys V d_loc K σ]
  have h_iff :
      (∀ ν ∈ syndromeClosedPauliFinset D_field,
        symplecticPauliSign ν (K.map (worldlinePolymerLogicalCoset D_field sys C_RCA)).sum = 1) ↔
      (∀ ν ∈ syndromeClosedPauliFinset D_field,
        symplecticPauliSign ν (K.map (fun γ => (worldlinePolymerLoopX γ, worldlinePolymerLoopZ γ))).sum = 1) :=
    forall₂_congr fun ν hν => by
      rw [symplecticPauliSign_list_sum_worldlinePolymerLogicalCoset_eq_loop D_field h_valid sys h_sys_checks K hK_valid hν]
  by_cases h_cond : ∀ ν ∈ syndromeClosedPauliFinset D_field,
      symplecticPauliSign ν (K.map (fun γ => (worldlinePolymerLoopX γ, worldlinePolymerLoopZ γ))).sum = 1
  · rw [if_pos (h_iff.mpr h_cond), if_pos h_cond]
  · rw [if_neg (mt h_iff.mp h_cond), if_neg h_cond]

/-- Simultaneous vanishing of the multi-polymer weighted loop sector trace and the logical character
average when the net loop Pauli operator anticommutes with some $\nu_0 \in \mathcal{G}_{\mathrm{closed}}$
(Part II, Section 3.2 (`subsec:rca1-pinching`), Proposition 3.4 (`prop:pauli-diag-off`) and Section 3.5 (`subsec:worldline-expansion`), Lemma 3.9 (`lem:worldline-factorization-time-reversal`)). -/
lemma multiPolymer_trace_and_character_average_eq_zero_of_anticomm
    {L q_code r_0 m_max L_star R_cut : ℕ} [NeZero L] {C_RCA β : ℝ}
    (D_field : Box3D L → LocalCSSDescriptor q_code r_0 m_max) (h_valid : ValidDescriptorField D_field)
    (sys : SysCSS[L, q_code, m_max])
    (h_sys_checks : ∀ idx, sys.checkProj idx = staticCSSCheckProj D_field idx ∧
      sys.support idx = staticCSSCheckSupport D_field idx ∧ sys.weight idx = 1)
    (h_tqo1 : SatisfiesTQO1 sys L_star) (h_tqo2 : SatisfiesSectorFilteredLinearTQO2 sys 1 L_star C_RCA)
    (hR_le : R_cut ≤ L_star) (V : QuasiLocalPerturbation 3 L (SiteCSS[L, q_code]))
    (d_loc : ℕ → Finset (Box3D L) → (IdxCSS[L, q_code, m_max] → Bool) → ℝ)
    (K : WorldlineUrsellCluster L q_code)
    (hK_valid : ∀ γ ∈ K, IsValidWorldlinePolymer D_field sys C_RCA R_cut γ)
    {σ₀ : IdxCSS[L, q_code, m_max] → Bool} (hσ₀ : σ₀ ∈ realizableSyndromes D_field)
    (h_not_all : ¬(∀ ν ∈ syndromeClosedPauliFinset D_field,
      symplecticPauliSign ν (K.map (fun γ => (worldlinePolymerLoopX γ, worldlinePolymerLoopZ γ))).sum = 1)) :
    hilbertTrace (sys.syndromeProjector σ₀ *
      (K.map (worldlinePolymerWeightedLoopOp D_field sys V)).prod) = 0 ∧
    (∑ ν ∈ syndromeClosedPauliFinset D_field,
      (((syndromeClosedPauliFinset D_field).card : ℝ))⁻¹ *
        (K.map (fun γ => worldlinePolymerWeight D_field sys C_RCA β V d_loc ν γ σ₀)).prod) = 0 := by
  push_neg at h_not_all; rcases h_not_all with ⟨ν₀, hν₀, h_ne_one⟩
  have h_anti : symplecticPauliSign ν₀
      (K.map (fun γ => (worldlinePolymerLoopX γ, worldlinePolymerLoopZ γ))).sum = -1 := by
    unfold symplecticPauliSign at h_ne_one ⊢; split_ifs at h_ne_one ⊢ with h_mod
    · rfl
    · exact False.elim (h_ne_one rfl)
  refine ⟨hilbertTrace_syndromeProjector_prod_worldlinePolymerWeightedLoopOp_eq_zero_of_anticomm
    D_field h_valid sys h_sys_checks h_tqo1 h_tqo2 hR_le V K hK_valid hσ₀ hν₀ h_anti, ?_⟩
  rw [multiPolymer_logical_character_average_eq_loop D_field h_valid sys h_sys_checks V d_loc K hK_valid σ₀,
    if_neg (fun h_all => h_ne_one (h_all ν₀ hν₀))]

/-- Hard-core truncation of `worldlineMayerPolymerClusterWeight` (Part II, Section 3.5 (`subsec:worldline-expansion`), Proposition 3.10 (`prop:tube-local-ursell-erasure`), Equation `eq:ursell-partition-sigma`). -/
lemma worldlineMayerPolymerClusterWeight_eq_zero_of_card_checks_lt_length
    {L q_code r_0 m_max w_0 R_cut : ℕ} [NeZero L]
    (D_field : Box3D L → LocalCSSDescriptor q_code r_0 m_max) (sys : SysCSS[L, q_code, m_max])
    (h_sys_supp : ∀ idx, sys.support idx = staticCSSCheckSupport D_field idx)
    (h_geom : sys.IsGeometricallyLocal r_0 w_0) {C_RCA β : ℝ} (hr0_le : 1 + 4 * (r_0 : ℝ) ≤ C_RCA)
    (V : QuasiLocalPerturbation 3 L (SiteCSS[L, q_code]))
    (d_loc : ℕ → Finset (Box3D L) → (IdxCSS[L, q_code, m_max] → Bool) → ℝ)
    (ν : PauliBitstringPair L q_code) (σ : IdxCSS[L, q_code, m_max] → Bool)
    (K : WorldlineUrsellCluster L q_code) (h_lt : Fintype.card (IdxCSS[L, q_code, m_max]) < K.length) :
    worldlineMayerPolymerClusterWeight D_field sys C_RCA R_cut β V d_loc ν σ K = 0 := by
  unfold worldlineMayerPolymerClusterWeight
  split_ifs with hK
  · exfalso
    have h_le := length_le_card_checks_of_valid_and_pairwise_compatible
      (R_cut := R_cut) D_field sys h_sys_supp h_geom hr0_le K hK.1 hK.2
    omega
  · rfl

/-- Evaluation of `worldlineMayerPolymerClusterWeight` on `[]` and `[γ]` (Part II, Section 3.5 (`subsec:worldline-expansion`), Proposition 3.10 (`prop:tube-local-ursell-erasure`), Equation `eq:ursell-partition-sigma`). -/
lemma worldlineMayerPolymerClusterWeight_nil_and_singleton
    {L q_code r_0 m_max R_cut : ℕ} [NeZero L]
    (D_field : Box3D L → LocalCSSDescriptor q_code r_0 m_max)
    (sys : SysCSS[L, q_code, m_max]) (C_RCA β : ℝ)
    (V : QuasiLocalPerturbation 3 L (SiteCSS[L, q_code]))
    (d_loc : ℕ → Finset (Box3D L) → (IdxCSS[L, q_code, m_max] → Bool) → ℝ)
    (ν : PauliBitstringPair L q_code) (σ : IdxCSS[L, q_code, m_max] → Bool)
    (γ : WorldlineDysonPolymer L q_code) :
    worldlineMayerPolymerClusterWeight D_field sys C_RCA R_cut β V d_loc ν σ [] = 1 ∧
    worldlineMayerPolymerClusterWeight D_field sys C_RCA R_cut β V d_loc ν σ [γ] =
      if IsValidWorldlinePolymer D_field sys C_RCA R_cut γ then
        worldlinePolymerWeight D_field sys C_RCA β V d_loc ν γ σ
      else 0 := by
  refine ⟨by unfold worldlineMayerPolymerClusterWeight; rw [if_pos ⟨fun _ h => False.elim (List.not_mem_nil h), List.Pairwise.nil⟩]; norm_num, ?_⟩
  unfold worldlineMayerPolymerClusterWeight
  by_cases hγ : IsValidWorldlinePolymer D_field sys C_RCA R_cut γ
  · rw [if_pos ⟨fun γ' hγ' => by rcases List.mem_singleton.mp hγ' with rfl; exact hγ, List.pairwise_singleton _ γ⟩, if_pos hγ]; simp
  · rw [if_neg (fun h => hγ (h.1 γ (List.mem_singleton_self γ))), if_neg hγ]

/-- Multi-polymer spanning-surface parity sign identity (Part II, Section 3.5 (`subsec:worldline-expansion`), Lemma 3.9 (`lem:worldline-factorization-time-reversal`), Equation `eq:P-gamma-spanning-surface`). -/
lemma prod_spanningSurfaceSign_worldlinePolymerSpanningSurface_eq_symplecticPauliSign
    {L q_code r_0 m_max R_cut : ℕ} [NeZero L] {C_RCA : ℝ}
    (D_field : Box3D L → LocalCSSDescriptor q_code r_0 m_max) (h_valid : ValidDescriptorField D_field)
    (sys : SysCSS[L, q_code, m_max])
    (h_sys_checks : ∀ idx, sys.checkProj idx = staticCSSCheckProj D_field idx ∧
      sys.support idx = staticCSSCheckSupport D_field idx ∧ sys.weight idx = 1)
    (K : WorldlineUrsellCluster L q_code)
    (hK_valid : ∀ γ ∈ K, IsValidWorldlinePolymer D_field sys C_RCA R_cut γ)
    (u v : BoxSlot3D L q_code → ZMod 2) :
    (K.map (fun γ => spanningSurfaceSign (worldlinePolymerSpanningSurface D_field sys C_RCA γ)
      (staticCSSPauliFlip D_field u v))).prod =
    symplecticPauliSign (u, v)
      ((K.map (worldlinePolymerLogicalCoset D_field sys C_RCA)).sum +
        (K.map (fun γ => (worldlinePolymerLoopX γ, worldlinePolymerLoopZ γ))).sum) := by
  have h_mul_right := (symplecticPauliSign_mul_and_orthogonality D_field).2.1
  induction K with
  | nil => simp [symplecticPauliSign]
  | cons hd tl ih =>
    simp only [List.map_cons, List.prod_cons, List.sum_cons]
    rw [add_add_add_comm (worldlinePolymerLogicalCoset D_field sys C_RCA hd)
      ((tl.map (worldlinePolymerLogicalCoset D_field sys C_RCA)).sum)
      (worldlinePolymerLoopX hd, worldlinePolymerLoopZ hd)
      ((tl.map (fun γ => (worldlinePolymerLoopX γ, worldlinePolymerLoopZ γ))).sum),
      h_mul_right,
      spanningSurfaceSign_worldlinePolymerSpanningSurface_eq_symplecticPauliSign
        D_field h_valid sys h_sys_checks (hK_valid hd List.mem_cons_self) u v,
      ih (fun γ hγ => hK_valid γ (List.mem_cons_of_mem hd hγ))]

/-- Evaluation of the connected-graph Ursell coefficient `ursellConnectedGraphCoeff` on a
2-polymer tuple `[γ₁, γ₂]` (Part II, Section 3.5 (`subsec:worldline-expansion`), Proposition 3.10 (`prop:tube-local-ursell-erasure`), Equation `eq:ursell-partition-sigma`):
`ursellConnectedGraphCoeff sys C_RCA [γ₁, γ₂] = (1 / 2 : ℝ) * (if ArePolymersIncompatible sys C_RCA γ₁ γ₂ then -1 else 0)`. -/
lemma ursellConnectedGraphCoeff_pair
    {L q_code m_max : ℕ} [NeZero L]
    (sys : SysCSS[L, q_code, m_max]) (C_RCA : ℝ)
    (γ₁ γ₂ : WorldlineDysonPolymer L q_code) :
    ursellConnectedGraphCoeff sys C_RCA [γ₁, γ₂] =
      (1 / 2 : ℝ) * (if ArePolymersIncompatible sys C_RCA γ₁ γ₂ then -1 else 0) := by
  let K : WorldlineUrsellCluster L q_code := [γ₁, γ₂]
  let i0 : Fin K.length := ⟨0, by simp [K]⟩
  let i1 : Fin K.length := ⟨1, by simp [K]⟩
  have hi01_ne : i0 ≠ i1 := fun h => by cases Fin.ext_iff.mp h
  have hi01_lt : i0 < i1 := Nat.zero_lt_one
  have h_fin2 : ∀ u : Fin K.length, u = i0 ∨ u = i1 := fun ⟨u_val, hu_lt⟩ => by
    have hu' : u_val < 2 := hu_lt
    rcases (by omega : u_val = 0 ∨ u_val = 1) with rfl | rfl <;> [exact Or.inl rfl; exact Or.inr rfl]
  have h_edge_i01 : ∀ e : Fin K.length × Fin K.length, e.1 < e.2 → e = (i0, i1) := by
    rintro ⟨⟨a_val, ha⟩, ⟨b_val, hb⟩⟩ hab
    have hab' : a_val < b_val := hab; have hb' : b_val < 2 := hb
    have ha0 : a_val = 0 := by omega
    have hb1 : b_val = 1 := by omega
    subst ha0 hb1; rfl
  have h_empty_not_conn : ¬KPIsConnectedSubgraph
      (fun a b : Fin K.length => (a, b) ∈ (∅ : Finset (Fin K.length × Fin K.length)) ∨
        (b, a) ∈ (∅ : Finset (Fin K.length × Fin K.length))) Finset.univ := fun h_conn => by
    have h_eq : ∀ u : Fin K.length, Relation.ReflTransGen
        (fun x y : Fin K.length => x ∈ (Finset.univ : Finset (Fin K.length)) ∧
          y ∈ (Finset.univ : Finset (Fin K.length)) ∧
          ((x, y) ∈ (∅ : Finset (Fin K.length × Fin K.length)) ∨
            (y, x) ∈ (∅ : Finset (Fin K.length × Fin K.length)))) i0 u → i0 = u := by
      intro u h_u; induction h_u with
      | refl => rfl
      | tail _ h_step => rcases h_step.2.2 with h | h <;> exact False.elim (Finset.notMem_empty _ h)
    exact hi01_ne (h_eq i1 (h_conn.2 i0 (Finset.mem_univ i0) i1 (Finset.mem_univ i1)))
  let E_compat : Finset (Fin K.length × Fin K.length) :=
    Finset.univ.filter (fun e => e.1 < e.2 ∧ PolymerClusterOverlap sys C_RCA K e.1 e.2)
  by_cases h_inc : ArePolymersIncompatible sys C_RCA γ₁ γ₂
  · rw [if_pos h_inc]
    have hE_eq : E_compat = {(i0, i1)} := by
      ext e; rw [Finset.mem_singleton, Finset.mem_filter]
      exact ⟨fun ⟨_, hab, _⟩ => h_edge_i01 e hab,
        fun he => by rw [he]; exact ⟨Finset.mem_univ _, hi01_lt, hi01_ne, h_inc⟩⟩
    have h_sing_conn : KPIsConnectedSubgraph
        (fun a b : Fin K.length => (a, b) ∈ ({(i0, i1)} : Finset (Fin K.length × Fin K.length)) ∨
          (b, a) ∈ ({(i0, i1)} : Finset (Fin K.length × Fin K.length))) Finset.univ := by
      refine ⟨⟨i0, Finset.mem_univ i0⟩, fun u _ v _ => ?_⟩
      rcases h_fin2 u with rfl | rfl <;> rcases h_fin2 v with rfl | rfl
      · exact Relation.ReflTransGen.refl
      · exact Relation.ReflTransGen.single ⟨Finset.mem_univ i0, Finset.mem_univ i1, Or.inl (Finset.mem_singleton_self _)⟩
      · exact Relation.ReflTransGen.single ⟨Finset.mem_univ i1, Finset.mem_univ i0, Or.inr (Finset.mem_singleton_self _)⟩
      · exact Relation.ReflTransGen.refl
    have h_filt_eq : E_compat.powerset.filter
        (fun G => KPIsConnectedSubgraph (fun a b => (a, b) ∈ G ∨ (b, a) ∈ G) Finset.univ) = {{(i0, i1)}} := by
      ext G; rw [Finset.mem_singleton, Finset.mem_filter, hE_eq, Finset.mem_powerset, Finset.subset_singleton_iff]
      exact ⟨fun ⟨h_sub, hG⟩ => by
        rcases h_sub with rfl | rfl <;> [exact False.elim (h_empty_not_conn hG); rfl],
        by rintro rfl; exact ⟨Or.inr rfl, h_sing_conn⟩⟩
    change ((Nat.factorial K.length : ℝ)⁻¹) *
      ∑ G ∈ E_compat.powerset.filter (fun G => KPIsConnectedSubgraph (fun a b => (a, b) ∈ G ∨ (b, a) ∈ G) Finset.univ),
        ((-1 : ℝ) ^ G.card) = (1 / 2 : ℝ) * -1
    rw [h_filt_eq, Finset.sum_singleton, Finset.card_singleton]
    change ((Nat.factorial 2 : ℝ)⁻¹) * ((-1 : ℝ) ^ 1) = (1 / 2 : ℝ) * -1; norm_num
  · rw [if_neg h_inc, mul_zero]
    have hE_empty : E_compat = ∅ := Finset.filter_eq_empty_iff.mpr fun e _ ⟨hab, h_ov⟩ => by
      have he := h_edge_i01 e hab; rw [he] at h_ov; exact h_inc h_ov.2
    have h_filt_empty : E_compat.powerset.filter
        (fun G => KPIsConnectedSubgraph (fun a b => (a, b) ∈ G ∨ (b, a) ∈ G) Finset.univ) = ∅ :=
      Finset.filter_eq_empty_iff.mpr fun G hG hG_conn => by
        rw [hE_empty, Finset.powerset_empty, Finset.mem_singleton] at hG; subst hG; exact h_empty_not_conn hG_conn
    change ((Nat.factorial K.length : ℝ)⁻¹) *
      ∑ G ∈ E_compat.powerset.filter (fun G => KPIsConnectedSubgraph (fun a b => (a, b) ∈ G ∨ (b, a) ∈ G) Finset.univ),
        ((-1 : ℝ) ^ G.card) = 0
    rw [h_filt_empty, Finset.sum_empty, mul_zero]

/-- Two-polymer Mayer–Ursell cancellation identity (Part II, Section 3.5 (`subsec:worldline-expansion`), Proposition 3.10 (`prop:tube-local-ursell-erasure`), Equation `eq:ursell-partition-sigma`): for any valid polymers `γ₁, γ₂`, subtracting the 2-polymer
connected Ursell weight `worldlineClusterUrsellWeight ... [γ₁, γ₂] σ` from the 2-polymer
compatible gas weight `worldlineMayerPolymerClusterWeight ... [γ₁, γ₂]` recovers the unconditioned
second-order exponential term `(1 / 2) * w_ν(γ₁; σ) * w_ν(γ₂; σ)`. -/
lemma worldlineMayerPolymerClusterWeight_and_ursell_pair
    {L q_code r_0 m_max R_cut : ℕ} [NeZero L]
    (D_field : Box3D L → LocalCSSDescriptor q_code r_0 m_max)
    (sys : SysCSS[L, q_code, m_max]) (C_RCA : ℝ) (β : ℝ)
    (V : QuasiLocalPerturbation 3 L (SiteCSS[L, q_code]))
    (d_loc : ℕ → Finset (Box3D L) → (IdxCSS[L, q_code, m_max] → Bool) → ℝ)
    (ν : PauliBitstringPair L q_code)
    (σ : IdxCSS[L, q_code, m_max] → Bool)
    {γ₁ γ₂ : WorldlineDysonPolymer L q_code}
    (hγ₁ : IsValidWorldlinePolymer D_field sys C_RCA R_cut γ₁)
    (hγ₂ : IsValidWorldlinePolymer D_field sys C_RCA R_cut γ₂) :
    worldlineMayerPolymerClusterWeight D_field sys C_RCA R_cut β V d_loc ν σ [γ₁, γ₂] -
      worldlineClusterUrsellWeight D_field sys C_RCA β V d_loc ν [γ₁, γ₂] σ =
    (1 / 2 : ℝ) *
      (worldlinePolymerWeight D_field sys C_RCA β V d_loc ν γ₁ σ *
        worldlinePolymerWeight D_field sys C_RCA β V d_loc ν γ₂ σ) := by
  unfold worldlineMayerPolymerClusterWeight worldlineClusterUrsellWeight
  rw [ursellConnectedGraphCoeff_pair sys C_RCA γ₁ γ₂]
  have h_valid_pair : ∀ γ ∈ ([γ₁, γ₂] : WorldlineUrsellCluster L q_code),
      IsValidWorldlinePolymer D_field sys C_RCA R_cut γ := fun γ hγ => by
    rcases List.mem_cons.mp hγ with rfl | h_tl
    · exact hγ₁
    · rcases List.mem_singleton.mp h_tl with rfl; exact hγ₂
  by_cases h_inc : ArePolymersIncompatible sys C_RCA γ₁ γ₂
  · have h_not_pw : ¬((∀ γ ∈ ([γ₁, γ₂] : WorldlineUrsellCluster L q_code),
        IsValidWorldlinePolymer D_field sys C_RCA R_cut γ) ∧
        ([γ₁, γ₂] : WorldlineUrsellCluster L q_code).Pairwise
          (fun a b => ¬ArePolymersIncompatible sys C_RCA a b)) :=
      fun ⟨_, h_pw⟩ => (List.pairwise_cons.mp h_pw).1 γ₂ (List.mem_singleton_self γ₂) h_inc
    rw [if_neg h_not_pw, if_pos h_inc]
    simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one]; ring
  · have h_pw : ([γ₁, γ₂] : WorldlineUrsellCluster L q_code).Pairwise
        (fun a b => ¬ArePolymersIncompatible sys C_RCA a b) :=
      List.pairwise_cons.mpr ⟨fun b hb => by rcases List.mem_singleton.mp hb with rfl; exact h_inc,
        List.pairwise_singleton _ γ₂⟩
    rw [if_pos ⟨h_valid_pair, h_pw⟩, if_neg h_inc]
    simp only [List.length_cons, List.length_nil, List.map_cons, List.map_nil,
      List.prod_cons, List.prod_nil, mul_one]; norm_num

/-- **Mayer Subgraph Expansion of `worldlineMayerPolymerClusterWeight`**
(Part II, Section 3.5 (`subsec:worldline-expansion`), Proposition 3.10 (`prop:tube-local-ursell-erasure`), Equation `eq:ursell-partition-sigma`):
While `worldlineClusterUrsellWeight` sums `(-1)^|G|` over connected spanning subgraphs
`G ⊆ E_compat(K)` of the polymer incompatibility graph, `worldlineMayerPolymerClusterWeight`
sums `(-1)^|G|` over all subgraphs `G ∈ E_compat(K).powerset`. -/
lemma worldlineMayerPolymerClusterWeight_eq_powerset_sum
    {L q_code r_0 m_max R_cut : ℕ} [NeZero L]
    (D_field : Box3D L → LocalCSSDescriptor q_code r_0 m_max)
    (sys : SysCSS[L, q_code, m_max]) (C_RCA : ℝ) (β : ℝ)
    (V : QuasiLocalPerturbation 3 L (SiteCSS[L, q_code]))
    (d_loc : ℕ → Finset (Box3D L) → (IdxCSS[L, q_code, m_max] → Bool) → ℝ)
    (ν : PauliBitstringPair L q_code)
    (σ : IdxCSS[L, q_code, m_max] → Bool)
    (K : WorldlineUrsellCluster L q_code) :
    let E_compat : Finset (Fin K.length × Fin K.length) :=
      Finset.univ.filter (fun e => e.1 < e.2 ∧ PolymerClusterOverlap sys C_RCA K e.1 e.2)
    worldlineMayerPolymerClusterWeight D_field sys C_RCA R_cut β V d_loc ν σ K =
      if ∀ γ ∈ K, IsValidWorldlinePolymer D_field sys C_RCA R_cut γ then
        ((Nat.factorial K.length : ℝ)⁻¹) *
          (∑ G ∈ E_compat.powerset, ((-1 : ℝ) ^ G.card)) *
          (K.map (fun γ => worldlinePolymerWeight D_field sys C_RCA β V d_loc ν γ σ)).prod
      else 0 := by
  intro E_compat
  have h_pw_iff :
      K.Pairwise (fun γ₁ γ₂ => ¬ArePolymersIncompatible sys C_RCA γ₁ γ₂) ↔ E_compat = ∅ := by
    rw [List.pairwise_iff_get, Finset.eq_empty_iff_forall_notMem]
    exact ⟨fun h_pw e he => h_pw e.1 e.2 (Finset.mem_filter.mp he).2.1 (Finset.mem_filter.mp he).2.2.2,
      fun h_emp i j h_lt h_inc => h_emp (i, j) (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h_lt, ne_of_lt h_lt, h_inc⟩)⟩
  unfold worldlineMayerPolymerClusterWeight
  rw [sum_powerset_neg_one_pow_card E_compat]
  by_cases h_val : ∀ γ ∈ K, IsValidWorldlinePolymer D_field sys C_RCA R_cut γ
  · by_cases h_pw : K.Pairwise (fun γ₁ γ₂ => ¬ArePolymersIncompatible sys C_RCA γ₁ γ₂)
    · rw [if_pos ⟨h_val, h_pw⟩, if_pos h_val, if_pos (h_pw_iff.mp h_pw), mul_one]
    · have h_not_emp : E_compat ≠ ∅ := fun h => h_pw (h_pw_iff.mpr h)
      rw [if_neg (fun h => h_pw h.2), if_pos h_val, if_neg h_not_emp, mul_zero, zero_mul]
  · rw [if_neg (fun h => h_val h.1), if_neg h_val]

/-- **Disconnected Subgraph Decomposition of `worldlineMayerPolymerClusterWeight - worldlineClusterUrsellWeight`**
(Part II, Section 3.5 (`subsec:worldline-expansion`), Proposition 3.10 (`prop:tube-local-ursell-erasure`), Equation `eq:ursell-partition-sigma`):
For any non-empty polymer tuple `K ≠ []`, subtracting the connected Ursell cluster weight
`if IsValidWorldlineUrsellCluster ... K then worldlineClusterUrsellWeight ... K σ else 0` from the
Mayer polymer-gas cluster weight `worldlineMayerPolymerClusterWeight ... K` isolates the sum of
`(-1)^|G|` over all **disconnected** subgraphs `G ∈ E_compat(K).powerset`. -/
lemma worldlineMayerPolymerClusterWeight_sub_ursell_eq_disconnected_sum
    {L q_code r_0 m_max R_cut : ℕ} [NeZero L]
    (D_field : Box3D L → LocalCSSDescriptor q_code r_0 m_max)
    (sys : SysCSS[L, q_code, m_max]) (C_RCA : ℝ) (β : ℝ)
    (V : QuasiLocalPerturbation 3 L (SiteCSS[L, q_code]))
    (d_loc : ℕ → Finset (Box3D L) → (IdxCSS[L, q_code, m_max] → Bool) → ℝ)
    (ν : PauliBitstringPair L q_code)
    (σ : IdxCSS[L, q_code, m_max] → Bool)
    {K : WorldlineUrsellCluster L q_code}
    (hK_ne : K ≠ []) :
    let E_compat : Finset (Fin K.length × Fin K.length) :=
      Finset.univ.filter (fun e => e.1 < e.2 ∧ PolymerClusterOverlap sys C_RCA K e.1 e.2)
    worldlineMayerPolymerClusterWeight D_field sys C_RCA R_cut β V d_loc ν σ K -
      (if IsValidWorldlineUrsellCluster D_field sys C_RCA R_cut K then
        worldlineClusterUrsellWeight D_field sys C_RCA β V d_loc ν K σ
      else 0) =
      if ∀ γ ∈ K, IsValidWorldlinePolymer D_field sys C_RCA R_cut γ then
        ((Nat.factorial K.length : ℝ)⁻¹) *
          (∑ G ∈ E_compat.powerset.filter (fun G =>
            ¬KPIsConnectedSubgraph (fun a b => (a, b) ∈ G ∨ (b, a) ∈ G) Finset.univ),
            ((-1 : ℝ) ^ G.card)) *
          (K.map (fun γ => worldlinePolymerWeight D_field sys C_RCA β V d_loc ν γ σ)).prod
      else 0 := by
  intro E_compat
  rw [worldlineMayerPolymerClusterWeight_eq_powerset_sum D_field sys C_RCA β V d_loc ν σ K,
    (ursellConnectedGraphCoeff_eq_zero_of_not_connected_and_valid_ite_eq
      D_field sys C_RCA β V d_loc ν σ K).2]
  by_cases h_val : ∀ γ ∈ K, IsValidWorldlinePolymer D_field sys C_RCA R_cut γ
  · rw [if_pos h_val, if_pos ⟨hK_ne, h_val⟩, if_pos h_val]
    unfold worldlineClusterUrsellWeight ursellConnectedGraphCoeff
    (try dsimp only)
    have h_split := (Finset.sum_filter_add_sum_filter_not E_compat.powerset
      (fun G => KPIsConnectedSubgraph (fun a b => (a, b) ∈ G ∨ (b, a) ∈ G) Finset.univ)
      (fun G => ((-1 : ℝ) ^ G.card))).symm
    change ((Nat.factorial K.length : ℝ)⁻¹) *
        (∑ G ∈ E_compat.powerset, (-1 : ℝ) ^ G.card) *
        (K.map (fun γ => worldlinePolymerWeight D_field sys C_RCA β V d_loc ν γ σ)).prod -
      ((Nat.factorial K.length : ℝ)⁻¹) *
        (∑ G ∈ E_compat.powerset.filter (fun G =>
          KPIsConnectedSubgraph (fun a b => (a, b) ∈ G ∨ (b, a) ∈ G) Finset.univ),
          (-1 : ℝ) ^ G.card) *
        (K.map (fun γ => worldlinePolymerWeight D_field sys C_RCA β V d_loc ν γ σ)).prod = _
    rw [h_split]
    ring
  · rw [if_neg h_val, if_neg (fun h => h_val h.2), if_neg h_val, sub_zero]

/-- Multi-polymer untwisted weight factorization along any list `K` of valid worldline polymers on a
realizable syndrome `σ ∈ realizableSyndromes D_field` (Part II, Section 3.5 (`subsec:worldline-expansion`), Lemma 3.9 (`lem:worldline-factorization-time-reversal`), Equation `eq:P-gamma-spanning-surface`). -/
lemma list_prod_spanningSurfaceSign_mul_worldlinePolymerMicroWeight_eq_of_valid
    {L q_code r_0 m_max w_0 L_star R_cut : ℕ} [NeZero L]
    {C_RCA J β : ℝ}
    (D_field : Box3D L → LocalCSSDescriptor q_code r_0 m_max)
    (h_valid : ValidDescriptorField D_field)
    (sys : SysCSS[L, q_code, m_max])
    (h_sys_checks : ∀ idx, sys.checkProj idx = staticCSSCheckProj D_field idx ∧
      sys.support idx = staticCSSCheckSupport D_field idx ∧ sys.weight idx = 1)
    (h_geom : sys.IsGeometricallyLocal r_0 w_0)
    (h_tqo1 : SatisfiesTQO1 sys L_star)
    (h_tqo2 : SatisfiesSectorFilteredLinearTQO2 sys 1 L_star C_RCA)
    (hR_le : R_cut ≤ L_star)
    (hr0_le : 1 + 4 * (r_0 : ℝ) ≤ C_RCA)
    (V : QuasiLocalPerturbation 3 L (SiteCSS[L, q_code]))
    (e_loc : ℕ → Finset (Box3D L) → ℝ)
    (d_loc : ℕ → Finset (Box3D L) → (IdxCSS[L, q_code, m_max] → Bool) → ℝ)
    (h_scalar : IsLocalCollarScalarFamily D_field sys R_cut C_RCA J V e_loc d_loc)
    (K : WorldlineUrsellCluster L q_code)
    (hK_valid : ∀ γ ∈ K, IsValidWorldlinePolymer D_field sys C_RCA R_cut γ)
    {σ : IdxCSS[L, q_code, m_max] → Bool}
    (hσ : σ ∈ realizableSyndromes D_field) :
    (K.map (fun γ =>
      spanningSurfaceSign (worldlinePolymerSpanningSurface D_field sys C_RCA γ) σ *
        worldlinePolymerMicroWeight D_field sys C_RCA β V d_loc γ
          (restrictSyndromeToCollar (worldlinePolymerNativeCollar sys C_RCA γ) σ))).prod =
    (K.map (fun γ =>
      ((-1 : ℝ) ^ γ.1.length) *
        (hilbertTrace (sys.syndromeProjector σ *
          ((hermitianPauliZX (worldlinePolymerLogicalCoset D_field sys C_RCA γ).1
            (worldlinePolymerLogicalCoset D_field sys C_RCA γ).2)† *
            worldlinePolymerWeightedLoopOp D_field sys V γ)) /
          hilbertTrace (sys.syndromeProjector σ)) *
        ∫ τ : Fin γ.1.length → ℝ,
          if InOrderedDysonSimplex β τ then
            Real.exp (-worldlineBareAction D_field sys γ.1 σ β τ) *
              ∏ ϑ ∈ γ.2, worldlineMayerBondFactor D_field γ.1 d_loc σ β ϑ τ
          else 0)).prod := by
  congr 1
  exact List.map_congr_left fun γ hγ =>
    spanningSurfaceSign_mul_worldlinePolymerMicroWeight_eq_of_valid
      D_field h_valid sys h_sys_checks h_geom h_tqo1 h_tqo2 hR_le hr0_le
      V e_loc d_loc h_scalar (hK_valid γ hγ) hσ

/-- For any Pauli bitstring pair `(a, b)` that commutes with all syndrome-closed Pauli operators
`ν ∈ syndromeClosedPauliFinset D_field` (`∀ ν ∈ syndromeClosedPauliFinset D_field, symplecticPauliSign ν (a, b) = 1`),
linear-functional duality on `𝔽₂` (`exists_subset_sum_zmod2_of_ker_subset` on `Finset.univ`) produces
a check subset `α : Finset (IdxCSS[L, q_code, m_max])` such that for every Pauli pair `(u, v)` and
every complex scalar `z : ℂ`:
1. `symplecticPauliSign (u, v) (a, b) = spanningSurfaceSign α (staticCSSPauliFlip D_field u v)`, and
2. for every realizable syndrome `σ ∈ realizableSyndromes D_field`,
   `hilbertTrace (sys.syndromeProjector σ * (z • (weylPauliZ a * weylPauliX b))) = spanningSurfaceSign α σ * hilbertTrace (sys.P0 * (z • (weylPauliZ a * weylPauliX b)))`
(Part II, Section 3.5 (`subsec:worldline-expansion`), Lemma 3.9 (`lem:worldline-factorization-time-reversal`), Equation `eq:P-gamma-spanning-surface`). -/
lemma exists_global_spanning_surface_of_commute_syndromeClosed
    {L q_code r_0 m_max : ℕ} [NeZero L]
    (D_field : Box3D L → LocalCSSDescriptor q_code r_0 m_max)
    (sys : SysCSS[L, q_code, m_max])
    (h_sys_checks : ∀ idx, sys.checkProj idx = staticCSSCheckProj D_field idx ∧
      sys.support idx = staticCSSCheckSupport D_field idx ∧ sys.weight idx = 1)
    {a b : BoxSlot3D L q_code → ZMod 2}
    (h_comm : ∀ ν ∈ syndromeClosedPauliFinset D_field, symplecticPauliSign ν (a, b) = 1) :
    ∃ α : Finset (IdxCSS[L, q_code, m_max]),
      (∀ p : PauliBitstringPair L q_code,
        (∑ slot, (p.1 slot * b slot + a slot * p.2 slot)) =
          ∑ c ∈ α, boolToZMod2 (staticCSSPauliFlip D_field p.1 p.2 c)) ∧
      (∀ u v : BoxSlot3D L q_code → ZMod 2,
        symplecticPauliSign (u, v) (a, b) =
          spanningSurfaceSign α (staticCSSPauliFlip D_field u v)) ∧
      (∀ σ ∈ realizableSyndromes D_field, ∀ z : ℂ,
        hilbertTrace (sys.syndromeProjector σ * (z • (weylPauliZ a * weylPauliX b))) =
          spanningSurfaceSign α σ *
            hilbertTrace (sys.P0 * (z • (weylPauliZ a * weylPauliX b)))) := by
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
    exact Finset.sum_congr rfl fun slot _ => by
      ring
  have h_ker : ∀ p : PauliBitstringPair L q_code,
      (∀ c ∈ (Finset.univ : Finset (IdxCSS[L, q_code, m_max])), f_chk c p = 0) →
      φ_pair p = 0 := fun p hp_ker => by
    have hp_closed : p ∈ syndromeClosedPauliFinset D_field := by
      rw [syndromeClosedPauliFinset, Finset.mem_filter]; refine ⟨Finset.mem_univ _, ?_⟩; ext c
      have h0 := hp_ker c (Finset.mem_univ c); dsimp [f_chk, boolToZMod2] at h0
      cases h_flip : staticCSSPauliFlip D_field p.1 p.2 c
      · rfl
      · rw [h_flip] at h0; revert h0; decide
    have h_sc := (signScalar_symplectic_eq_symplecticPauliSign_and_mul p p p (a, b) (a, b) (a, b)).1
    have h_phi_eq : (∑ q : BoxSlot3D L q_code, (p.1 q * b q + p.2 q * a q)) = φ_pair p :=
      Finset.sum_congr rfl fun q _ => by ring
    rw [h_phi_eq, h_comm p hp_closed] at h_sc
    rcases _root_.zmod2_eq_zero_or_one (φ_pair p) with h0 | h1
    · exact h0
    · rw [h1] at h_sc; change (-1 : ℂ) = (1 : ℂ) at h_sc; norm_num at h_sc
  have h_duality : ∃ α ⊆ (Finset.univ : Finset (IdxCSS[L, q_code, m_max])),
      ∀ p : PauliBitstringPair L q_code, φ_pair p = ∑ c ∈ α, f_chk c p := by
    suffices ∀ (C_col : Finset (IdxCSS[L, q_code, m_max]))
        (φ : PauliBitstringPair L q_code → ZMod 2),
        (∀ v w, φ (v + w) = φ v + φ w) →
        (∀ v, (∀ c ∈ C_col, f_chk c v = 0) → φ v = 0) →
        ∃ α ⊆ C_col, ∀ v, φ v = ∑ c ∈ α, f_chk c v from
      this Finset.univ φ_pair hφ_add h_ker
    intro C_col
    induction C_col using Finset.induction_on with
    | empty =>
      intro φ _ h_k; refine ⟨∅, Finset.Subset.refl ∅, fun v => ?_⟩
      rw [Finset.sum_empty]; exact h_k v (fun c hc => False.elim (Finset.notMem_empty c hc))
    | @insert c₀ s hc₀ ih =>
      intro φ hφ_a h_k
      by_cases h_s : ∀ v, (∀ c ∈ s, f_chk c v = 0) → φ v = 0
      · rcases ih φ hφ_a h_s with ⟨α, hα_sub, hα_eq⟩
        exact ⟨α, Finset.Subset.trans hα_sub (Finset.subset_insert c₀ s), hα_eq⟩
      · push_neg at h_s; rcases h_s with ⟨v₀, hv₀_s, hv₀_φ⟩
        have hφ_v₀ : φ v₀ = 1 := (_root_.zmod2_eq_zero_or_one (φ v₀)).resolve_left hv₀_φ
        have hfc₀_v₀ : f_chk c₀ v₀ = 1 :=
          (_root_.zmod2_eq_zero_or_one (f_chk c₀ v₀)).resolve_left fun h0 => hv₀_φ (h_k v₀ fun c hc => by
            rcases Finset.mem_insert.mp hc with rfl | hcs <;> [exact h0; exact hv₀_s c hcs])
        let φ' : PauliBitstringPair L q_code → ZMod 2 := fun v => φ v + f_chk c₀ v
        have hφ'_a : ∀ v w, φ' (v + w) = φ' v + φ' w := fun v w => by
          dsimp [φ']; rw [hφ_a, hf_add]; ring
        have hφ'_k : ∀ v, (∀ c ∈ s, f_chk c v = 0) → φ' v = 0 := fun v hv_s => by
          dsimp [φ']
          rcases _root_.zmod2_eq_zero_or_one (f_chk c₀ v) with h0 | h1
          · rw [h_k v (fun c hc => by
              rcases Finset.mem_insert.mp hc with rfl | hcs <;> [exact h0; exact hv_s c hcs]), h0, add_zero]
          · have h_sum_zero := h_k (v + v₀) fun c hc => by
              rw [hf_add]; rcases Finset.mem_insert.mp hc with rfl | hcs
              · rw [h1, hfc₀_v₀]; decide
              · rw [hv_s c hcs, hv₀_s c hcs, add_zero]
            rw [hφ_a, hφ_v₀] at h_sum_zero; rw [h1, h_sum_zero]
        rcases ih φ' hφ'_a hφ'_k with ⟨α, hα_sub, hα_eq⟩
        refine ⟨insert c₀ α, Finset.insert_subset_insert c₀ hα_sub, fun v => ?_⟩
        rw [Finset.sum_insert (fun h_in => hc₀ (hα_sub h_in)), ← hα_eq v]; dsimp [φ']
        exact ((by decide : ∀ x y : ZMod 2, y + (x + y) = x) (φ v) (f_chk c₀ v)).symm
  rcases h_duality with ⟨α, _, hα_eq⟩
  have h_sign_eq : ∀ u v : BoxSlot3D L q_code → ZMod 2,
      symplecticPauliSign (u, v) (a, b) =
        spanningSurfaceSign α (staticCSSPauliFlip D_field u v) := fun u v => by
    have h_sc := (signScalar_symplectic_eq_symplecticPauliSign_and_mul
      (u, v) (u, v) (u, v) (a, b) (a, b) (a, b)).1
    have h_phi_eq : (∑ q : BoxSlot3D L q_code, (u q * b q + v q * a q)) = φ_pair (u, v) :=
      Finset.sum_congr rfl fun q _ => by ring
    rw [h_phi_eq, hα_eq (u, v)] at h_sc
    have h_span_sc : ∀ s : Finset (IdxCSS[L, q_code, m_max]),
        signScalar (∑ c ∈ s, f_chk c (u, v)) =
          ((spanningSurfaceSign s (staticCSSPauliFlip D_field u v) : ℝ) : ℂ) := by
      intro s; induction s using Finset.induction_on with
      | empty => simp [spanningSurfaceSign, signScalar_zero]
      | @insert c₀ s hc₀ ih =>
        rw [Finset.sum_insert hc₀, signScalar_add, ih]; unfold spanningSurfaceSign
        rw [Finset.filter_insert]; dsimp [f_chk]
        cases hσ : staticCSSPauliFlip D_field u v c₀
        · simp [boolToZMod2, signScalar_zero]
        · rw [if_pos rfl, Finset.card_insert_of_notMem (fun h => hc₀ (Finset.mem_filter.mp h).1)]
          change (-1 : ℂ) * ((if (s.filter (fun c => staticCSSPauliFlip D_field u v c = true)).card % 2 = 1
              then (-1 : ℝ) else 1 : ℝ) : ℂ) =
            ((if ((s.filter (fun c => staticCSSPauliFlip D_field u v c = true)).card + 1) % 2 = 1
              then (-1 : ℝ) else 1 : ℝ) : ℂ)
          by_cases h_mod : (s.filter (fun c => staticCSSPauliFlip D_field u v c = true)).card % 2 = 1
          · rw [if_pos h_mod, if_neg (by omega)]; norm_num
          · rw [if_neg h_mod, if_pos (by omega)]; norm_num
    rw [h_span_sc α] at h_sc; exact_mod_cast h_sc.symm
  refine ⟨α, hα_eq, h_sign_eq, fun σ hσ z => ?_⟩
  rcases (Finset.mem_filter.mp hσ).2 with ⟨u, v, rfl⟩
  rw [hilbertTrace_syndromeProjector_smul_weylPauliZX_eq D_field sys h_sys_checks u v a b z,
    h_sign_eq u v]

/-- For any singleton polymer cluster `[γ]`, the Mayer polymer cluster weight equals the Ursell
cluster weight (Part II, Section 3.5 (`subsec:worldline-expansion`), Proposition 3.10 (`prop:tube-local-ursell-erasure`), Equation `eq:ursell-partition-sigma`). -/
lemma worldlineMayerPolymerClusterWeight_sub_ursell_singleton
    {L q_code r_0 m_max R_cut : ℕ} [NeZero L]
    (D_field : Box3D L → LocalCSSDescriptor q_code r_0 m_max)
    (sys : SysCSS[L, q_code, m_max]) (C_RCA : ℝ) (β : ℝ)
    (V : QuasiLocalPerturbation 3 L (SiteCSS[L, q_code]))
    (d_loc : ℕ → Finset (Box3D L) → (IdxCSS[L, q_code, m_max] → Bool) → ℝ)
    (ν : PauliBitstringPair L q_code)
    (σ : IdxCSS[L, q_code, m_max] → Bool)
    (γ : WorldlineDysonPolymer L q_code) :
    worldlineMayerPolymerClusterWeight D_field sys C_RCA R_cut β V d_loc ν σ [γ] =
      if IsValidWorldlineUrsellCluster D_field sys C_RCA R_cut [γ] then
        worldlineClusterUrsellWeight D_field sys C_RCA β V d_loc ν [γ] σ
      else 0 := by
  have h_sub := worldlineMayerPolymerClusterWeight_sub_ursell_eq_disconnected_sum
    (R_cut := R_cut) D_field sys C_RCA β V d_loc ν σ (List.cons_ne_nil γ [])
  (try dsimp only at h_sub)
  let E_compat : Finset (Fin ([γ].length) × Fin ([γ].length)) :=
    Finset.univ.filter (fun e => e.1 < e.2 ∧ PolymerClusterOverlap sys C_RCA [γ] e.1 e.2)
  have h_conn_univ : ∀ G : Finset (Fin ([γ].length) × Fin ([γ].length)),
      KPIsConnectedSubgraph (fun a b => (a, b) ∈ G ∨ (b, a) ∈ G)
        (Finset.univ : Finset (Fin ([γ].length))) := by
    intro G
    refine ⟨⟨⟨0, Nat.zero_lt_one⟩, Finset.mem_univ _⟩, fun u _ v _ => ?_⟩
    have hu : u.1 < 1 := u.isLt
    have hv : v.1 < 1 := v.isLt
    have huv : u = v := Fin.ext (by omega)
    rw [huv]
  have h_filt_emp :
      E_compat.powerset.filter
        (fun G => ¬KPIsConnectedSubgraph (fun a b => (a, b) ∈ G ∨ (b, a) ∈ G) Finset.univ) = ∅ := by
    rw [Finset.filter_eq_empty_iff]
    intro G _ h_not
    exact h_not (h_conn_univ G)
  change worldlineMayerPolymerClusterWeight D_field sys C_RCA R_cut β V d_loc ν σ [γ] -
      (if IsValidWorldlineUrsellCluster D_field sys C_RCA R_cut [γ] then
        worldlineClusterUrsellWeight D_field sys C_RCA β V d_loc ν [γ] σ
      else 0) =
    if ∀ γ' ∈ ([γ] : WorldlineUrsellCluster L q_code),
        IsValidWorldlinePolymer D_field sys C_RCA R_cut γ' then
      ((Nat.factorial ([γ].length) : ℝ)⁻¹) *
        (∑ G ∈ E_compat.powerset.filter
          (fun G => ¬KPIsConnectedSubgraph (fun a b => (a, b) ∈ G ∨ (b, a) ∈ G) Finset.univ),
          ((-1 : ℝ) ^ G.card)) *
        (([γ].map (fun γ' => worldlinePolymerWeight D_field sys C_RCA β V d_loc ν γ' σ)).prod)
    else 0 at h_sub
  rw [h_filt_emp, Finset.sum_empty, mul_zero, zero_mul, ite_self] at h_sub
  exact sub_eq_zero.mp h_sub

/-- For every valid worldline polymer `γ` (`isValidWorldlinePolymer D_field sys C_RCA R_cut γ`),
its net loop Pauli bitstring pair `(worldlinePolymerLoopX γ, worldlinePolymerLoopZ γ)` is
syndrome-closed (`∈ syndromeClosedPauliFinset D_field`), and therefore for every tuple `K` of
valid worldline polymers, the net loop sum `(K.map (fun γ => (worldlinePolymerLoopX γ, worldlinePolymerLoopZ γ))).sum`
also belongs to `syndromeClosedPauliFinset D_field` (Part II, Section 3.2 (`subsec:rca1-pinching`), Proposition 3.4 (`prop:pauli-diag-off`)). -/
lemma worldlinePolymerLoop_and_sum_mem_syndromeClosedPauliFinset_of_valid
    {L q_code r_0 m_max R_cut : ℕ} [NeZero L]
    {C_RCA : ℝ}
    (D_field : Box3D L → LocalCSSDescriptor q_code r_0 m_max)
    (sys : SysCSS[L, q_code, m_max])
    (γ : WorldlineDysonPolymer L q_code)
    (hγ : IsValidWorldlinePolymer D_field sys C_RCA R_cut γ)
    (K : WorldlineUrsellCluster L q_code)
    (hK : ∀ γ' ∈ K, IsValidWorldlinePolymer D_field sys C_RCA R_cut γ') :
    (worldlinePolymerLoopX γ, worldlinePolymerLoopZ γ) ∈ syndromeClosedPauliFinset D_field ∧
    (K.map (fun γ' => (worldlinePolymerLoopX γ', worldlinePolymerLoopZ γ'))).sum ∈
      syndromeClosedPauliFinset D_field := by
  have h_single : ∀ γ' : WorldlineDysonPolymer L q_code,
      IsValidWorldlinePolymer D_field sys C_RCA R_cut γ' →
      (worldlinePolymerLoopX γ', worldlinePolymerLoopZ γ') ∈ syndromeClosedPauliFinset D_field := by
    intro γ' hγ'
    rw [syndromeClosedPauliFinset, Finset.mem_filter]
    exact ⟨Finset.mem_univ _, hγ'.2.2.1.2⟩
  refine ⟨h_single γ hγ, ?_⟩
  induction K with
  | nil =>
    rw [List.map_nil, List.sum_nil]
    exact (zero_mem_syndromeClosedPauliFinset_and_sum_inv D_field 0).1
  | cons hd tl ih =>
    rw [List.map_cons, List.sum_cons]
    have h_hd := h_single hd (hK hd List.mem_cons_self)
    have h_tl := ih (fun γ' hγ' => hK γ' (List.mem_cons_of_mem hd hγ'))
    rw [syndromeClosedPauliFinset, Finset.mem_filter] at h_hd h_tl ⊢
    refine ⟨Finset.mem_univ _, ?_⟩
    let p₁ := (worldlinePolymerLoopX hd, worldlinePolymerLoopZ hd)
    let p₂ := (tl.map (fun γ' => (worldlinePolymerLoopX γ', worldlinePolymerLoopZ γ'))).sum
    change staticCSSPauliFlip D_field (p₁.1 + p₂.1) (p₁.2 + p₂.2) = fun _ => false
    rw [staticCSSPauliFlip_add D_field p₁.1 p₂.1 p₁.2 p₂.2, h_hd.2, h_tl.2]
    ext c
    rfl

/-- For any two collar-compatible valid worldline polymers `γ₁, γ₂` (`¬arePolymersIncompatible sys C_RCA γ₁ γ₂`)
with `1 ≤ C_RCA`, their net loop bitstrings have disjoint slot supports, so
`worldlinePolymerLoopX γ₁ slot * worldlinePolymerLoopZ γ₂ slot = 0` for every `slot`
(Part II, Section 3.5 (`subsec:worldline-expansion`), Lemma 3.9 (`lem:worldline-factorization-time-reversal`)). -/
lemma worldlinePolymerLoop_slot_disjoint_of_compatible
    {L q_code r_0 m_max R_cut : ℕ} [NeZero L]
    (D_field : Box3D L → LocalCSSDescriptor q_code r_0 m_max)
    (sys : SysCSS[L, q_code, m_max])
    (h_sys_supp : ∀ idx, sys.support idx = staticCSSCheckSupport D_field idx)
    {C_RCA : ℝ} (hC_RCA : 1 ≤ C_RCA)
    {γ₁ γ₂ : WorldlineDysonPolymer L q_code}
    (hγ₁ : IsValidWorldlinePolymer D_field sys C_RCA R_cut γ₁)
    (hγ₂ : IsValidWorldlinePolymer D_field sys C_RCA R_cut γ₂)
    (h_compat : ¬ArePolymersIncompatible sys C_RCA γ₁ γ₂)
    (slot : BoxSlot3D L q_code) :
    (worldlinePolymerLoopX γ₁ slot ≠ 0 ∨ worldlinePolymerLoopZ γ₁ slot ≠ 0 →
      worldlinePolymerLoopX γ₂ slot = 0 ∧ worldlinePolymerLoopZ γ₂ slot = 0) ∧
    worldlinePolymerLoopX γ₁ slot * worldlinePolymerLoopZ γ₂ slot = 0 := by
  have h_col_disj : Disjoint (worldlinePolymerNativeCollar sys C_RCA γ₁)
      (worldlinePolymerNativeCollar sys C_RCA γ₂) := not_not.mp h_compat
  have h_mem_jump : ∀ {γ : WorldlineDysonPolymer L q_code},
      IsValidWorldlinePolymer D_field sys C_RCA R_cut γ →
      worldlinePolymerLoopX γ slot ≠ 0 ∨ worldlinePolymerLoopZ γ slot ≠ 0 →
      ∃ ξ ∈ γ.1, slot.1 ∈ ξ.1.2 := by
    intro γ hγ h_ne
    have h_list : ∀ l : List (WorldlineJumpMonomer L q_code),
        (l.map (fun ξ => ξ.2.1)).sum slot ≠ 0 ∨ (l.map (fun ξ => ξ.2.2)).sum slot ≠ 0 →
        ∃ ξ ∈ l, ξ.2.1 slot ≠ 0 ∨ ξ.2.2 slot ≠ 0 := by
      intro l
      induction l with
      | nil =>
        intro h; rcases h with h | h <;> exact False.elim (h rfl)
      | cons hd tl ih =>
        intro h_sum
        by_cases h_hd : hd.2.1 slot ≠ 0 ∨ hd.2.2 slot ≠ 0
        · exact ⟨hd, List.mem_cons_self, h_hd⟩
        · push_neg at h_hd
          have h_tl : (tl.map (fun ξ => ξ.2.1)).sum slot ≠ 0 ∨
              (tl.map (fun ξ => ξ.2.2)).sum slot ≠ 0 := by
            rcases h_sum with h1 | h2
            · left; intro h0; apply h1
              change hd.2.1 slot + (tl.map (fun ξ => ξ.2.1)).sum slot = 0
              rw [h_hd.1, h0, add_zero]
            · right; intro h0; apply h2
              change hd.2.2 slot + (tl.map (fun ξ => ξ.2.2)).sum slot = 0
              rw [h_hd.2, h0, add_zero]
          rcases ih h_tl with ⟨ξ, hξ, hξ_ne⟩
          exact ⟨ξ, List.mem_cons_of_mem hd hξ, hξ_ne⟩
    rcases h_list γ.1 h_ne with ⟨ξ, hξ, hξ_ne⟩
    exact ⟨ξ, hξ, (hγ.2.1 ξ hξ).1 slot hξ_ne⟩
  have h_disj : worldlinePolymerLoopX γ₁ slot ≠ 0 ∨ worldlinePolymerLoopZ γ₁ slot ≠ 0 →
      worldlinePolymerLoopX γ₂ slot = 0 ∧ worldlinePolymerLoopZ γ₂ slot = 0 := by
    intro h₁
    by_contra! h₂
    have h₂_or : worldlinePolymerLoopX γ₂ slot ≠ 0 ∨ worldlinePolymerLoopZ γ₂ slot ≠ 0 := by
      by_cases hx : worldlinePolymerLoopX γ₂ slot = 0
      · exact Or.inr (h₂ hx)
      · exact Or.inl hx
    rcases h_mem_jump hγ₁ h₁ with ⟨ξ₁, hξ₁, h_in₁⟩
    rcases h_mem_jump hγ₂ h₂_or with ⟨ξ₂, hξ₂, h_in₂⟩
    have hp₁ : ξ₁.1 ∈ worldlinePolymerMonomers γ₁ :=
      Finset.mem_union_left _ (List.mem_toFinset.mpr (List.mem_map_of_mem hξ₁))
    have hp₂ : ξ₂.1 ∈ worldlinePolymerMonomers γ₂ :=
      Finset.mem_union_left _ (List.mem_toFinset.mpr (List.mem_map_of_mem hξ₂))
    have h_disj_col : Disjoint (rcaCollarChecks sys C_RCA ξ₁.1.1 ξ₁.1.2)
        (rcaCollarChecks sys C_RCA ξ₂.1.1 ξ₂.1.2) :=
      Finset.disjoint_left.mpr fun c hc₁ hc₂ =>
        Finset.disjoint_left.mp h_col_disj
          (Finset.mem_biUnion.mpr ⟨ξ₁.1, hp₁, hc₁⟩)
          (Finset.mem_biUnion.mpr ⟨ξ₂.1, hp₂, hc₂⟩)
    rcases mem_scaleCubeFinset_iff.mp (hγ₁.1 ξ₁.1 hp₁) with ⟨_, hA₁⟩
    rcases mem_scaleCubeFinset_iff.mp (hγ₂.1 ξ₂.1 hp₂) with ⟨_, hA₂⟩
    exact slot_disjoint_of_disjoint_rcaCollarChecks
      D_field sys h_sys_supp hC_RCA hA₁ hA₂ h_disj_col slot h_in₁ h_in₂
  refine ⟨h_disj, ?_⟩
  by_cases hx : worldlinePolymerLoopX γ₁ slot = 0
  · rw [hx, zero_mul]
  · rw [(h_disj (Or.inl hx)).2, mul_zero]

/-- Any Pauli bitstring pair `(a, b)` that commutes with all syndrome-closed Pauli operators
`ν ∈ syndromeClosedPauliFinset D_field` is a sum of CSS check generators and therefore acts
as the identity $+1$ on the vacuum code projector `sys.P0`:
`(weylPauliZ a * weylPauliX b) * sys.P0 = sys.P0` and
`hilbertTrace (sys.P0 * (z • (weylPauliZ a * weylPauliX b))) = z.re * hilbertTrace sys.P0`
(Part II, Section 3.2 (`subsec:rca1-pinching`), Proposition 3.4 (`prop:pauli-diag-off`) and Section 3.5 (`subsec:worldline-expansion`), Lemma 3.9 (`lem:worldline-factorization-time-reversal`)). -/
lemma weylPauliZX_mul_P0_and_trace_eq_of_commute_syndromeClosed
    {L q_code r_0 m_max : ℕ} [NeZero L]
    (D_field : Box3D L → LocalCSSDescriptor q_code r_0 m_max)
    (sys : SysCSS[L, q_code, m_max])
    (h_sys_checks : ∀ idx, sys.checkProj idx = staticCSSCheckProj D_field idx ∧
      sys.support idx = staticCSSCheckSupport D_field idx ∧ sys.weight idx = 1)
    {a b : BoxSlot3D L q_code → ZMod 2}
    (h_comm : ∀ ν ∈ syndromeClosedPauliFinset D_field, symplecticPauliSign ν (a, b) = 1) :
    weylPauliZ a * sys.P0 = sys.P0 ∧
    weylPauliX b * sys.P0 = sys.P0 ∧
    (weylPauliZ a * weylPauliX b) * sys.P0 = sys.P0 ∧
    ∀ z : ℂ,
      hilbertTrace (sys.P0 * (z • (weylPauliZ a * weylPauliX b))) =
        z.re * hilbertTrace sys.P0 := by
  rcases exists_global_spanning_surface_of_commute_syndromeClosed
      D_field sys h_sys_checks h_comm with ⟨α, hα_eq, _, _⟩
  have ha_eq : a = ∑ c ∈ α, staticCSSCheckPauliZ D_field c := by
    ext q
    let δq : BoxSlot3D L q_code → ZMod 2 := fun slot => if slot = q then 1 else 0
    have hq := hα_eq (0, δq)
    have h_lhs : (∑ slot : BoxSlot3D L q_code, ((0 : BoxSlot3D L q_code → ZMod 2) slot * b slot +
        a slot * δq slot)) = a q := by
      rw [Finset.sum_eq_single q]; · simp [δq]
      · intro slot _ hne; simp [δq, hne]
      · intro h_abs; exact False.elim (h_abs (Finset.mem_univ q))
    have h_rhs : (∑ c ∈ α, boolToZMod2 (staticCSSPauliFlip D_field 0 δq c)) =
        (∑ c ∈ α, staticCSSCheckPauliZ D_field c) q := by
      rw [Finset.sum_apply]; refine Finset.sum_congr rfl fun c _ => ?_
      rw [boolToZMod2_staticCSSPauliFlip_eq_sum_checkPauli D_field (0, δq) c]; (try dsimp only)
      rw [Finset.sum_eq_single q]; · simp [δq]
      · intro slot _ hne; simp [δq, hne]
      · intro h_abs; exact False.elim (h_abs (Finset.mem_univ q))
    rw [← h_lhs, hq, h_rhs]
  have hb_eq : b = ∑ c ∈ α, staticCSSCheckPauliX D_field c := by
    ext q
    let δq : BoxSlot3D L q_code → ZMod 2 := fun slot => if slot = q then 1 else 0
    have hq := hα_eq (δq, 0)
    have h_lhs : (∑ slot : BoxSlot3D L q_code, (δq slot * b slot +
        a slot * (0 : BoxSlot3D L q_code → ZMod 2) slot)) = b q := by
      rw [Finset.sum_eq_single q]; · simp [δq]
      · intro slot _ hne; simp [δq, hne]
      · intro h_abs; exact False.elim (h_abs (Finset.mem_univ q))
    have h_rhs : (∑ c ∈ α, boolToZMod2 (staticCSSPauliFlip D_field δq 0 c)) =
        (∑ c ∈ α, staticCSSCheckPauliX D_field c) q := by
      rw [Finset.sum_apply]; refine Finset.sum_congr rfl fun c _ => ?_
      rw [boolToZMod2_staticCSSPauliFlip_eq_sum_checkPauli D_field (δq, 0) c]; (try dsimp only)
      rw [Finset.sum_eq_single q]; · simp [δq]
      · intro slot _ hne; simp [δq, hne]
      · intro h_abs; exact False.elim (h_abs (Finset.mem_univ q))
    rw [← h_lhs, hq, h_rhs]
  have hZ_P0 : ∀ s : Finset (IdxCSS[L, q_code, m_max]),
      weylPauliZ (∑ c ∈ s, staticCSSCheckPauliZ D_field c) * sys.P0 = sys.P0 := fun s => by
    induction s using Finset.induction_on with
    | empty => rw [Finset.sum_empty, weylPauliZ_zero, one_mul]
    | @insert c₀ s hc₀ ih =>
      rw [Finset.sum_insert hc₀, weylPauliZ_add, mul_assoc, ih,
        (weylPauli_staticCSSCheckPauli_mul_P0 D_field sys h_sys_checks c₀).1]
  have hX_P0 : ∀ s : Finset (IdxCSS[L, q_code, m_max]),
      weylPauliX (∑ c ∈ s, staticCSSCheckPauliX D_field c) * sys.P0 = sys.P0 := fun s => by
    induction s using Finset.induction_on with
    | empty => rw [Finset.sum_empty, weylPauliX_zero, one_mul]
    | @insert c₀ s hc₀ ih =>
      rw [Finset.sum_insert hc₀, weylPauliX_add, mul_assoc, ih,
        (weylPauli_staticCSSCheckPauli_mul_P0 D_field sys h_sys_checks c₀).2]
  have ha_P0 : weylPauliZ a * sys.P0 = sys.P0 := by rw [ha_eq]; exact hZ_P0 α
  have hb_P0 : weylPauliX b * sys.P0 = sys.P0 := by rw [hb_eq]; exact hX_P0 α
  have hab_P0 : (weylPauliZ a * weylPauliX b) * sys.P0 = sys.P0 := by
    rw [mul_assoc, hb_P0, ha_P0]
  refine ⟨ha_P0, hb_P0, hab_P0, fun z => ?_⟩
  have h_res := PerturbedThermalBarrier.syndrome_resolution_indexed sys
  rw [hilbertTrace_mul_comm_aux sys.P0 (z • (weylPauliZ a * weylPauliX b)),
    clm_smul_mul, hab_P0, ← h_res.1, hilbertTrace_complex_smul_syndromeProjector]

/-- Any stabilizer bitstring pair `(a, b)` (`∀ ν ∈ syndromeClosedPauliFinset D_field, symplecticPauliSign ν (a, b) = 1`)
acts on every realizable syndrome projector `sys.syndromeProjector (staticCSSPauliFlip D_field u v)` as multiplication
by `symplecticPauliSign (u, v) (a, b)`; in particular, for any valid polymer `γ`, the stabilizer bitstring
`μ(γ) + (a(γ), b(γ))` acts on `sys.syndromeProjector σ₀` as `spanningSurfaceSign α(γ) σ₀`
(Part II, Section 3.5 (`subsec:worldline-expansion`), Lemma 3.9 (`lem:worldline-factorization-time-reversal`), Equation `eq:P-gamma-spanning-surface`). -/
lemma weylPauliZX_mul_syndromeProjector_eq_of_commute_syndromeClosed
    {L q_code r_0 m_max R_cut : ℕ} [NeZero L]
    {C_RCA : ℝ}
    (D_field : Box3D L → LocalCSSDescriptor q_code r_0 m_max)
    (h_valid : ValidDescriptorField D_field)
    (sys : SysCSS[L, q_code, m_max])
    (h_sys_checks : ∀ idx, sys.checkProj idx = staticCSSCheckProj D_field idx ∧
      sys.support idx = staticCSSCheckSupport D_field idx ∧ sys.weight idx = 1) :
    (∀ {a b : BoxSlot3D L q_code → ZMod 2},
      (∀ ν ∈ syndromeClosedPauliFinset D_field, symplecticPauliSign ν (a, b) = 1) →
      ∀ u v : BoxSlot3D L q_code → ZMod 2,
        (weylPauliZ a * weylPauliX b) *
          sys.syndromeProjector (staticCSSPauliFlip D_field u v) =
        ((symplecticPauliSign (u, v) (a, b) : ℝ) : ℂ) •
          sys.syndromeProjector (staticCSSPauliFlip D_field u v)) ∧
    (∀ {γ : WorldlineDysonPolymer L q_code},
      IsValidWorldlinePolymer D_field sys C_RCA R_cut γ →
      ∀ {σ₀ : IdxCSS[L, q_code, m_max] → Bool}, σ₀ ∈ realizableSyndromes D_field →
        let μ := worldlinePolymerLogicalCoset D_field sys C_RCA γ
        (weylPauliZ (μ.1 + worldlinePolymerLoopX γ) *
          weylPauliX (μ.2 + worldlinePolymerLoopZ γ)) * sys.syndromeProjector σ₀ =
        ((spanningSurfaceSign (worldlinePolymerSpanningSurface D_field sys C_RCA γ) σ₀ : ℝ) : ℂ) •
          sys.syndromeProjector σ₀) := by
  have h_part1 : ∀ {a b : BoxSlot3D L q_code → ZMod 2},
      (∀ ν ∈ syndromeClosedPauliFinset D_field, symplecticPauliSign ν (a, b) = 1) →
      ∀ u v : BoxSlot3D L q_code → ZMod 2,
        (weylPauliZ a * weylPauliX b) *
          sys.syndromeProjector (staticCSSPauliFlip D_field u v) =
        ((symplecticPauliSign (u, v) (a, b) : ℝ) : ℂ) •
          sys.syndromeProjector (staticCSSPauliFlip D_field u v) := by
    intro a b h_comm u v
    have hab_P0 := (weylPauliZX_mul_P0_and_trace_eq_of_commute_syndromeClosed
      D_field sys h_sys_checks h_comm).2.2.1
    have h_res := PerturbedThermalBarrier.syndrome_resolution_indexed sys
    let U := weylPauliZ u * weylPauliX v
    let U_inv := weylPauliX v * weylPauliZ u
    have hU_right : U * U_inv = 1 := by
      calc (weylPauliZ u * weylPauliX v) * (weylPauliX v * weylPauliZ u)
        _ = weylPauliZ u * (weylPauliX v * weylPauliX v) * weylPauliZ u := by simp only [mul_assoc]
        _ = 1 := by rw [weylPauliX_sq_eq_one v, mul_one, weylPauliZ_sq_eq_one u]
    have hU_inter : U * sys.P0 = sys.syndromeProjector (staticCSSPauliFlip D_field u v) * U := by
      have h_flip : ∀ idx, U * sys.checkProj idx =
          (if staticCSSPauliFlip D_field u v idx then 1 - sys.checkProj idx else sys.checkProj idx) * U :=
        fun idx => by rw [(h_sys_checks idx).1]; exact weylPauliZX_mul_staticCSSCheckProj D_field u v idx
      have h_int := intertwine_syndromeProjector_of_checkFlip sys h_flip (fun _ => false)
      have h_xor : (fun i => xor false (staticCSSPauliFlip D_field u v i)) =
          staticCSSPauliFlip D_field u v := by ext i; simp
      rw [h_res.1, h_xor] at h_int; exact h_int
    have h_proj_eq : sys.syndromeProjector (staticCSSPauliFlip D_field u v) = U * sys.P0 * U_inv := by
      calc sys.syndromeProjector (staticCSSPauliFlip D_field u v)
        _ = (sys.syndromeProjector (staticCSSPauliFlip D_field u v) * U) * U_inv := by
            rw [mul_assoc, hU_right, mul_one]
        _ = U * sys.P0 * U_inv := by rw [← hU_inter]
    have h_comm_U : (weylPauliZ a * weylPauliX b) * U =
        ((symplecticPauliSign (u, v) (a, b) : ℝ) : ℂ) • (U * (weylPauliZ a * weylPauliX b)) := by
      dsimp [U]
      rw [weylPauliZX_comm_signScalar a b u v,
        ← (signScalar_symplectic_eq_symplecticPauliSign_and_mul (u, v) (u, v) (u, v) (a, b) (a, b) (a, b)).1]
      refine congrArg (· • ((weylPauliZ u * weylPauliX v) * (weylPauliZ a * weylPauliX b)))
        (congrArg signScalar (Finset.sum_congr rfl fun q _ => by ring))
    calc (weylPauliZ a * weylPauliX b) * sys.syndromeProjector (staticCSSPauliFlip D_field u v)
      _ = ((weylPauliZ a * weylPauliX b) * U) * sys.P0 * U_inv := by
          rw [h_proj_eq]; simp only [mul_assoc]
      _ = ((symplecticPauliSign (u, v) (a, b) : ℝ) : ℂ) •
            (U * ((weylPauliZ a * weylPauliX b) * sys.P0) * U_inv) := by
          rw [h_comm_U, clm_smul_mul, clm_smul_mul]; simp only [mul_assoc]
      _ = ((symplecticPauliSign (u, v) (a, b) : ℝ) : ℂ) •
            sys.syndromeProjector (staticCSSPauliFlip D_field u v) := by
          rw [hab_P0, ← h_proj_eq]
  refine ⟨h_part1, fun {γ} hγ {σ₀} hσ₀ => ?_⟩
  rcases (Finset.mem_filter.mp hσ₀).2 with ⟨u, v, rfl⟩
  intro μ
  rw [h_part1 (fun ν hν => symplecticPauliSign_coset_add_loop_eq_one D_field h_valid sys h_sys_checks hγ hν) u v]
  exact congrArg (fun x : ℝ => (x : ℂ) • sys.syndromeProjector (staticCSSPauliFlip D_field u v))
    (spanningSurfaceSign_worldlinePolymerSpanningSurface_eq_symplecticPauliSign
      D_field h_valid sys h_sys_checks hγ u v).symm

/-- Time-reversal invariance of monomer supports, native check collars, net loop bitstrings,
and `IsValidWorldlinePolymer` under $\gamma \mapsto \gamma^{\mathrm{rev}} = (\gamma.1.\mathrm{reverse}, \gamma.2)$
(Part II, Section 3.5 (`subsec:worldline-expansion`), Lemma 3.9 (`lem:worldline-factorization-time-reversal`)). -/
lemma worldlinePolymer_reverse_invariants
    {L q_code r_0 m_max R_cut : ℕ} [NeZero L]
    {C_RCA : ℝ}
    (D_field : Box3D L → LocalCSSDescriptor q_code r_0 m_max)
    (sys : SysCSS[L, q_code, m_max])
    (γ : WorldlineDysonPolymer L q_code) :
    let γ_rev : WorldlineDysonPolymer L q_code := (γ.1.reverse, γ.2)
    worldlinePolymerMonomers γ_rev = worldlinePolymerMonomers γ ∧
    worldlinePolymerNativeCollar sys C_RCA γ_rev = worldlinePolymerNativeCollar sys C_RCA γ ∧
    worldlinePolymerLoopX γ_rev = worldlinePolymerLoopX γ ∧
    worldlinePolymerLoopZ γ_rev = worldlinePolymerLoopZ γ ∧
    (IsValidWorldlinePolymer D_field sys C_RCA R_cut γ_rev ↔
      IsValidWorldlinePolymer D_field sys C_RCA R_cut γ) := by
  intro γ_rev
  have h_mon : worldlinePolymerMonomers γ_rev = worldlinePolymerMonomers γ := by
    unfold worldlinePolymerMonomers; dsimp [γ_rev]; rw [List.map_reverse, List.toFinset_reverse]
  have h_col : worldlinePolymerNativeCollar sys C_RCA γ_rev =
      worldlinePolymerNativeCollar sys C_RCA γ := by
    unfold worldlinePolymerNativeCollar; rw [h_mon]
  have h_X : worldlinePolymerLoopX γ_rev = worldlinePolymerLoopX γ := by
    unfold worldlinePolymerLoopX; dsimp [γ_rev]; rw [List.map_reverse, List.sum_reverse]
  have h_Z : worldlinePolymerLoopZ γ_rev = worldlinePolymerLoopZ γ := by
    unfold worldlinePolymerLoopZ; dsimp [γ_rev]; rw [List.map_reverse, List.sum_reverse]
  refine ⟨h_mon, h_col, h_X, h_Z, ?_⟩
  unfold IsValidWorldlinePolymer; rw [h_mon, h_X, h_Z]; dsimp [γ_rev]; rw [List.length_reverse]
  refine and_congr_right fun _ => and_congr_left fun _ => ?_
  exact ⟨fun h ξ hξ => h ξ (List.mem_reverse.mpr hξ),
    fun h ξ hξ => h ξ (List.mem_reverse.mp hξ)⟩

/-- Time-reversal invariance of `worldlinePolymerBoundingBoxCollar`, `IsSpanningCheckSurfaceForPolymer`,
`worldlinePolymerSpanningSurface`, and `worldlinePolymerLogicalCoset` under
 $\gamma \mapsto \gamma^{\mathrm{rev}} = (\gamma.1.\mathrm{reverse}, \gamma.2)$
(Part II, Section 3.5 (`subsec:worldline-expansion`), Lemma 3.9 (`lem:worldline-factorization-time-reversal`), Equation `eq:P-gamma-spanning-surface`). -/
lemma worldlinePolymerSpanningSurface_and_logicalCoset_reverse_eq
    {L q_code r_0 m_max : ℕ} [NeZero L] {C_RCA : ℝ}
    (D_field : Box3D L → LocalCSSDescriptor q_code r_0 m_max) (sys : SysCSS[L, q_code, m_max])
    (γ : WorldlineDysonPolymer L q_code) :
    let γ_rev : WorldlineDysonPolymer L q_code := (γ.1.reverse, γ.2)
    worldlinePolymerBoundingBoxCollar sys C_RCA γ_rev = worldlinePolymerBoundingBoxCollar sys C_RCA γ ∧
    (∀ μ α, IsSpanningCheckSurfaceForPolymer D_field sys γ_rev μ α ↔
      IsSpanningCheckSurfaceForPolymer D_field sys γ μ α) ∧
    worldlinePolymerSpanningSurface D_field sys C_RCA γ_rev = worldlinePolymerSpanningSurface D_field sys C_RCA γ ∧
    worldlinePolymerLogicalCoset D_field sys C_RCA γ_rev = worldlinePolymerLogicalCoset D_field sys C_RCA γ := by
  intro γ_rev
  rcases worldlinePolymer_reverse_invariants (R_cut := 0) (C_RCA := C_RCA) D_field sys γ with ⟨h_mon, _, h_X, h_Z, _⟩
  have h_cube : worldlinePolymerCubeUnion γ_rev = worldlinePolymerCubeUnion γ := by
    unfold worldlinePolymerCubeUnion; rw [h_mon]
  have h_ball : HasEnclosingPolymerBall γ_rev = HasEnclosingPolymerBall γ :=
    funext fun r => propext (by unfold HasEnclosingPolymerBall; rw [h_cube])
  have h_diam : worldlinePolymerDiameter γ_rev = worldlinePolymerDiameter γ := by
    unfold worldlinePolymerDiameter HasEnclosingPolymerBall; rw [h_cube]
  have h_bbox : worldlinePolymerBoundingBox γ_rev = worldlinePolymerBoundingBox γ := by
    unfold worldlinePolymerBoundingBox HasEnclosingPolymerBall; rw [h_diam, h_cube]
  have h_bcol : worldlinePolymerBoundingBoxCollar sys C_RCA γ_rev =
      worldlinePolymerBoundingBoxCollar sys C_RCA γ := by
    unfold worldlinePolymerBoundingBoxCollar; rw [h_diam, h_bbox]
  have h_loop : ∃ r : ℝ, r ≠ 0 ∧ worldlinePolymerLoopOp γ_rev = ((r : ℝ) : ℂ) • worldlinePolymerLoopOp γ := by
    rcases list_prod_map_worldlineJumpOpZX_eq_signScalar_smul γ.1.reverse with ⟨s₁, hs₁⟩
    rcases list_prod_map_worldlineJumpOpZX_eq_signScalar_smul γ.1 with ⟨s₂, hs₂⟩
    have hX₁ : (γ.1.reverse.map (fun ξ => ξ.2.1)).sum = worldlinePolymerLoopX γ := by
      unfold worldlinePolymerLoopX; rw [List.map_reverse, List.sum_reverse]
    have hZ₁ : (γ.1.reverse.map (fun ξ => ξ.2.2)).sum = worldlinePolymerLoopZ γ := by
      unfold worldlinePolymerLoopZ; rw [List.map_reverse, List.sum_reverse]
    rw [hX₁, hZ₁] at hs₁
    have hs₁' : worldlinePolymerLoopOp γ =
        signScalar s₁ • (weylPauliZ (worldlinePolymerLoopX γ) * weylPauliX (worldlinePolymerLoopZ γ)) := hs₁
    have hs₂' : worldlinePolymerLoopOp γ_rev =
        signScalar s₂ • (weylPauliZ (worldlinePolymerLoopX γ) * weylPauliX (worldlinePolymerLoopZ γ)) := by
      unfold worldlinePolymerLoopOp; dsimp [γ_rev]; rw [List.reverse_reverse]; exact hs₂
    let r : ℝ := if s₂ + s₁ = 0 then 1 else -1
    have hr_ne : r ≠ 0 := by dsimp [r]; split_ifs <;> norm_num
    have hr_eq : ((r : ℝ) : ℂ) = signScalar (s₂ + s₁) := by dsimp [r, signScalar]; split_ifs <;> norm_num
    refine ⟨r, hr_ne, ?_⟩; rw [hr_eq, hs₁', hs₂', smul_smul, ← signScalar_add]
    have h_add : s₂ + s₁ + s₁ = s₂ := by generalize s₂ = a; generalize s₁ = b; revert a b; decide
    rw [h_add]
  have h_span_iff : ∀ μ α, IsSpanningCheckSurfaceForPolymer D_field sys γ_rev μ α ↔
      IsSpanningCheckSurfaceForPolymer D_field sys γ μ α := fun μ α => by
    rcases h_loop with ⟨r, hr_ne, hr_loop⟩
    unfold IsSpanningCheckSurfaceForPolymer; (try dsimp only); rw [hr_loop, clm_mul_smul]
    let L₀ := (hermitianPauliZX μ.1 μ.2)† * worldlinePolymerLoopOp γ
    have h_tr : ∀ P T : ℬ_CSS[L, q_code], hilbertTrace (P * (((r : ℝ) : ℂ) • T)) = r * hilbertTrace (P * T) :=
      fun P T => by rw [clm_mul_smul, (hilbertTrace_add_and_complex_smul_decomp _ 0 0 0 r 0).2.1]
    have h_I : Complex.I • (((r : ℝ) : ℂ) • L₀) = ((r : ℝ) : ℂ) • (Complex.I • L₀) := smul_comm _ _ _
    have hr_nz : ∀ x : ℝ, r * x ≠ 0 ↔ x ≠ 0 := fun x => ⟨fun h hx => h (by rw [hx, mul_zero]), mul_ne_zero hr_ne⟩
    rw [h_I, h_tr sys.P0 L₀, h_tr sys.P0 (Complex.I • L₀), hr_nz, hr_nz]
    refine and_congr_right fun _ => forall₂_congr fun σ _ => ?_
    rw [h_tr (sys.syndromeProjector σ) L₀, h_tr (sys.syndromeProjector σ) (Complex.I • L₀),
      mul_left_comm (spanningSurfaceSign α σ) r, mul_left_comm (spanningSurfaceSign α σ) r,
      mul_right_inj' hr_ne, mul_right_inj' hr_ne]
  have h_span_eq : IsSpanningCheckSurfaceForPolymer D_field sys γ_rev =
      IsSpanningCheckSurfaceForPolymer D_field sys γ :=
    funext fun μ => funext fun α => propext (h_span_iff μ α)
  have h_coset : worldlinePolymerLogicalCoset D_field sys C_RCA γ_rev =
      worldlinePolymerLogicalCoset D_field sys C_RCA γ := by
    unfold worldlinePolymerLogicalCoset; dsimp only [γ_rev]; rw [h_X, h_Z]
  refine ⟨h_bcol, h_span_iff, ?_, h_coset⟩
  dsimp only [γ_rev] at h_bcol h_span_eq h_coset ⊢
  unfold worldlinePolymerSpanningSurface; simp only [h_bcol, h_span_eq, h_coset]

/-- When the net logical coset sum `(K.map (worldlinePolymerLogicalCoset D_field sys C_RCA)).sum` vanishes,
any global spanning surface `α_K` for the net loop bitstring `(a_K, b_K)` has the same parity sign
on every realizable syndrome `σ₀ ∈ realizableSyndromes D_field` as the product of the individual
polymer spanning-surface signs `spanningSurfaceSign (worldlinePolymerSpanningSurface D_field sys C_RCA γ) σ₀`
(Part II, Section 3.5 (`subsec:worldline-expansion`), Lemma 3.9 (`lem:worldline-factorization-time-reversal`), Equation `eq:P-gamma-spanning-surface`). -/
lemma spanningSurfaceSign_eq_prod_worldlinePolymerSpanningSurface_of_sum_logicalCoset_eq_zero
    {L q_code r_0 m_max R_cut : ℕ} [NeZero L] {C_RCA : ℝ}
    (D_field : Box3D L → LocalCSSDescriptor q_code r_0 m_max) (h_valid : ValidDescriptorField D_field)
    (sys : SysCSS[L, q_code, m_max])
    (h_sys_checks : ∀ idx, sys.checkProj idx = staticCSSCheckProj D_field idx ∧
      sys.support idx = staticCSSCheckSupport D_field idx ∧ sys.weight idx = 1)
    (K : WorldlineUrsellCluster L q_code)
    (hK_valid : ∀ γ ∈ K, IsValidWorldlinePolymer D_field sys C_RCA R_cut γ)
    (h_coset_zero : (K.map (worldlinePolymerLogicalCoset D_field sys C_RCA)).sum = 0)
    {α_K : Finset (IdxCSS[L, q_code, m_max])}
    (hα_sign : ∀ u v : BoxSlot3D L q_code → ZMod 2,
      symplecticPauliSign (u, v) ((K.map worldlinePolymerLoopX).sum, (K.map worldlinePolymerLoopZ).sum) =
        spanningSurfaceSign α_K (staticCSSPauliFlip D_field u v))
    {σ₀ : IdxCSS[L, q_code, m_max] → Bool} (hσ₀ : σ₀ ∈ realizableSyndromes D_field) :
    spanningSurfaceSign α_K σ₀ =
      (K.map (fun γ => spanningSurfaceSign (worldlinePolymerSpanningSurface D_field sys C_RCA γ) σ₀)).prod := by
  rcases (Finset.mem_filter.mp hσ₀).2 with ⟨u, v, rfl⟩
  rw [prod_spanningSurfaceSign_worldlinePolymerSpanningSurface_eq_symplecticPauliSign
    D_field h_valid sys h_sys_checks K hK_valid u v, h_coset_zero, zero_add,
    (list_sum_worldlinePolymerLoop_pair_and_prod_loopOp_eq K).1, hα_sign u v]

/-- Multi-polymer sector trace reduction to the vacuum projector `sys.P0` when the net loop Pauli
operator commutes with all syndrome-closed Pauli operators `ν ∈ syndromeClosedPauliFinset D_field`
(Part II, Section 3.5 (`subsec:worldline-expansion`), Lemma 3.9 (`lem:worldline-factorization-time-reversal`), Equation `eq:P-gamma-spanning-surface`). -/
lemma multiPolymer_syndromeProjector_trace_eq_vacuum_trace_of_commute_syndromeClosed
    {L q_code r_0 m_max L_star R_cut : ℕ} [NeZero L] {C_RCA : ℝ}
    (D_field : Box3D L → LocalCSSDescriptor q_code r_0 m_max) (h_valid : ValidDescriptorField D_field)
    (sys : SysCSS[L, q_code, m_max])
    (h_sys_checks : ∀ idx, sys.checkProj idx = staticCSSCheckProj D_field idx ∧
      sys.support idx = staticCSSCheckSupport D_field idx ∧ sys.weight idx = 1)
    (h_tqo1 : SatisfiesTQO1 sys L_star) (h_tqo2 : SatisfiesSectorFilteredLinearTQO2 sys 1 L_star C_RCA)
    (hR_le : R_cut ≤ L_star) (V : QuasiLocalPerturbation 3 L (SiteCSS[L, q_code]))
    (K : WorldlineUrsellCluster L q_code)
    (hK_valid : ∀ γ ∈ K, IsValidWorldlinePolymer D_field sys C_RCA R_cut γ)
    (h_comm : ∀ ν ∈ syndromeClosedPauliFinset D_field,
      symplecticPauliSign ν (K.map (fun γ => (worldlinePolymerLoopX γ, worldlinePolymerLoopZ γ))).sum = 1)
    {σ₀ : IdxCSS[L, q_code, m_max] → Bool} (hσ₀ : σ₀ ∈ realizableSyndromes D_field) :
    let a_K := (K.map worldlinePolymerLoopX).sum
    let b_K := (K.map worldlinePolymerLoopZ).sum
    ∃ (α_K : Finset (IdxCSS[L, q_code, m_max])) (c_K : Fin K.length → ℂ) (s_K : ZMod 2),
      (∀ u v : BoxSlot3D L q_code → ZMod 2,
        symplecticPauliSign (u, v) (a_K, b_K) = spanningSurfaceSign α_K (staticCSSPauliFlip D_field u v)) ∧
      (∀ i : Fin K.length,
        worldlinePolymerWeightedLoopOp D_field sys V (K.get i) * sys.syndromeProjector σ₀ =
          c_K i • (worldlinePolymerLoopOp (K.get i) * sys.syndromeProjector σ₀)) ∧
      (K.map worldlinePolymerLoopOp).prod = signScalar s_K • (weylPauliZ a_K * weylPauliX b_K) ∧
      hilbertTrace (sys.syndromeProjector σ₀ * (K.map (worldlinePolymerWeightedLoopOp D_field sys V)).prod) =
        spanningSurfaceSign α_K σ₀ * ((∏ i : Fin K.length, c_K i) * signScalar s_K).re * hilbertTrace sys.P0 := by
  intro a_K b_K
  rcases list_sum_worldlinePolymerLoop_pair_and_prod_loopOp_eq K with ⟨h_sum_pair, s_K, hs_K⟩
  have h_comm_ab : ∀ ν ∈ syndromeClosedPauliFinset D_field, symplecticPauliSign ν (a_K, b_K) = 1 :=
    fun ν hν => by have h1 := h_comm ν hν; rwa [h_sum_pair] at h1
  rcases exists_global_spanning_surface_of_commute_syndromeClosed
      D_field sys h_sys_checks h_comm_ab with ⟨α_K, _, hα_sign, hα_trace⟩
  rcases list_prod_worldlinePolymerWeightedLoopOp_mul_syndromeProjector_eq
      D_field h_valid sys h_sys_checks h_tqo1 h_tqo2 hR_le V K hK_valid hσ₀ with ⟨c_K, hc_i, hc_K⟩
  let z_K : ℂ := (∏ i : Fin K.length, c_K i) * signScalar s_K
  let W_K := z_K • (weylPauliZ a_K * weylPauliX b_K)
  have h_idem := ((PerturbedThermalBarrier.syndrome_resolution_indexed sys).2.1 σ₀).1
  have h_tr_W : hilbertTrace (sys.syndromeProjector σ₀ *
      (K.map (worldlinePolymerWeightedLoopOp D_field sys V)).prod) =
      hilbertTrace (sys.syndromeProjector σ₀ * W_K) := by
    calc hilbertTrace (sys.syndromeProjector σ₀ *
          (K.map (worldlinePolymerWeightedLoopOp D_field sys V)).prod)
      _ = hilbertTrace ((sys.syndromeProjector σ₀ * sys.syndromeProjector σ₀) *
            (K.map (worldlinePolymerWeightedLoopOp D_field sys V)).prod) := by rw [h_idem]
      _ = hilbertTrace (sys.syndromeProjector σ₀ *
            ((K.map (worldlinePolymerWeightedLoopOp D_field sys V)).prod * sys.syndromeProjector σ₀)) := by
          rw [mul_assoc, hilbertTrace_mul_comm_aux (sys.syndromeProjector σ₀) _, mul_assoc]
      _ = hilbertTrace (sys.syndromeProjector σ₀ * (W_K * sys.syndromeProjector σ₀)) := by
          rw [hc_K, hs_K, clm_smul_mul, smul_smul]; rfl
      _ = hilbertTrace ((sys.syndromeProjector σ₀ * sys.syndromeProjector σ₀) * W_K) := by
          rw [← mul_assoc (sys.syndromeProjector σ₀) W_K,
            hilbertTrace_mul_comm_aux _ (sys.syndromeProjector σ₀), ← mul_assoc]
      _ = hilbertTrace (sys.syndromeProjector σ₀ * W_K) := by rw [h_idem]
  refine ⟨α_K, c_K, s_K, hα_sign, hc_i, hs_K, ?_⟩
  rw [h_tr_W, hα_trace σ₀ hσ₀ z_K,
    (weylPauliZX_mul_P0_and_trace_eq_of_commute_syndromeClosed D_field sys h_sys_checks h_comm_ab).2.2.2 z_K,
    mul_assoc]

/-- Time-reversal adjoint action of `worldlinePolymerWeightedLoopOp` and invariance of
`worldlinePolymerLoopAmplitude` under $\gamma \mapsto \gamma^{\mathrm{rev}} = (\gamma.1.\mathrm{reverse}, \gamma.2)$
(Part II, Section 3.5 (`subsec:worldline-expansion`), Lemma 3.9 (`lem:worldline-factorization-time-reversal`), Equation `eq:P-gamma-spanning-surface`). -/
lemma worldlinePolymerWeightedLoopOp_and_loopAmplitude_reverse_eq
    {L q_code r_0 m_max L_star R_cut : ℕ} [NeZero L] {C_RCA : ℝ}
    (D_field : Box3D L → LocalCSSDescriptor q_code r_0 m_max) (h_valid : ValidDescriptorField D_field)
    (sys : SysCSS[L, q_code, m_max])
    (h_sys_checks : ∀ idx, sys.checkProj idx = staticCSSCheckProj D_field idx ∧
      sys.support idx = staticCSSCheckSupport D_field idx ∧ sys.weight idx = 1)
    (h_tqo1 : SatisfiesTQO1 sys L_star) (h_tqo2 : SatisfiesSectorFilteredLinearTQO2 sys 1 L_star C_RCA)
    (hR_le : R_cut ≤ L_star) (V : QuasiLocalPerturbation 3 L (SiteCSS[L, q_code]))
    (γ : WorldlineDysonPolymer L q_code) (hγ : IsValidWorldlinePolymer D_field sys C_RCA R_cut γ)
    {σ₀ : IdxCSS[L, q_code, m_max] → Bool} (hσ₀ : σ₀ ∈ realizableSyndromes D_field) :
    let γ_rev : WorldlineDysonPolymer L q_code := (γ.1.reverse, γ.2)
    let μ := worldlinePolymerLogicalCoset D_field sys C_RCA γ
    let α := worldlinePolymerSpanningSurface D_field sys C_RCA γ
    let A_γ := worldlinePolymerLoopAmplitude D_field sys C_RCA V γ
      (restrictSyndromeToCollar (worldlinePolymerNativeCollar sys C_RCA γ) σ₀)
    (∃ ω_γ : ℂ, ω_γ.re = A_γ ∧
      worldlinePolymerWeightedLoopOp D_field sys V γ * sys.syndromeProjector σ₀ =
        (ω_γ * spanningSurfaceSign α σ₀) • (hermitianPauliZX μ.1 μ.2 * sys.syndromeProjector σ₀) ∧
      worldlinePolymerWeightedLoopOp D_field sys V γ_rev * sys.syndromeProjector σ₀ =
        (star ω_γ * spanningSurfaceSign α σ₀) • (hermitianPauliZX μ.1 μ.2 * sys.syndromeProjector σ₀)) ∧
    (((1 / 2 : ℂ) • (worldlinePolymerWeightedLoopOp D_field sys V γ +
        worldlinePolymerWeightedLoopOp D_field sys V γ_rev)) * sys.syndromeProjector σ₀ =
      ((A_γ * spanningSurfaceSign α σ₀ : ℝ) : ℂ) • (hermitianPauliZX μ.1 μ.2 * sys.syndromeProjector σ₀)) ∧
    worldlinePolymerLoopAmplitude D_field sys C_RCA V γ_rev
      (restrictSyndromeToCollar (worldlinePolymerNativeCollar sys C_RCA γ_rev) σ₀) = A_γ := by
  intro γ_rev μ α A_γ
  let a := worldlinePolymerLoopX γ
  let b := worldlinePolymerLoopZ γ
  let L_op := (hermitianPauliZX μ.1 μ.2)† * worldlinePolymerLoopOp γ
  rcases exists_collar_scalar_worldlinePolymerLoopAmplitude_and_weightedLoopOp_eq
      D_field h_valid sys h_sys_checks h_tqo1 h_tqo2 hR_le V γ hγ with ⟨C_γ, _, hC_act⟩
  rcases hC_act σ₀ hσ₀ with ⟨hB_act, hA_eq⟩
  rcases hermitianPauliZX_isSelfAdjoint_and_sq_eq_one μ.1 μ.2 with ⟨hM_sa, hM_sq⟩
  have hM_adj : (hermitianPauliZX μ.1 μ.2)† = hermitianPauliZX μ.1 μ.2 :=
    ContinuousLinearMap.isSelfAdjoint_iff'.mp hM_sa
  have hM_zx : ∃ z₁ : ℂ, hermitianPauliZX μ.1 μ.2 = z₁ • (weylPauliZ μ.1 * weylPauliX μ.2) := by
    unfold hermitianPauliZX; split_ifs <;> [exact ⟨1, (one_smul ℂ _).symm⟩; exact ⟨Complex.I, rfl⟩]
  rcases hM_zx with ⟨z₁, hz₁⟩
  rcases list_prod_map_worldlineJumpOpZX_eq_signScalar_smul γ.1.reverse with ⟨s_loop, hs_loop⟩
  have h_sum_X : (γ.1.reverse.map (fun ξ => ξ.2.1)).sum = a := by
    dsimp [a, worldlinePolymerLoopX]; rw [List.map_reverse, List.sum_reverse]
  have h_sum_Z : (γ.1.reverse.map (fun ξ => ξ.2.2)).sum = b := by
    dsimp [b, worldlinePolymerLoopZ]; rw [List.map_reverse, List.sum_reverse]
  rw [h_sum_X, h_sum_Z] at hs_loop
  have h_loop_zx : worldlinePolymerLoopOp γ = signScalar s_loop • (weylPauliZ a * weylPauliX b) := hs_loop
  let z₀ : ℂ := z₁ * signScalar s_loop * signScalar (∑ p, a p * μ.2 p)
  have hL_zx : L_op = z₀ • (weylPauliZ (μ.1 + a) * weylPauliX (μ.2 + b)) := by
    dsimp [L_op, z₀]; rw [hM_adj, hz₁, h_loop_zx, clm_smul_mul, clm_mul_smul, smul_smul,
      weylPauliZX_mul_weylPauliZX μ.1 μ.2 a b, smul_smul]
  let ω_γ : ℂ := C_γ σ₀ * z₀
  have h_stab : ∀ ν ∈ syndromeClosedPauliFinset D_field, symplecticPauliSign ν (μ.1 + a, μ.2 + b) = 1 :=
    fun ν hν => symplecticPauliSign_coset_add_loop_eq_one D_field h_valid sys h_sys_checks hγ hν
  have h_res := PerturbedThermalBarrier.syndrome_resolution_indexed sys
  have hP0_pos : 0 < hilbertTrace sys.P0 := by
    rw [← h_res.1]
    exact hilbertTrace_pos_of_isStarProjection_ne_zero (h_res.2.1 (fun _ => false))
      (by rw [h_res.1]; exact sys_P0_ne_zero_of_validDescriptorField D_field h_valid sys h_sys_checks)
  have hω_re : ω_γ.re = A_γ := by
    have h_tr := (weylPauliZX_mul_P0_and_trace_eq_of_commute_syndromeClosed
      D_field sys h_sys_checks h_stab).2.2.2 ω_γ
    have h_smul : C_γ σ₀ • L_op = ω_γ • (weylPauliZ (μ.1 + a) * weylPauliX (μ.2 + b)) := by
      rw [hL_zx, smul_smul]
    change ω_γ.re = worldlinePolymerLoopAmplitude D_field sys C_RCA V γ
      (restrictSyndromeToCollar (worldlinePolymerNativeCollar sys C_RCA γ) σ₀)
    rw [hA_eq, h_smul, h_tr, mul_div_cancel_right₀ _ (ne_of_gt hP0_pos)]
  have h_zx_act := (weylPauliZX_mul_syndromeProjector_eq_of_commute_syndromeClosed
    D_field h_valid sys h_sys_checks).2 hγ hσ₀
  have hL_act : L_op * sys.syndromeProjector σ₀ =
      (z₀ * spanningSurfaceSign α σ₀) • sys.syndromeProjector σ₀ := by
    rw [hL_zx, clm_smul_mul, h_zx_act, smul_smul]
  have h_loop_act : worldlinePolymerLoopOp γ * sys.syndromeProjector σ₀ =
      (z₀ * spanningSurfaceSign α σ₀) • (hermitianPauliZX μ.1 μ.2 * sys.syndromeProjector σ₀) := by
    calc worldlinePolymerLoopOp γ * sys.syndromeProjector σ₀
      _ = (hermitianPauliZX μ.1 μ.2 * (hermitianPauliZX μ.1 μ.2)†) *
            worldlinePolymerLoopOp γ * sys.syndromeProjector σ₀ := by rw [hM_adj, hM_sq, one_mul]
      _ = hermitianPauliZX μ.1 μ.2 * (L_op * sys.syndromeProjector σ₀) := by dsimp [L_op]; simp only [mul_assoc]
      _ = (z₀ * spanningSurfaceSign α σ₀) • (hermitianPauliZX μ.1 μ.2 * sys.syndromeProjector σ₀) := by
          rw [hL_act, clm_mul_smul]
  have hB_eq : worldlinePolymerWeightedLoopOp D_field sys V γ * sys.syndromeProjector σ₀ =
      (ω_γ * spanningSurfaceSign α σ₀) • (hermitianPauliZX μ.1 μ.2 * sys.syndromeProjector σ₀) := by
    rw [hB_act, h_loop_act, smul_smul]; congr 1; dsimp [ω_γ, z₀]; ring
  have hγ_rev : IsValidWorldlinePolymer D_field sys C_RCA R_cut γ_rev :=
    (worldlinePolymer_reverse_invariants D_field sys γ).2.2.2.2.mpr hγ
  rcases (exists_collar_scalar_worldlinePolymerWeightedLoopOp_and_commute_loopOp
    D_field h_valid sys h_sys_checks h_tqo1 h_tqo2 hR_le V hγ).2 with ⟨_, _, hB_proj⟩
  rcases (exists_collar_scalar_worldlinePolymerWeightedLoopOp_and_commute_loopOp
    D_field h_valid sys h_sys_checks h_tqo1 h_tqo2 hR_le V hγ_rev).2 with ⟨_, _, hBrev_proj⟩
  have hP_star : star (sys.syndromeProjector σ₀) = sys.syndromeProjector σ₀ :=
    (h_res.2.1 σ₀).2.star_eq
  have hH_star : star (hermitianPauliZX μ.1 μ.2) = hermitianPauliZX μ.1 μ.2 := by
    rw [ContinuousLinearMap.star_eq_adjoint, hM_adj]
  have hμ_closed := (isSpanningCheckSurfaceForPolymer_of_isValidWorldlinePolymer
    D_field h_valid sys h_sys_checks γ hγ).1
  have hH_comm : hermitianPauliZX μ.1 μ.2 * sys.syndromeProjector σ₀ =
      sys.syndromeProjector σ₀ * hermitianPauliZX μ.1 μ.2 := by
    rw [hz₁, clm_smul_mul, clm_mul_smul,
      ((weylPauliZX_comm_checkProj_and_syndromeProjector_of_syndromeClosed
        D_field sys h_sys_checks hμ_closed).2.1 σ₀).eq]
  have hHP_star : star (hermitianPauliZX μ.1 μ.2 * sys.syndromeProjector σ₀) =
      hermitianPauliZX μ.1 μ.2 * sys.syndromeProjector σ₀ := by
    rw [star_mul, hP_star, hH_star, hH_comm]
  have hB_rev_adj : star (worldlinePolymerWeightedLoopOp D_field sys V γ) =
      worldlinePolymerWeightedLoopOp D_field sys V γ_rev := by
    rw [ContinuousLinearMap.star_eq_adjoint,
      ((worldlineSyndromeShiftBlockOp_isSelfAdjoint_and_reverse_weightedLoopOp D_field sys V).2 γ).symm]
  have hBP_star : star (worldlinePolymerWeightedLoopOp D_field sys V γ * sys.syndromeProjector σ₀) =
      worldlinePolymerWeightedLoopOp D_field sys V γ_rev * sys.syndromeProjector σ₀ := by
    calc star (worldlinePolymerWeightedLoopOp D_field sys V γ * sys.syndromeProjector σ₀)
      _ = star (sys.syndromeProjector σ₀ *
            (worldlinePolymerWeightedLoopOp D_field sys V γ * sys.syndromeProjector σ₀)) := by
          rw [(hB_proj σ₀ hσ₀).2]
      _ = sys.syndromeProjector σ₀ *
            (worldlinePolymerWeightedLoopOp D_field sys V γ_rev * sys.syndromeProjector σ₀) := by
          rw [star_mul, star_mul, hP_star, hB_rev_adj, mul_assoc]
      _ = worldlinePolymerWeightedLoopOp D_field sys V γ_rev * sys.syndromeProjector σ₀ :=
          (hBrev_proj σ₀ hσ₀).2
  have hBrev_eq : worldlinePolymerWeightedLoopOp D_field sys V γ_rev * sys.syndromeProjector σ₀ =
      (star ω_γ * spanningSurfaceSign α σ₀) • (hermitianPauliZX μ.1 μ.2 * sys.syndromeProjector σ₀) := by
    rw [← hBP_star, hB_eq, star_smul, hHP_star, star_mul, Complex.star_def, Complex.conj_ofReal,
      ← Complex.star_def, mul_comm ((spanningSurfaceSign α σ₀ : ℝ) : ℂ) (star ω_γ)]
  have h_avg : (((1 / 2 : ℂ) • (worldlinePolymerWeightedLoopOp D_field sys V γ +
        worldlinePolymerWeightedLoopOp D_field sys V γ_rev)) * sys.syndromeProjector σ₀) =
      ((A_γ * spanningSurfaceSign α σ₀ : ℝ) : ℂ) • (hermitianPauliZX μ.1 μ.2 * sys.syndromeProjector σ₀) := by
    rw [clm_smul_mul, add_mul, hB_eq, hBrev_eq, ← add_smul, smul_smul]
    congr 1
    rw [← hω_re]
    apply Complex.ext
    · simp [Complex.add_re, Complex.mul_re, Complex.mul_im]; ring
    · simp [Complex.add_im, Complex.mul_re, Complex.mul_im]
  refine ⟨⟨ω_γ, hω_re, hB_eq, hBrev_eq⟩, h_avg, ?_⟩
  have hV_supp : ∀ r ∈ Finset.Icc 1 (min R_cut L), ∀ A ∈ boxCubes 3 L r,
      IsSupportedOn (SiteCSS[L, q_code]) A (V.term r A) :=
    fun r hr A hA => V.is_supported r (Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp hr).1,
      le_trans (Finset.mem_Icc.mp hr).2 (Nat.min_le_right R_cut L)⟩) A hA
  have h_amp_rev := spanningSurfaceSign_mul_worldlinePolymerLoopAmplitude_eq_of_valid
    D_field h_valid sys h_sys_checks h_tqo1 h_tqo2 hR_le V hV_supp γ_rev hγ_rev hσ₀
  rcases worldlinePolymerSpanningSurface_and_logicalCoset_reverse_eq D_field sys γ with
    ⟨_, _, h_span_rev, h_coset_rev⟩
  rw [h_span_rev, h_coset_rev] at h_amp_rev
  have h_idem := (h_res.2.1 σ₀).1
  have h_tr_rev : hilbertTrace (sys.syndromeProjector σ₀ *
      ((hermitianPauliZX μ.1 μ.2)† * worldlinePolymerWeightedLoopOp D_field sys V γ_rev)) =
      (star ω_γ * spanningSurfaceSign α σ₀).re * hilbertTrace (sys.syndromeProjector σ₀) := by
    have h_op : (hermitianPauliZX μ.1 μ.2)† *
        (worldlinePolymerWeightedLoopOp D_field sys V γ_rev * sys.syndromeProjector σ₀) =
        (star ω_γ * spanningSurfaceSign α σ₀) • sys.syndromeProjector σ₀ := by
      rw [hBrev_eq, clm_mul_smul, ← mul_assoc, hM_adj, hM_sq, one_mul]
    calc hilbertTrace (sys.syndromeProjector σ₀ *
          ((hermitianPauliZX μ.1 μ.2)† * worldlinePolymerWeightedLoopOp D_field sys V γ_rev))
      _ = hilbertTrace ((sys.syndromeProjector σ₀ * sys.syndromeProjector σ₀) *
            ((hermitianPauliZX μ.1 μ.2)† * worldlinePolymerWeightedLoopOp D_field sys V γ_rev)) := by rw [h_idem]
      _ = hilbertTrace (sys.syndromeProjector σ₀ *
            ((hermitianPauliZX μ.1 μ.2)† *
              (worldlinePolymerWeightedLoopOp D_field sys V γ_rev * sys.syndromeProjector σ₀))) := by
          rw [mul_assoc, hilbertTrace_mul_comm_aux (sys.syndromeProjector σ₀) _, mul_assoc, mul_assoc]
      _ = hilbertTrace (sys.syndromeProjector σ₀ *
            ((star ω_γ * spanningSurfaceSign α σ₀) • sys.syndromeProjector σ₀)) := by rw [h_op]
      _ = (star ω_γ * spanningSurfaceSign α σ₀).re * hilbertTrace (sys.syndromeProjector σ₀) := by
          rw [clm_mul_smul, h_idem, hilbertTrace_complex_smul_syndromeProjector]
  have hP_pos := (hilbertTrace_syndromeProjector_eq_P0_of_realizableSyndromes
    D_field h_valid sys h_sys_checks hσ₀).2
  have h_sign_sq := (spanningSurfaceSign_insert_and_identities α σ₀).2.1
  calc worldlinePolymerLoopAmplitude D_field sys C_RCA V γ_rev
        (restrictSyndromeToCollar (worldlinePolymerNativeCollar sys C_RCA γ_rev) σ₀)
    _ = spanningSurfaceSign α σ₀ * (spanningSurfaceSign α σ₀ *
          worldlinePolymerLoopAmplitude D_field sys C_RCA V γ_rev
            (restrictSyndromeToCollar (worldlinePolymerNativeCollar sys C_RCA γ_rev) σ₀)) := by
        rw [← mul_assoc, h_sign_sq, one_mul]
    _ = spanningSurfaceSign α σ₀ * ((star ω_γ * spanningSurfaceSign α σ₀).re *
          hilbertTrace (sys.syndromeProjector σ₀) / hilbertTrace (sys.syndromeProjector σ₀)) := by
        rw [h_amp_rev, h_tr_rev]
    _ = spanningSurfaceSign α σ₀ * (star ω_γ * spanningSurfaceSign α σ₀).re := by
        rw [mul_div_cancel_right₀ _ (ne_of_gt hP_pos)]
    _ = (spanningSurfaceSign α σ₀ * spanningSurfaceSign α σ₀) * ω_γ.re := by
        simp [Complex.mul_re]; ring
    _ = A_γ := by rw [h_sign_sq, one_mul, hω_re]

lemma abs_worldlineBareAction_le_sum
    {L q_code r_0 m_max w_0 R_cut : ℕ} [NeZero L]
    {C_RCA c_wl β : ℝ} (hR_cut : 1 ≤ R_cut) (hβ : 0 ≤ β)
    (D_field : Box3D L → LocalCSSDescriptor q_code r_0 m_max)
    (sys : SysCSS[L, q_code, m_max])
    (h_sys_checks : ∀ idx, sys.checkProj idx = staticCSSCheckProj D_field idx ∧
      sys.support idx = staticCSSCheckSupport D_field idx ∧ sys.weight idx = 1)
    (h_geom : sys.IsGeometricallyLocal r_0 w_0)
    (hc_wl_cal : (kpCollarMaxCheckCard R_cut r_0 w_0 C_RCA : ℝ) ≤ c_wl)
    (γ : WorldlineDysonPolymer L q_code)
    (hγ : IsValidWorldlinePolymer D_field sys C_RCA R_cut γ)
    (σ₀ : IdxCSS[L, q_code, m_max] → Bool)
    (τ : Fin γ.1.length → ℝ) :
    |worldlineBareAction D_field sys γ.1 σ₀ β τ| ≤
      β * (γ.1.map (fun ξ => (1 / 27 : ℝ) * c_wl * ((ξ.1.1 : ℝ) ^ 3))).sum := by
  unfold worldlineBareAction
  have hc_wl_nn : 0 ≤ c_wl := le_trans (Nat.cast_nonneg _) hc_wl_cal
  let w_step : WorldlineJumpMonomer L q_code → ℝ :=
    fun ξ => (1 / 27 : ℝ) * c_wl * ((ξ.1.1 : ℝ) ^ 3)
  have hw_nn : ∀ ξ : WorldlineJumpMonomer L q_code, 0 ≤ w_step ξ := fun ξ => by
    dsimp [w_step]; positivity
  have hC_nn : 0 ≤ (γ.1.map w_step).sum :=
    List.sum_nonneg (by intro y hy; rcases List.mem_map.mp hy with ⟨ξ, _, rfl⟩; exact hw_nn ξ)
  have h_traj_le : ∀ t ∈ Set.Icc 0 β,
      |sys.syndromeEnergy (worldlineTrajectorySyndrome D_field γ.1 σ₀ τ t) -
        sys.syndromeEnergy σ₀| ≤ (γ.1.map w_step).sum := by
    intro t _
    unfold worldlineTrajectorySyndrome
    let l := (List.finRange γ.1.length).filter (fun j => decide (τ j ≤ t))
    have h_fold := abs_syndromeEnergy_foldr_syndromeXor_sub_le_sum sys
      (fun idx => (h_sys_checks idx).2.2)
      (fun j => staticCSSPauliFlip D_field (γ.1.get j).2.1 (γ.1.get j).2.2)
      (fun j => cubeIntersectingChecks sys (γ.1.get j).1.2)
      (fun j => w_step (γ.1.get j))
      l
      (fun j _ => by
        let ξ := γ.1.get j
        have hξ_mem : ξ ∈ γ.1 := List.get_mem γ.1 j
        have hp_mem : ξ.1 ∈ worldlinePolymerMonomers γ :=
          Finset.mem_union_left _ (List.mem_toFinset.mpr (List.mem_map_of_mem hξ_mem))
        rcases mem_scaleCubeFinset_iff.mp (hγ.1 ξ.1 hp_mem) with ⟨hr, hA⟩
        refine ⟨fun c hc => staticCSSPauliFlip_mem_cubeIntersectingChecks D_field sys
          (fun idx => (h_sys_checks idx).2.1) ξ.1.2 ξ.2.1 ξ.2.2 (hγ.2.1 ξ hξ_mem).1 c hc,
          card_cubeIntersectingChecks_cast_le_div_twenty_seven hR_cut sys h_geom hc_wl_cal hr hA⟩)
      σ₀
    have h_filt_le : (l.map (fun j => w_step (γ.1.get j))).sum ≤
        ((List.finRange γ.1.length).map (fun j => w_step (γ.1.get j))).sum :=
      list_sum_map_filter_le (List.finRange γ.1.length) (fun j => decide (τ j ≤ t))
        (fun j => w_step (γ.1.get j)) (fun j _ => hw_nn (γ.1.get j))
    rw [list_map_finRange_get_eq_map γ.1 w_step] at h_filt_le
    exact le_trans h_fold h_filt_le
  exact abs_setIntegral_Icc_le_of_abs_le hβ hC_nn _ h_traj_le

lemma abs_exp_neg_worldlineBareAction_mul_prod_mayer_le_sum
    {L q_code r_0 m_max w_0 R_cut : ℕ} [NeZero L]
    {C_RCA c_wl β J : ℝ} {f : ℕ → ℝ}
    (hR_cut : 1 ≤ R_cut) (hβ : 0 ≤ β) (hJ : 0 ≤ J) (hf_nn : ∀ r, 0 ≤ f r)
    (D_field : Box3D L → LocalCSSDescriptor q_code r_0 m_max)
    (sys : SysCSS[L, q_code, m_max])
    (h_sys_checks : ∀ idx, sys.checkProj idx = staticCSSCheckProj D_field idx ∧
      sys.support idx = staticCSSCheckSupport D_field idx ∧ sys.weight idx = 1)
    (h_geom : sys.IsGeometricallyLocal r_0 w_0)
    (hc_wl_cal : (kpCollarMaxCheckCard R_cut r_0 w_0 C_RCA : ℝ) ≤ c_wl)
    (d_loc : ℕ → Finset (Box3D L) → (IdxCSS[L, q_code, m_max] → Bool) → ℝ)
    (hd_bound : ∀ r ∈ Finset.Icc 1 (min R_cut L), ∀ A ∈ boxCubes 3 L r, ∀ σ,
      |d_loc r A σ| ≤ 2 * (J * f r))
    (γ : WorldlineDysonPolymer L q_code)
    (hγ : IsValidWorldlinePolymer D_field sys C_RCA R_cut γ)
    (σ₀ : IdxCSS[L, q_code, m_max] → Bool)
    (τ : Fin γ.1.length → ℝ) :
    |Real.exp (-worldlineBareAction D_field sys γ.1 σ₀ β τ) *
      ∏ ϑ ∈ γ.2, worldlineMayerBondFactor D_field γ.1 d_loc σ₀ β ϑ τ| ≤
      (γ.1.map (fun ξ => Real.exp ((1 / 27 : ℝ) * c_wl * β * ((ξ.1.1 : ℝ) ^ 3)))).prod *
        ∏ ϑ ∈ γ.2, 4 * β * J * f ϑ.1 * Real.exp (4 * β * J * f ϑ.1) := by
  rw [abs_mul, abs_of_pos (Real.exp_pos _), Finset.abs_prod]
  have h_bare := abs_worldlineBareAction_le_sum hR_cut hβ D_field sys h_sys_checks h_geom hc_wl_cal γ hγ σ₀ τ
  have h_sum_eq :
      β * (γ.1.map (fun ξ => (1 / 27 : ℝ) * c_wl * ((ξ.1.1 : ℝ) ^ 3))).sum =
        (γ.1.map (fun ξ => (1 / 27 : ℝ) * c_wl * β * ((ξ.1.1 : ℝ) ^ 3))).sum := by
    induction γ.1 with
    | nil => simp
    | cons hd tl ih =>
      rw [List.map_cons, List.sum_cons, List.map_cons, List.sum_cons, mul_add, ih]
      ring
  have h_exp : Real.exp (-worldlineBareAction D_field sys γ.1 σ₀ β τ) ≤
      (γ.1.map (fun ξ => Real.exp ((1 / 27 : ℝ) * c_wl * β * ((ξ.1.1 : ℝ) ^ 3)))).prod := by
    rw [← exp_list_map_sum, ← h_sum_eq]
    exact Real.exp_le_exp.mpr (le_trans (neg_le_abs _) h_bare)
  have h_prod : ∏ ϑ ∈ γ.2, |worldlineMayerBondFactor D_field γ.1 d_loc σ₀ β ϑ τ| ≤
      ∏ ϑ ∈ γ.2, 4 * β * J * f ϑ.1 * Real.exp (4 * β * J * f ϑ.1) := by
    refine Finset.prod_le_prod₀ (fun ϑ _ => abs_nonneg _) (fun ϑ hϑ => ?_)
    exact abs_worldlineMayerBondFactor_le hβ hJ D_field sys f hf_nn d_loc hd_bound γ hγ σ₀ τ hϑ
  exact mul_le_mul h_exp h_prod (Finset.prod_nonneg (fun _ _ => abs_nonneg _))
    (List.prod_nonneg (by intro y hy; rcases List.mem_map.mp hy with ⟨_, _, rfl⟩; exact Real.exp_nonneg _))

def validJumpMonomersAtCube {L q_code r_0 m_max : ℕ}
    (D_field : Box3D L → LocalCSSDescriptor q_code r_0 m_max)
    (sys : SysCSS[L, q_code, m_max])
    (p : ℕ × Finset (Box3D L)) : Finset (WorldlineJumpMonomer L q_code) :=
  (cubeIntersectingChecks sys p.2).powerset.image
    (fun S => (p, canonicalJumpPauliRep D_field p.2 (fun c => decide (c ∈ S))))

lemma card_validJumpMonomersAtCube_le {L q_code r_0 m_max : ℕ}
    (D_field : Box3D L → LocalCSSDescriptor q_code r_0 m_max)
    (sys : SysCSS[L, q_code, m_max])
    (p : ℕ × Finset (Box3D L)) :
    (validJumpMonomersAtCube D_field sys p).card ≤ 2 ^ (cubeIntersectingChecks sys p.2).card :=
  le_trans Finset.card_image_le (by rw [Finset.card_powerset])

lemma mem_validJumpMonomersAtCube_of_valid {L q_code r_0 m_max R_cut : ℕ} [NeZero L]
    {C_RCA : ℝ}
    (D_field : Box3D L → LocalCSSDescriptor q_code r_0 m_max)
    (sys : SysCSS[L, q_code, m_max])
    (h_sys_supp : ∀ idx, sys.support idx = staticCSSCheckSupport D_field idx)
    {γ : WorldlineDysonPolymer L q_code}
    (hγ : IsValidWorldlinePolymer D_field sys C_RCA R_cut γ)
    {ξ : WorldlineJumpMonomer L q_code} (hξ : ξ ∈ γ.1) :
    ξ ∈ validJumpMonomersAtCube D_field sys ξ.1 := by
  rcases hγ.2.1 ξ hξ with ⟨h_supp, _, h_can⟩
  let S : Finset (IdxCSS[L, q_code, m_max]) :=
    (cubeIntersectingChecks sys ξ.1.2).filter (fun c => staticCSSPauliFlip D_field ξ.2.1 ξ.2.2 c = true)
  have hS_pow : S ∈ (cubeIntersectingChecks sys ξ.1.2).powerset :=
    Finset.mem_powerset.mpr (Finset.filter_subset _ _)
  have h_dec : (fun c => decide (c ∈ S)) = staticCSSPauliFlip D_field ξ.2.1 ξ.2.2 := by
    ext c
    dsimp [S]
    by_cases hc : c ∈ cubeIntersectingChecks sys ξ.1.2
    · simp [hc]
    · have h_f : staticCSSPauliFlip D_field ξ.2.1 ξ.2.2 c = false := by
        cases hb : staticCSSPauliFlip D_field ξ.2.1 ξ.2.2 c
        · rfl
        · exact False.elim (hc (staticCSSPauliFlip_mem_cubeIntersectingChecks
            D_field sys h_sys_supp ξ.1.2 ξ.2.1 ξ.2.2 h_supp c hb))
      simp [hc, h_f]
  exact Finset.mem_image.mpr ⟨S, hS_pow, Prod.ext rfl (by rw [h_dec, ← h_can])⟩

lemma worldlinePolymerWeight_abs_le_prod
    {L q_code r_0 m_max w_0 R_cut : ℕ} [NeZero L]
    {C_RCA c_wl β J : ℝ} {f : ℕ → ℝ}
    (hR_cut : 1 ≤ R_cut) (hβ : 0 ≤ β) (hJ : 0 ≤ J) (hf_nn : ∀ r, 0 ≤ f r)
    (D_field : Box3D L → LocalCSSDescriptor q_code r_0 m_max)
    (sys : SysCSS[L, q_code, m_max])
    (h_sys_checks : ∀ idx, sys.checkProj idx = staticCSSCheckProj D_field idx ∧
      sys.support idx = staticCSSCheckSupport D_field idx ∧ sys.weight idx = 1)
    (h_geom : sys.IsGeometricallyLocal r_0 w_0)
    (hc_wl_cal : (kpCollarMaxCheckCard R_cut r_0 w_0 C_RCA : ℝ) ≤ c_wl)
    (V : QuasiLocalPerturbation 3 L (SiteCSS[L, q_code]))
    (hV_norm : ∀ r ∈ Finset.Icc 1 (min R_cut L), ∀ A ∈ boxCubes 3 L r, ‖V.term r A‖ ≤ J * f r)
    (d_loc : ℕ → Finset (Box3D L) → (IdxCSS[L, q_code, m_max] → Bool) → ℝ)
    (hd_scale : ∀ r ∈ Finset.Icc 1 (min R_cut L), ∀ A ∈ boxCubes 3 L r,
      ∀ σ, |d_loc r A σ| ≤ 2 * (J * f r))
    (ν : PauliBitstringPair L q_code)
    (γ : WorldlineDysonPolymer L q_code)
    (hγ : IsValidWorldlinePolymer D_field sys C_RCA R_cut γ)
    (σ : IdxCSS[L, q_code, m_max] → Bool) :
    |worldlinePolymerWeight D_field sys C_RCA β V d_loc ν γ σ| ≤
      ((γ.1.length.factorial : ℝ)⁻¹) *
        (γ.1.map (fun ξ => 2 * β * J * f ξ.1.1 *
          Real.exp ((1 / 27 : ℝ) * c_wl * β * ((ξ.1.1 : ℝ) ^ 3)))).prod *
        ∏ ϑ ∈ γ.2, 4 * β * J * f ϑ.1 * Real.exp (4 * β * J * f ϑ.1) := by
  let σ₀ := restrictSyndromeToCollar (worldlinePolymerNativeCollar sys C_RCA γ) σ
  rw [worldlinePolymerWeight_abs, worldlinePolymerMicroWeight_abs]
  have h_amp := worldlinePolymerLoopAmplitude_abs_le_prod_two_mul_J_mul_f D_field sys V f hV_norm γ hγ σ₀
  let B := (γ.1.map (fun ξ => Real.exp ((1 / 27 : ℝ) * c_wl * β * ((ξ.1.1 : ℝ) ^ 3)))).prod *
    ∏ ϑ ∈ γ.2, 4 * β * J * f ϑ.1 * Real.exp (4 * β * J * f ϑ.1)
  have hB_nn : 0 ≤ B := by
    dsimp [B]
    refine mul_nonneg ?_ (Finset.prod_nonneg fun ϑ _ => ?_)
    · exact List.prod_nonneg (by intro y hy; rcases List.mem_map.mp hy with ⟨_, _, rfl⟩; exact Real.exp_nonneg _)
    · have := hf_nn ϑ.1; positivity
  have h_int := abs_integral_kpOrderedDysonSimplex_le hβ hB_nn
    (fun τ => Real.exp (-worldlineBareAction D_field sys γ.1 σ₀ β τ) *
      ∏ ϑ ∈ γ.2, worldlineMayerBondFactor D_field γ.1 d_loc σ₀ β ϑ τ)
    (fun τ _ => abs_exp_neg_worldlineBareAction_mul_prod_mayer_le_sum hR_cut hβ hJ hf_nn
      D_field sys h_sys_checks h_geom hc_wl_cal d_loc hd_scale γ hγ σ₀ τ)
  have h_amp_nn : 0 ≤ (γ.1.map (fun ξ => 2 * (J * f ξ.1.1))).prod :=
    List.prod_nonneg (by intro y hy; rcases List.mem_map.mp hy with ⟨ξ, _, rfl⟩; have := hf_nn ξ.1.1; positivity)
  calc |worldlinePolymerLoopAmplitude D_field sys C_RCA V γ σ₀| *
        |∫ τ : Fin γ.1.length → ℝ,
          if InOrderedDysonSimplex β τ then
            Real.exp (-worldlineBareAction D_field sys γ.1 σ₀ β τ) *
              ∏ ϑ ∈ γ.2, worldlineMayerBondFactor D_field γ.1 d_loc σ₀ β ϑ τ
          else 0|
    _ ≤ (γ.1.map (fun ξ => 2 * (J * f ξ.1.1))).prod * (((β ^ γ.1.length) / (γ.1.length.factorial : ℝ)) * B) :=
        mul_le_mul h_amp h_int (abs_nonneg _) h_amp_nn
    _ = ((γ.1.length.factorial : ℝ)⁻¹) *
          ((β ^ γ.1.length * (γ.1.map (fun ξ => 2 * (J * f ξ.1.1))).prod) *
            (γ.1.map (fun ξ => Real.exp ((1 / 27 : ℝ) * c_wl * β * ((ξ.1.1 : ℝ) ^ 3)))).prod) *
          ∏ ϑ ∈ γ.2, 4 * β * J * f ϑ.1 * Real.exp (4 * β * J * f ϑ.1) := by
        dsimp [B]; ring
    _ = ((γ.1.length.factorial : ℝ)⁻¹) *
          (γ.1.map (fun ξ => 2 * β * J * f ξ.1.1 *
            Real.exp ((1 / 27 : ℝ) * c_wl * β * ((ξ.1.1 : ℝ) ^ 3)))).prod *
          ∏ ϑ ∈ γ.2, 4 * β * J * f ϑ.1 * Real.exp (4 * β * J * f ϑ.1) := by
        rw [← list_prod_const_mul γ.1 β (fun ξ => 2 * (J * f ξ.1.1)),
          list_prod_mul_distrib]
        congr 2
        refine congrArg List.prod (List.map_congr_left fun ξ _ => by ring)

lemma validJumpMonomersAtCube_card_mul_le_kpMonomerWeight
    {L q_code r_0 m_max w_0 R_cut : ℕ} [NeZero L]
    {C_RCA c_wl β J : ℝ} {f : ℕ → ℝ}
    (hR_cut : 1 ≤ R_cut) (hβ : 0 ≤ β) (hJ : 0 ≤ J) (hf_nn : ∀ r, 0 ≤ f r)
    (D_field : Box3D L → LocalCSSDescriptor q_code r_0 m_max)
    (sys : SysCSS[L, q_code, m_max])
    (h_geom : sys.IsGeometricallyLocal r_0 w_0)
    (hc_wl_cal : (kpCollarMaxCheckCard R_cut r_0 w_0 C_RCA : ℝ) ≤ c_wl)
    {p : ℕ × Finset (Box3D L)} (hp : p ∈ worldlineScaleCubeFinset L R_cut) :
    ((validJumpMonomersAtCube D_field sys p).card : ℝ) *
      (2 * β * J * f p.1 * Real.exp ((1 / 27 : ℝ) * c_wl * β * ((p.1 : ℝ) ^ 3))) ≤
      kpMonomerWeight c_wl β J f p :=
  two_pow_cubeIntersectingChecks_mul_le_kpMonomerWeight hR_cut hβ hJ hf_nn sys h_geom hc_wl_cal hp
    (card_validJumpMonomersAtCube_le D_field sys p)

private lemma boolToZMod2_foldr_syndromeXor_aux {α : Type*} {L q_code m_max : ℕ}
    (δ : α → IdxCSS[L, q_code, m_max] → Bool) (l : List α)
    (σ : IdxCSS[L, q_code, m_max] → Bool) (c : IdxCSS[L, q_code, m_max]) :
    boolToZMod2 ((l.foldr (fun x acc => syndromeXor (δ x) acc) σ) c) =
      (l.map (fun x => boolToZMod2 (δ x c))).sum + boolToZMod2 (σ c) := by
  have h_bne : ∀ b₁ b₂ : Bool, boolToZMod2 (bne b₁ b₂) = boolToZMod2 b₁ + boolToZMod2 b₂ := by
    intro b₁ b₂; cases b₁ <;> cases b₂ <;> rfl
  induction l with
  | nil => simp
  | cons hd tl ih =>
    rw [List.foldr_cons, List.map_cons, List.sum_cons]
    change boolToZMod2 (bne (δ hd c) ((tl.foldr (fun x acc => syndromeXor (δ x) acc) σ) c)) = _
    rw [h_bne, ih, add_assoc]

private lemma list_sum_map_finRange_filter_aux {n : ℕ} {M : Type*} [AddCommMonoid M]
    (p : Fin n → Bool) (f : Fin n → M) :
    (((List.finRange n).filter p).map f).sum = ∑ j : Fin n, if p j then f j else 0 := by
  have h_list : ∀ l : List (Fin n),
      ((l.filter p).map f).sum = (l.map (fun j => if p j then f j else 0)).sum := by
    intro l
    induction l with
    | nil => simp
    | cons hd tl ih =>
      rw [List.filter_cons, List.map_cons, List.sum_cons]
      split_ifs with h
      · rw [List.map_cons, List.sum_cons, ih]
      · rw [zero_add, ih]
  rw [h_list]
  exact (Fin.sum_univ_def (fun j => if p j then f j else 0)).symm

lemma integral_inOrderedDysonSimplex_reverse_polymer_eq
    {L q_code r_0 m_max R_cut : ℕ} [NeZero L]
    {C_RCA β : ℝ} (hβ_nn : 0 ≤ β)
    (D_field : Box3D L → LocalCSSDescriptor q_code r_0 m_max)
    (sys : SysCSS[L, q_code, m_max])
    (d_loc : ℕ → Finset (Box3D L) → (IdxCSS[L, q_code, m_max] → Bool) → ℝ)
    (γ : WorldlineDysonPolymer L q_code)
    (hγ : IsValidWorldlinePolymer D_field sys C_RCA R_cut γ)
    (σ₀ : IdxCSS[L, q_code, m_max] → Bool) :
    (∫ τ : Fin γ.1.reverse.length → ℝ,
      if InOrderedDysonSimplex β τ then
        Real.exp (-worldlineBareAction D_field sys γ.1.reverse σ₀ β τ) *
          ∏ ϑ ∈ γ.2, worldlineMayerBondFactor D_field γ.1.reverse d_loc σ₀ β ϑ τ
      else 0) =
    ∫ τ : Fin γ.1.length → ℝ,
      if InOrderedDysonSimplex β τ then
        Real.exp (-worldlineBareAction D_field sys γ.1 σ₀ β τ) *
          ∏ ϑ ∈ γ.2, worldlineMayerBondFactor D_field γ.1 d_loc σ₀ β ϑ τ
      else 0 := by
  let m := γ.1.length
  have h_len : γ.1.reverse.length = m := List.length_reverse
  let e_len : (Fin m → ℝ) ≃ᵐ (Fin γ.1.reverse.length → ℝ) :=
    MeasurableEquiv.piCongrLeft (fun _ => ℝ) (finCongr h_len.symm)
  have mp_len : MeasureTheory.MeasurePreserving e_len
      MeasureTheory.volume MeasureTheory.volume :=
    MeasureTheory.measurePreserving_piCongrLeft (fun _ => MeasureTheory.volume) (finCongr h_len.symm)
  have h_elen_app : ∀ τ : Fin m → ℝ, e_len τ = fun j => τ (Fin.cast h_len j) := by
    intro τ; funext j
    exact MeasurableEquiv.piCongrLeft_apply_apply
      (β := fun _ : Fin γ.1.reverse.length => ℝ) (finCongr h_len.symm) τ (Fin.cast h_len j)
  rw [← mp_len.integral_comp']
  let e_rev : (Fin m → ℝ) ≃ᵐ (Fin m → ℝ) :=
    MeasurableEquiv.piCongrLeft (fun _ => ℝ) Fin.revPerm
  have mp_rev : MeasureTheory.MeasurePreserving e_rev
      MeasureTheory.volume MeasureTheory.volume :=
    MeasureTheory.measurePreserving_piCongrLeft (fun _ => MeasureTheory.volume) Fin.revPerm
  have h_erev_app : ∀ τ : Fin m → ℝ, e_rev τ = fun i => τ i.rev := by
    intro τ; funext i
    have h1 := MeasurableEquiv.piCongrLeft_apply_apply
      (β := fun _ : Fin m => ℝ) Fin.revPerm τ i.rev
    simpa using h1
  let e_sub : (Fin m → ℝ) ≃ᵐ (Fin m → ℝ) :=
    { toFun := fun τ i => β + τ i * (-1 : ℝ)
      invFun := fun τ i => β + τ i * (-1 : ℝ)
      left_inv := fun τ => by ext i; ring
      right_inv := fun τ => by ext i; ring
      measurable_toFun := measurable_pi_iff.mpr fun i =>
        measurable_const.add ((measurable_pi_apply i).mul_const (-1))
      measurable_invFun := measurable_pi_iff.mpr fun i =>
        measurable_const.add ((measurable_pi_apply i).mul_const (-1)) }
  have mp_neg : MeasureTheory.MeasurePreserving (fun x : ℝ => x * (-1 : ℝ))
      MeasureTheory.volume MeasureTheory.volume :=
    ⟨measurable_id.mul_const (-1), by
      have h := Real.smul_map_volume_mul_right (by norm_num : (-1 : ℝ) ≠ 0)
      simpa using h⟩
  have mp_sub : MeasureTheory.MeasurePreserving e_sub
      MeasureTheory.volume MeasureTheory.volume :=
    MeasureTheory.volume_preserving_pi (fun _ : Fin m =>
      (MeasureTheory.measurePreserving_add_left MeasureTheory.volume β).comp mp_neg)
  let e_tot := e_rev.trans e_sub
  have mp_tot : MeasureTheory.MeasurePreserving e_tot
      MeasureTheory.volume MeasureTheory.volume := mp_sub.comp mp_rev
  have h_etot_app : ∀ τ : Fin m → ℝ, e_tot τ = fun i => β - τ i.rev := by
    intro τ; funext i
    change β + (e_rev τ) i * (-1 : ℝ) = β - τ i.rev
    rw [h_erev_app]; ring
  rw [← mp_tot.integral_comp']
  refine congrArg (MeasureTheory.integral MeasureTheory.volume) (funext fun τ => ?_)
  (try dsimp only)
  let τ_rev : Fin γ.1.reverse.length → ℝ := fun j => β - τ (Fin.cast h_len j).rev
  have h_app : e_len (e_tot τ) = τ_rev := by
    rw [h_elen_app, h_etot_app]
  rw [h_app]
  have h_simp_iff : InOrderedDysonSimplex β τ_rev ↔ InOrderedDysonSimplex β τ := by
    constructor
    · rintro ⟨h_b, h_sm⟩
      refine ⟨fun i => ?_, fun i₁ i₂ h_lt => ?_⟩
      · have hi := h_b (Fin.cast h_len.symm i.rev)
        dsimp [τ_rev] at hi
        rw [Fin.rev_rev] at hi
        exact ⟨by linarith [hi.2], by linarith [hi.1]⟩
      · have h_rev_lt : Fin.cast h_len.symm i₂.rev < Fin.cast h_len.symm i₁.rev :=
          Fin.rev_lt_rev.mpr h_lt
        have h_lt' := h_sm h_rev_lt
        dsimp [τ_rev] at h_lt'
        rw [Fin.rev_rev, Fin.rev_rev] at h_lt'
        linarith
    · rintro ⟨h_b, h_sm⟩
      refine ⟨fun j => ?_, fun j₁ j₂ h_lt => ?_⟩
      · have hj := h_b (Fin.cast h_len j).rev
        dsimp [τ_rev]
        exact ⟨by linarith [hj.2], by linarith [hj.1]⟩
      · have h_rev_lt : (Fin.cast h_len j₂).rev < (Fin.cast h_len j₁).rev :=
          Fin.rev_lt_rev.mpr h_lt
        have h_lt' := h_sm h_rev_lt
        dsimp [τ_rev]
        linarith
  have h_traj_eq : ∀ t : ℝ, (∀ i : Fin m, t ≠ τ i) →
      worldlineTrajectorySyndrome D_field γ.1.reverse σ₀ τ_rev (β - t) =
        worldlineTrajectorySyndrome D_field γ.1 σ₀ τ t := by
    intro t ht_ne
    have h_inj : Function.Injective boolToZMod2 := by
      intro b₁ b₂; cases b₁ <;> cases b₂ <;> decide
    ext c
    apply h_inj
    unfold worldlineTrajectorySyndrome
    rw [boolToZMod2_foldr_syndromeXor_aux, list_sum_map_finRange_filter_aux,
      boolToZMod2_foldr_syndromeXor_aux, list_sum_map_finRange_filter_aux]
    congr 1
    let e_cast : Fin γ.1.reverse.length ≃ Fin m := finCongr h_len
    rw [← Equiv.sum_comp e_cast.symm, ← Equiv.sum_comp Fin.revPerm]
    have h_sum_zero :
        ∑ i : Fin m, boolToZMod2 (staticCSSPauliFlip D_field (γ.1.get i).2.1 (γ.1.get i).2.2 c) = 0 := by
      have h_closed := hγ.2.2.1.2
      have h_loop_eq : staticCSSPauliFlip D_field (worldlinePolymerLoopX (γ.1, ∅))
          (worldlinePolymerLoopZ (γ.1, ∅)) = (fun _ => false) := h_closed
      rw [← worldlineJumpListFlip_eq_staticCSSPauliFlip_loop D_field (γ.1, ∅)] at h_loop_eq
      have hc0 : boolToZMod2 (worldlineJumpListFlip D_field γ.1 c) = 0 := by
        rw [congrFun h_loop_eq c]; rfl
      unfold worldlineJumpListFlip at hc0
      rw [boolToZMod2_foldr_syndromeXor_aux] at hc0
      change (γ.1.map (fun x => boolToZMod2 (staticCSSPauliFlip D_field x.2.1 x.2.2 c))).sum + 0 = 0 at hc0
      rw [add_zero] at hc0
      rw [Fin.sum_univ_def]
      rw [← List.map_get_finRange γ.1, List.map_map] at hc0
      exact hc0
    have h_term_sum : ∀ i : Fin m,
        (if decide (τ_rev (e_cast.symm (Fin.revPerm i)) ≤ β - t) then
          boolToZMod2 (staticCSSPauliFlip D_field
            (γ.1.reverse.get (e_cast.symm (Fin.revPerm i))).2.1
            (γ.1.reverse.get (e_cast.symm (Fin.revPerm i))).2.2 c)
        else 0) +
        (if decide (τ i ≤ t) then
          boolToZMod2 (staticCSSPauliFlip D_field (γ.1.get i).2.1 (γ.1.get i).2.2 c)
        else 0) =
        boolToZMod2 (staticCSSPauliFlip D_field (γ.1.get i).2.1 (γ.1.get i).2.2 c) := by
      intro i
      have h_get_rev : γ.1.reverse.get (e_cast.symm (Fin.revPerm i)) = γ.1.get i := by
        change γ.1.reverse[i.rev.1]'(by rw [h_len]; exact i.rev.2) = γ.1[i.1]
        rw [List.getElem_reverse]
        congr 1
        rw [Fin.val_rev]
        omega
      rw [h_get_rev]
      have h_tau_rev : τ_rev (e_cast.symm (Fin.revPerm i)) = β - τ i := by
        dsimp [τ_rev, e_cast]
        congr 2
        ext
        simp [Fin.revPerm]
      rw [h_tau_rev]
      rcases lt_or_gt_of_ne (ht_ne i) with h_lt | h_gt
      · have h1 : decide (β - τ i ≤ β - t) = true := decide_eq_true (by linarith)
        have h2 : decide (τ i ≤ t) = false := decide_eq_false (by linarith)
        rw [h1, h2]; simp
      · have h1 : decide (β - τ i ≤ β - t) = false := decide_eq_false (by linarith)
        have h2 : decide (τ i ≤ t) = true := decide_eq_true (by linarith)
        rw [h1, h2]; simp
    have h_add_eq :
        (∑ i : Fin m,
          if decide (τ_rev (e_cast.symm (Fin.revPerm i)) ≤ β - t) then
            boolToZMod2 (staticCSSPauliFlip D_field
              (γ.1.reverse.get (e_cast.symm (Fin.revPerm i))).2.1
              (γ.1.reverse.get (e_cast.symm (Fin.revPerm i))).2.2 c)
          else 0) +
        (∑ i : Fin m,
          if decide (τ i ≤ t) then
            boolToZMod2 (staticCSSPauliFlip D_field (γ.1.get i).2.1 (γ.1.get i).2.2 c)
          else 0) = 0 := by
      rw [← Finset.sum_add_distrib, Finset.sum_congr rfl (fun i _ => h_term_sum i), h_sum_zero]
    exact CharTwo.add_eq_zero.mp h_add_eq
  have h_int_time : ∀ G : (IdxCSS[L, q_code, m_max] → Bool) → ℝ,
      (∫ t in Set.Icc 0 β, G (worldlineTrajectorySyndrome D_field γ.1.reverse σ₀ τ_rev t)) =
        ∫ t in Set.Icc 0 β, G (worldlineTrajectorySyndrome D_field γ.1 σ₀ τ t) := by
    intro G
    rw [MeasureTheory.integral_Icc_eq_integral_Ioc, MeasureTheory.integral_Icc_eq_integral_Ioc,
      ← intervalIntegral.integral_of_le hβ_nn, ← intervalIntegral.integral_of_le hβ_nn]
    have h_sub := intervalIntegral.integral_comp_sub_left
      (a := 0) (b := β) (fun t => G (worldlineTrajectorySyndrome D_field γ.1.reverse σ₀ τ_rev t)) β
    rw [sub_self, sub_zero] at h_sub
    rw [← h_sub, intervalIntegral.integral_of_le hβ_nn, intervalIntegral.integral_of_le hβ_nn]
    have h_ae : ∀ᵐ t : ℝ ∂MeasureTheory.volume, ∀ i : Fin m, t ≠ τ i := by
      rw [MeasureTheory.ae_iff]
      have h_un : {t : ℝ | ¬∀ i : Fin m, t ≠ τ i} = ⋃ i : Fin m, ({τ i} : Set ℝ) := by
        ext t; simp [eq_comm]
      rw [h_un]
      exact MeasureTheory.measure_iUnion_null (fun i => by simp)
    refine MeasureTheory.integral_congr_ae (MeasureTheory.ae_restrict_of_ae (h_ae.mono fun t ht => ?_))
    (try dsimp only)
    rw [h_traj_eq t ht]
  by_cases h_s : InOrderedDysonSimplex β τ
  · rw [if_pos (h_simp_iff.mpr h_s), if_pos h_s]
    have h_bare : worldlineBareAction D_field sys γ.1.reverse σ₀ β τ_rev =
        worldlineBareAction D_field sys γ.1 σ₀ β τ :=
      h_int_time (fun η => sys.syndromeEnergy η - sys.syndromeEnergy σ₀)
    have h_mayer : ∀ ϑ ∈ γ.2,
        worldlineMayerBondFactor D_field γ.1.reverse d_loc σ₀ β ϑ τ_rev =
          worldlineMayerBondFactor D_field γ.1 d_loc σ₀ β ϑ τ := by
      intro ϑ _
      unfold worldlineMayerBondFactor
      rw [h_int_time (fun η => d_loc ϑ.1 ϑ.2 η - d_loc ϑ.1 ϑ.2 σ₀)]
    rw [h_bare, Finset.prod_congr rfl h_mayer]
  · rw [if_neg (mt h_simp_iff.mp h_s), if_neg h_s]

lemma list_ofFn_prod_avg_eq_sum_bool_tuple
    {L q_code : ℕ} (p : ℕ) (f₀ f₁ : Fin p → ℬ_CSS[L, q_code]) :
    (List.ofFn (fun i : Fin p => (1 / 2 : ℂ) • (f₀ i + f₁ i))).prod =
      ∑ b : Fin p → Bool,
        ((((2 : ℝ) ^ p)⁻¹ : ℝ) : ℂ) • (List.ofFn (fun i : Fin p => if b i then f₁ i else f₀ i)).prod := by
  induction p with
  | zero =>
    have h_univ : (Finset.univ : Finset (Fin 0 → Bool)) = {Fin.elim0} := by
      ext b
      simp only [Finset.mem_univ, Finset.mem_singleton, true_iff]
      funext i; exact Fin.elim0 i
    rw [h_univ, Finset.sum_singleton]
    simp
  | succ n ih =>
    rw [List.ofFn_succ, List.prod_cons, ih (fun i => f₀ i.succ) (fun i => f₁ i.succ),
      Finset.mul_sum, ← (Fin.consEquiv (fun _ : Fin (n + 1) => Bool)).sum_comp]
    have h_bool : (Finset.univ : Finset Bool) = {false, true} := by decide
    rw [Fintype.sum_prod_type, h_bool, Finset.sum_pair (by decide : false ≠ true), ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun b_tl _ => ?_
    dsimp [Fin.consEquiv]
    rw [List.ofFn_succ, List.ofFn_succ, List.prod_cons, List.prod_cons]
    simp only [Fin.cons_zero, Fin.cons_succ]
    rw [clm_smul_mul, clm_mul_smul, add_mul, smul_add, smul_add, smul_smul, smul_smul, pow_succ']
    congr 2 <;> { push_cast; ring }

def flipCluster {L q_code : ℕ} {p : ℕ} (b : Fin p → Bool)
    (K : WorldlineUrsellCluster L q_code) : WorldlineUrsellCluster L q_code :=
  List.ofFn (fun i : Fin p =>
    if h : i.1 < K.length then
      if b i then ((K.get ⟨i.1, h⟩).1.reverse, (K.get ⟨i.1, h⟩).2) else K.get ⟨i.1, h⟩
    else ([], ∅))

lemma flipCluster_invariants
    {L q_code r_0 m_max R_cut p : ℕ} [NeZero L] {C_RCA β : ℝ} (hβ_nn : 0 ≤ β)
    (D_field : Box3D L → LocalCSSDescriptor q_code r_0 m_max)
    (sys : SysCSS[L, q_code, m_max])
    (d_loc : ℕ → Finset (Box3D L) → (IdxCSS[L, q_code, m_max] → Bool) → ℝ)
    (σ₀ : IdxCSS[L, q_code, m_max] → Bool)
    (b : Fin p → Bool) (K : WorldlineUrsellCluster L q_code) (h_len : K.length = p) :
    (flipCluster b K).length = p ∧
    flipCluster b (flipCluster b K) = K ∧
    ((flipCluster b K).map (fun γ => γ.1.length)).sum = (K.map (fun γ => γ.1.length)).sum ∧
    ((flipCluster b K).map (fun γ => (worldlinePolymerLoopX γ, worldlinePolymerLoopZ γ))).sum =
      (K.map (fun γ => (worldlinePolymerLoopX γ, worldlinePolymerLoopZ γ))).sum ∧
    ((∀ γ ∈ K, IsValidWorldlinePolymer D_field sys C_RCA R_cut γ) →
      (∀ γ ∈ flipCluster b K, IsValidWorldlinePolymer D_field sys C_RCA R_cut γ) ∧
      ((flipCluster b K).Pairwise (fun γ₁ γ₂ => ¬ArePolymersIncompatible sys C_RCA γ₁ γ₂) ↔
        K.Pairwise (fun γ₁ γ₂ => ¬ArePolymersIncompatible sys C_RCA γ₁ γ₂)) ∧
      ((flipCluster b K).map (fun γ =>
        ((-1 : ℝ) ^ γ.1.length) *
          ∫ τ : Fin γ.1.length → ℝ,
            if InOrderedDysonSimplex β τ then
              Real.exp (-worldlineBareAction D_field sys γ.1 σ₀ β τ) *
                ∏ ϑ ∈ γ.2, worldlineMayerBondFactor D_field γ.1 d_loc σ₀ β ϑ τ
            else 0)).prod =
      (K.map (fun γ =>
        ((-1 : ℝ) ^ γ.1.length) *
          ∫ τ : Fin γ.1.length → ℝ,
            if InOrderedDysonSimplex β τ then
              Real.exp (-worldlineBareAction D_field sys γ.1 σ₀ β τ) *
                ∏ ϑ ∈ γ.2, worldlineMayerBondFactor D_field γ.1 d_loc σ₀ β ϑ τ
            else 0)).prod) := by
  have h_flen : (flipCluster b K).length = p := List.length_ofFn
  have h_get_gen : ∀ (K' : WorldlineUrsellCluster L q_code) (h_len' : K'.length = p) (i : Fin p),
      (flipCluster b K')[i.1]'(by simp [flipCluster]) =
        if b i then
          ((K'[i.1]'(by rw [h_len']; exact i.2)).1.reverse, (K'[i.1]'(by rw [h_len']; exact i.2)).2)
        else K'[i.1]'(by rw [h_len']; exact i.2) := by
    intro K' h_len' i
    have h_cond : i.1 < K'.length := by rw [h_len']; exact i.2
    unfold flipCluster
    rw [List.getElem_ofFn, dif_pos h_cond]
    rfl
  have h_get : ∀ i : Fin p,
      (flipCluster b K)[i.1]'(by rw [h_flen]; exact i.2) =
        if b i then
          ((K[i.1]'(by rw [h_len]; exact i.2)).1.reverse, (K[i.1]'(by rw [h_len]; exact i.2)).2)
        else K[i.1]'(by rw [h_len]; exact i.2) :=
    h_get_gen K h_len
  have h_inv : flipCluster b (flipCluster b K) = K := by
    refine List.ext_getElem (by simp [flipCluster, h_len]) fun i h1 h2 => ?_
    let idx : Fin p := ⟨i, by rw [← h_len]; exact h2⟩
    change (flipCluster b (flipCluster b K))[idx.1]'(by simp [flipCluster]) =
      K[idx.1]'(by rw [h_len]; exact idx.2)
    rw [h_get_gen (flipCluster b K) h_flen idx, h_get idx]
    cases b idx <;> simp [List.reverse_reverse]
  have h_map_eq : ∀ {α : Type} (g : WorldlineDysonPolymer L q_code → α),
      (∀ γ ∈ K, g (γ.1.reverse, γ.2) = g γ) →
      (flipCluster b K).map g = K.map g := by
    intro α g hg
    refine List.ext_getElem (by simp [h_flen, h_len]) fun i h1 h2 => ?_
    let idx : Fin p := ⟨i, by simp [h_len] at h2; exact h2⟩
    rw [List.getElem_map, List.getElem_map]
    change g ((flipCluster b K)[idx.1]'(by rw [h_flen]; exact idx.2)) =
      g (K[idx.1]'(by rw [h_len]; exact idx.2))
    rw [h_get idx]
    cases b idx
    · rfl
    · exact hg _ (List.getElem_mem _)
  have h_sum_len : ((flipCluster b K).map (fun γ => γ.1.length)).sum =
      (K.map (fun γ => γ.1.length)).sum :=
    congrArg List.sum (h_map_eq (fun γ => γ.1.length) (fun γ _ => List.length_reverse))
  have h_sum_loop :
      ((flipCluster b K).map (fun γ => (worldlinePolymerLoopX γ, worldlinePolymerLoopZ γ))).sum =
        (K.map (fun γ => (worldlinePolymerLoopX γ, worldlinePolymerLoopZ γ))).sum :=
    congrArg List.sum (h_map_eq (fun γ => (worldlinePolymerLoopX γ, worldlinePolymerLoopZ γ))
      (fun γ _ => by
        rcases worldlinePolymer_reverse_invariants (C_RCA := C_RCA) (R_cut := R_cut) D_field sys γ with
          ⟨_, _, hX, hZ, _⟩
        exact Prod.ext hX hZ))
  refine ⟨h_flen, h_inv, h_sum_len, h_sum_loop, fun hK_val => ?_⟩
  have h_fval : ∀ γ ∈ flipCluster b K, IsValidWorldlinePolymer D_field sys C_RCA R_cut γ := by
    intro γ hγ
    rcases List.mem_iff_getElem.mp hγ with ⟨i, hi, rfl⟩
    let idx : Fin p := ⟨i, by rw [← h_flen]; exact hi⟩
    change IsValidWorldlinePolymer D_field sys C_RCA R_cut
      ((flipCluster b K)[idx.1]'(by rw [h_flen]; exact idx.2))
    rw [h_get idx]
    have h_k : IsValidWorldlinePolymer D_field sys C_RCA R_cut
        (K[idx.1]'(by rw [h_len]; exact idx.2)) :=
      hK_val _ (List.getElem_mem _)
    cases b idx
    · exact h_k
    · exact (worldlinePolymer_reverse_invariants D_field sys _).2.2.2.2.mpr h_k
  have h_col_eq :
      (flipCluster b K).map (worldlinePolymerNativeCollar sys C_RCA) =
        K.map (worldlinePolymerNativeCollar sys C_RCA) :=
    h_map_eq _ (fun γ _ =>
      (worldlinePolymer_reverse_invariants (C_RCA := C_RCA) (R_cut := R_cut) D_field sys γ).2.1)
  have h_pw_iff :
      (flipCluster b K).Pairwise (fun γ₁ γ₂ => ¬ArePolymersIncompatible sys C_RCA γ₁ γ₂) ↔
        K.Pairwise (fun γ₁ γ₂ => ¬ArePolymersIncompatible sys C_RCA γ₁ γ₂) := by
    have h_map : ∀ L' : WorldlineUrsellCluster L q_code,
        L'.Pairwise (fun γ₁ γ₂ => ¬ArePolymersIncompatible sys C_RCA γ₁ γ₂) ↔
          (L'.map (worldlinePolymerNativeCollar sys C_RCA)).Pairwise
            (fun C₁ C₂ => ¬¬Disjoint C₁ C₂) :=
      fun _ => (List.pairwise_map (f := worldlinePolymerNativeCollar sys C_RCA)
        (R := fun C₁ C₂ => ¬¬Disjoint C₁ C₂)).symm
    rw [h_map, h_map, h_col_eq]
  refine ⟨h_fval, h_pw_iff, ?_⟩
  exact congrArg List.prod (h_map_eq _ (fun γ hγ => by
    (try dsimp only)
    rw [integral_inOrderedDysonSimplex_reverse_polymer_eq hβ_nn D_field sys d_loc γ (hK_val γ hγ) σ₀,
      List.length_reverse]))

local instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

private lemma sum_checkPauliZ_and_X_mul_eq_zero_of_syndromeClosed
    {L q_code r_0 m_max : ℕ}
    (D_field : Box3D L → LocalCSSDescriptor q_code r_0 m_max)
    {p : PauliBitstringPair L q_code}
    (hp : p ∈ syndromeClosedPauliFinset D_field)
    (c : IdxCSS[L, q_code, m_max]) :
    (∑ slot : BoxSlot3D L q_code, p.1 slot * staticCSSCheckPauliX D_field c slot) = 0 ∧
    (∑ slot : BoxSlot3D L q_code, staticCSSCheckPauliZ D_field c slot * p.2 slot) = 0 := by
  have h_flip : staticCSSPauliFlip D_field p.1 p.2 c = false :=
    congr_fun (Finset.mem_filter.mp hp).2 c
  have h_sum := boolToZMod2_staticCSSPauliFlip_eq_sum_checkPauli D_field p c
  rw [h_flip] at h_sum
  change (0 : ZMod 2) = _ at h_sum
  rw [Finset.sum_add_distrib] at h_sum
  rcases c with ⟨v, s⟩ | ⟨v, idx⟩ | ⟨v, idx⟩
  · have hX : (∑ slot : BoxSlot3D L q_code, p.1 slot * staticCSSCheckPauliX D_field (Sum.inl (v, s)) slot) = 0 := by
      dsimp [staticCSSCheckPauliX]; simp
    exact ⟨hX, by rw [hX, zero_add] at h_sum; exact h_sum.symm⟩
  · have hZ : (∑ slot : BoxSlot3D L q_code,
        staticCSSCheckPauliZ D_field (Sum.inr (Sum.inl (v, idx))) slot * p.2 slot) = 0 := by
      dsimp [staticCSSCheckPauliZ]; simp
    exact ⟨by rw [hZ, add_zero] at h_sum; exact h_sum.symm, hZ⟩
  · have hX : (∑ slot : BoxSlot3D L q_code,
        p.1 slot * staticCSSCheckPauliX D_field (Sum.inr (Sum.inr (v, idx))) slot) = 0 := by
      dsimp [staticCSSCheckPauliX]; simp
    exact ⟨hX, by rw [hX, zero_add] at h_sum; exact h_sum.symm⟩

private lemma sum_stabilizerPauliSubmodule_mul_eq_zero_of_syndromeClosed
    {L q_code r_0 m_max : ℕ}
    (D_field : Box3D L → LocalCSSDescriptor q_code r_0 m_max)
    {p : PauliBitstringPair L q_code}
    (hp : p ∈ syndromeClosedPauliFinset D_field)
    {q : PauliBitstringPair L q_code}
    (hq : q ∈ stabilizerPauliSubmodule D_field) :
    (∑ slot : BoxSlot3D L q_code, p.1 slot * q.2 slot) = 0 ∧
    (∑ slot : BoxSlot3D L q_code, q.1 slot * p.2 slot) = 0 := by
  refine Submodule.span_induction
    (p := fun q _ => (∑ slot : BoxSlot3D L q_code, p.1 slot * q.2 slot) = 0 ∧
      (∑ slot : BoxSlot3D L q_code, q.1 slot * p.2 slot) = 0)
    ?_ (by simp) ?_ ?_ hq
  · rintro _ ⟨c, rfl⟩
    exact sum_checkPauliZ_and_X_mul_eq_zero_of_syndromeClosed D_field hp c
  · intro x y _ _ hx hy
    exact ⟨by simp only [Prod.snd_add, Pi.add_apply, mul_add, Finset.sum_add_distrib, hx.1, hy.1, add_zero],
      by simp only [Prod.fst_add, Pi.add_apply, add_mul, Finset.sum_add_distrib, hx.2, hy.2, add_zero]⟩
  · intro r x _ hx
    rcases _root_.zmod2_eq_zero_or_one r with rfl | rfl <;> [simp; simpa using hx]

private lemma add_bareLogicalProjection_mem_stabilizerPauliSubmodule
    {L q_code r_0 m_max : ℕ}
    (D_field : Box3D L → LocalCSSDescriptor q_code r_0 m_max)
    (p : PauliBitstringPair L q_code) :
    p + bareLogicalProjection D_field p ∈ stabilizerPauliSubmodule D_field := by
  rcases exists_finset_sum_add_bareLogicalProjection D_field p with ⟨α, hα⟩
  rw [add_comm, hα]
  exact Submodule.sum_mem _ fun c _ => Submodule.subset_span ⟨c, rfl⟩

lemma sum_worldlinePolymerLogicalCoset_fst_mul_snd_eq_zero_of_compatible
    {L q_code r_0 m_max R_cut : ℕ} [NeZero L]
    {C_RCA : ℝ} (hC_RCA : 1 ≤ C_RCA)
    (D_field : Box3D L → LocalCSSDescriptor q_code r_0 m_max)
    (h_valid : ValidDescriptorField D_field)
    (sys : SysCSS[L, q_code, m_max])
    (h_sys_checks : ∀ idx, sys.checkProj idx = staticCSSCheckProj D_field idx ∧
      sys.support idx = staticCSSCheckSupport D_field idx ∧ sys.weight idx = 1)
    {γ₁ γ₂ : WorldlineDysonPolymer L q_code}
    (hγ₁ : IsValidWorldlinePolymer D_field sys C_RCA R_cut γ₁)
    (hγ₂ : IsValidWorldlinePolymer D_field sys C_RCA R_cut γ₂)
    (h_compat : ¬ArePolymersIncompatible sys C_RCA γ₁ γ₂) :
    (∑ slot : BoxSlot3D L q_code,
      (worldlinePolymerLogicalCoset D_field sys C_RCA γ₂).1 slot *
        (worldlinePolymerLogicalCoset D_field sys C_RCA γ₁).2 slot) = 0 := by
  let a₁ := worldlinePolymerLoopX γ₁; let b₁ := worldlinePolymerLoopZ γ₁
  let a₂ := worldlinePolymerLoopX γ₂; let b₂ := worldlinePolymerLoopZ γ₂
  let μ₁ := worldlinePolymerLogicalCoset D_field sys C_RCA γ₁
  let μ₂ := worldlinePolymerLogicalCoset D_field sys C_RCA γ₂
  let q₁ := (a₁, b₁) + μ₁; let q₂ := (a₂, b₂) + μ₂
  have hq₁_mem : q₁ ∈ stabilizerPauliSubmodule D_field :=
    add_bareLogicalProjection_mem_stabilizerPauliSubmodule D_field (a₁, b₁)
  have hq₂_mem : q₂ ∈ stabilizerPauliSubmodule D_field :=
    add_bareLogicalProjection_mem_stabilizerPauliSubmodule D_field (a₂, b₂)
  have hμ₁_closed : μ₁ ∈ syndromeClosedPauliFinset D_field :=
    (isSpanningCheckSurfaceForPolymer_of_isValidWorldlinePolymer D_field h_valid sys h_sys_checks γ₁ hγ₁).1
  have hp₂_closed : (a₂, b₂) ∈ syndromeClosedPauliFinset D_field :=
    Finset.mem_filter.mpr ⟨Finset.mem_univ _, hγ₂.2.2.1.2⟩
  have h_q2_mu1 : (∑ slot : BoxSlot3D L q_code, q₂.1 slot * μ₁.2 slot) = 0 :=
    (sum_stabilizerPauliSubmodule_mul_eq_zero_of_syndromeClosed D_field hμ₁_closed hq₂_mem).2
  have h_a2_q1 : (∑ slot : BoxSlot3D L q_code, a₂ slot * q₁.2 slot) = 0 :=
    (sum_stabilizerPauliSubmodule_mul_eq_zero_of_syndromeClosed D_field hp₂_closed hq₁_mem).1
  have h_compat_symm : ¬ArePolymersIncompatible sys C_RCA γ₂ γ₁ := fun h_inc =>
    h_compat (fun h_disj => h_inc h_disj.symm)
  have h_a2_b1 : (∑ slot : BoxSlot3D L q_code, a₂ slot * b₁ slot) = 0 :=
    Finset.sum_eq_zero fun slot _ =>
      (worldlinePolymerLoop_slot_disjoint_of_compatible D_field sys
        (fun idx => (h_sys_checks idx).2.1) hC_RCA hγ₂ hγ₁ h_compat_symm slot).2
  have hμ₂_eq : ∀ slot, μ₂.1 slot = a₂ slot + q₂.1 slot := fun slot => by
    change μ₂.1 slot = a₂ slot + (a₂ slot + μ₂.1 slot)
    exact (by generalize a₂ slot = x; generalize μ₂.1 slot = y; revert x y; decide)
  have hμ₁_eq : ∀ slot, μ₁.2 slot = b₁ slot + q₁.2 slot := fun slot => by
    change μ₁.2 slot = b₁ slot + (b₁ slot + μ₁.2 slot)
    exact (by generalize b₁ slot = x; generalize μ₁.2 slot = y; revert x y; decide)
  calc (∑ slot : BoxSlot3D L q_code, μ₂.1 slot * μ₁.2 slot)
    _ = ∑ slot : BoxSlot3D L q_code, (a₂ slot + q₂.1 slot) * μ₁.2 slot :=
        Finset.sum_congr rfl fun slot _ => by rw [hμ₂_eq slot]
    _ = (∑ slot : BoxSlot3D L q_code, a₂ slot * μ₁.2 slot) +
          (∑ slot : BoxSlot3D L q_code, q₂.1 slot * μ₁.2 slot) := by
        simp only [add_mul, Finset.sum_add_distrib]
    _ = ∑ slot : BoxSlot3D L q_code, a₂ slot * (b₁ slot + q₁.2 slot) := by
        rw [h_q2_mu1, add_zero]
        exact Finset.sum_congr rfl fun slot _ => by rw [hμ₁_eq slot]
    _ = (∑ slot : BoxSlot3D L q_code, a₂ slot * b₁ slot) +
          (∑ slot : BoxSlot3D L q_code, a₂ slot * q₁.2 slot) := by
        simp only [mul_add, Finset.sum_add_distrib]
    _ = 0 := by rw [h_a2_b1, h_a2_q1, add_zero]

end DirectWorldlineCluster
