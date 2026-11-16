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

import Proofs.DirectWorldlineCluster.WorldlineDysonUrsellSeries

/-!
# Off-Diagonal Jump-Monomer Decomposition and RCA-1 Spanning Check-Surface Signs

Decomposes off-diagonal cube perturbations into canonical syndrome-shift jump monomers (`worldlineScaleCubeJumpFinset`, `worldlineAllJumpMonomerFinset`) and proves disjoint-collar commutation of `worldlineSyndromeShiftBlockOp`. Characterizes RCA-1 spanning check surfaces for closed worldline polymers (`IsSpanningCheckSurfaceForPolymer`) and establishes the exact parity-sign factorization (`spanningSurfaceSign_mul_worldlinePolymerLoopAmplitude_eq_of_valid`).

## References

* Part II, Section 3.2 (`subsec:rca1-pinching`), Proposition 3.4 (`prop:pauli-diag-off`)
* Part II, Section 3.5 (`subsec:worldline-expansion`), Lemma 3.9 (`lem:worldline-factorization-time-reversal`)
-/

noncomputable section

open scoped Classical BigOperators InnerProduct ComplexConjugate
open Filter Topology Asymptotics ContinuousLinearMap KMSPinchedGibbs PerturbedThermalBarrier
open SpacetimeWorldlineKP

set_option linter.unusedVariables false
set_option maxRecDepth 20000
set_option maxHeartbeats 1600000

namespace DirectWorldlineCluster

local notation "SiteCSS[" L ", " q_code "]" => UniformSite3D L (CodeSlotConfig q_code)
local notation "ℋ_CSS[" L ", " q_code "]" => ManyBodyHilbertSpace (SiteCSS[L, q_code])
local notation "ℬ_CSS[" L ", " q_code "]" => ℋ_CSS[L, q_code] →L[ℂ] ℋ_CSS[L, q_code]
local notation "IdxCSS[" L ", " q_code ", " m_max "]" => StaticCSSCheckIdx L q_code m_max
local notation "SysCSS[" L ", " q_code ", " m_max "]" =>
  IndexedCommutingProjectorHamiltonian 3 L (SiteCSS[L, q_code]) (IdxCSS[L, q_code, m_max])

/-!
## 1. Canonical Jump-Monomer Decomposition, Disjoint-Collar Factorization, and Cluster Ursell Helpers
(Part II, Proposition 3.4(iii) (`prop:pauli-diag-off`), Proposition 3.6 (`prop:walsh-coset-dominance`), Lemma 3.9 (`lem:worldline-factorization-time-reversal`), and Proposition 3.10 (`prop:tube-local-ursell-erasure`))
-/

/-- Canonical off-diagonal jump monomers on a scale-cube `(r, A)` (Part II, Proposition 3.4(iii) (`prop:pauli-diag-off`), Equation `eq:V-off-jump-decomp`, and Section 3.5 (`subsec:worldline-expansion`), Equation `eq:local-pauli-jump-xi`): consists of all jump monomers `((r, A), p)` supported on `A` with non-zero syndrome shift `δ = staticCSSPauliFlip D_field p.1 p.2 ≠ 0` such that `p = canonicalJumpPauliRep D_field A δ`. -/
def worldlineScaleCubeJumpFinset
    {L q_code r_0 m_max : ℕ}
    (D_field : Box3D L → LocalCSSDescriptor q_code r_0 m_max)
    (r : ℕ) (A : Finset (Box3D L)) : Finset (WorldlineJumpMonomer L q_code) :=
  ((Finset.univ : Finset (PauliBitstringPair L q_code)).filter (fun p =>
    (∀ slot : BoxSlot3D L q_code, p.1 slot ≠ 0 ∨ p.2 slot ≠ 0 → slot.1 ∈ A) ∧
    staticCSSPauliFlip D_field p.1 p.2 ≠ (fun _ => false) ∧
    p = canonicalJumpPauliRep D_field A (staticCSSPauliFlip D_field p.1 p.2))).image
    (fun p => ((r, A), p))

/-- Characterization of membership in `worldlineScaleCubeJumpFinset D_field r A` and injectivity of the syndrome shift `staticCSSPauliFlip D_field ξ.2.1 ξ.2.2` across canonical jump monomers on `(r, A)` (Part II, Proposition 3.4(iii) (`prop:pauli-diag-off`), Equation `eq:V-off-jump-decomp`). -/
lemma mem_worldlineScaleCubeJumpFinset_iff_and_injOn
    {L q_code r_0 m_max : ℕ}
    (D_field : Box3D L → LocalCSSDescriptor q_code r_0 m_max)
    (r : ℕ) (A : Finset (Box3D L)) :
    (∀ ξ : WorldlineJumpMonomer L q_code,
      ξ ∈ worldlineScaleCubeJumpFinset D_field r A ↔
        ξ.1 = (r, A) ∧
        (∀ slot : BoxSlot3D L q_code, ξ.2.1 slot ≠ 0 ∨ ξ.2.2 slot ≠ 0 → slot.1 ∈ A) ∧
        staticCSSPauliFlip D_field ξ.2.1 ξ.2.2 ≠ (fun _ => false) ∧
        ξ.2 = canonicalJumpPauliRep D_field A (staticCSSPauliFlip D_field ξ.2.1 ξ.2.2)) ∧
    Set.InjOn (fun ξ : WorldlineJumpMonomer L q_code => staticCSSPauliFlip D_field ξ.2.1 ξ.2.2)
      (worldlineScaleCubeJumpFinset D_field r A : Set (WorldlineJumpMonomer L q_code)) := by
  have h_iff : ∀ ξ : WorldlineJumpMonomer L q_code,
      ξ ∈ worldlineScaleCubeJumpFinset D_field r A ↔
        ξ.1 = (r, A) ∧
        (∀ slot : BoxSlot3D L q_code, ξ.2.1 slot ≠ 0 ∨ ξ.2.2 slot ≠ 0 → slot.1 ∈ A) ∧
        staticCSSPauliFlip D_field ξ.2.1 ξ.2.2 ≠ (fun _ => false) ∧
        ξ.2 = canonicalJumpPauliRep D_field A (staticCSSPauliFlip D_field ξ.2.1 ξ.2.2) := by
    intro ξ
    unfold worldlineScaleCubeJumpFinset
    rw [Finset.mem_image]
    constructor
    · rintro ⟨p, hp, rfl⟩
      rcases (Finset.mem_filter.mp hp).2 with ⟨h_supp, h_ne, h_rep⟩
      exact ⟨rfl, h_supp, h_ne, h_rep⟩
    · rintro ⟨h1, h_supp, h_ne, h_rep⟩
      refine ⟨ξ.2, Finset.mem_filter.mpr ⟨Finset.mem_univ _, h_supp, h_ne, h_rep⟩, ?_⟩
      exact Prod.ext h1.symm rfl
  refine ⟨h_iff, ?_⟩
  intro ξ₁ hξ₁ ξ₂ hξ₂ h_eq
  (try dsimp only at h_eq)
  rcases (h_iff ξ₁).mp hξ₁ with ⟨h1_1, _, _, h1_rep⟩
  rcases (h_iff ξ₂).mp hξ₂ with ⟨h2_1, _, _, h2_rep⟩
  refine Prod.ext (h1_1.trans h2_1.symm) ?_
  rw [h1_rep, h2_rep, h_eq]

/-- Uniform `q_code`-independent bound on the number of canonical jump monomers on a scale-cube `(r, A)` (Part II, Proposition 3.4(iii) (`prop:pauli-diag-off`) and Proposition 3.10(ii) (`prop:tube-local-ursell-erasure`)): because every jump monomer `ξ ∈ worldlineScaleCubeJumpFinset D_field r A` is uniquely determined by its syndrome shift `δ` supported inside `cubeIntersectingChecks sys A`, there are at most `2 ^ (cubeIntersectingChecks sys A).card ≤ 2 ^ kpCollarMaxCheckCard R_cut r_0 w_0 C_RCA` canonical jump monomers on `(r, A)`. -/
lemma card_worldlineScaleCubeJumpFinset_le
    {L q_code r_0 m_max w_0 R_cut : ℕ} [NeZero L]
    (D_field : Box3D L → LocalCSSDescriptor q_code r_0 m_max)
    (sys : SysCSS[L, q_code, m_max])
    (h_sys_supp : ∀ idx, sys.support idx = staticCSSCheckSupport D_field idx)
    (h_geom : sys.IsGeometricallyLocal r_0 w_0)
    (C_RCA : ℝ) {r : ℕ} (hr : r ∈ Finset.Icc 1 (min R_cut L))
    {A : Finset (Box3D L)} (hA : A ∈ boxCubes 3 L r) :
    (worldlineScaleCubeJumpFinset D_field r A).card ≤
      2 ^ (cubeIntersectingChecks sys A).card ∧
    (worldlineScaleCubeJumpFinset D_field r A).card ≤
      2 ^ kpCollarMaxCheckCard R_cut r_0 w_0 C_RCA := by
  rcases mem_worldlineScaleCubeJumpFinset_iff_and_injOn D_field r A with ⟨h_iff, h_inj⟩
  let S := cubeIntersectingChecks sys A
  let f : WorldlineJumpMonomer L q_code → Finset (IdxCSS[L, q_code, m_max]) :=
    fun ξ => S.filter (fun c => staticCSSPauliFlip D_field ξ.2.1 ξ.2.2 c = true)
  have hf_maps : ∀ ξ ∈ worldlineScaleCubeJumpFinset D_field r A, f ξ ∈ S.powerset :=
    fun ξ _ => Finset.mem_powerset.mpr (Finset.filter_subset _ S)
  have hf_inj : Set.InjOn f
      (worldlineScaleCubeJumpFinset D_field r A : Set (WorldlineJumpMonomer L q_code)) := by
    intro ξ₁ hξ₁ ξ₂ hξ₂ hf_eq
    apply h_inj hξ₁ hξ₂
    (try dsimp only)
    have h1_supp := ((h_iff ξ₁).mp hξ₁).2.1
    have h2_supp := ((h_iff ξ₂).mp hξ₂).2.1
    ext c
    by_cases hc : c ∈ S
    · have h_mem_iff : c ∈ f ξ₁ ↔ c ∈ f ξ₂ := by rw [hf_eq]
      simp only [f, Finset.mem_filter, hc, true_and] at h_mem_iff
      cases h_b1 : staticCSSPauliFlip D_field ξ₁.2.1 ξ₁.2.2 c <;>
        cases h_b2 : staticCSSPauliFlip D_field ξ₂.2.1 ξ₂.2.2 c
      · rfl
      · exfalso
        have := h_mem_iff.mpr h_b2
        rw [h_b1] at this; cases this
      · exfalso
        have := h_mem_iff.mp h_b1
        rw [h_b2] at this; cases this
      · rfl
    · have h1_false : staticCSSPauliFlip D_field ξ₁.2.1 ξ₁.2.2 c = false := by
        cases h_b1 : staticCSSPauliFlip D_field ξ₁.2.1 ξ₁.2.2 c
        · rfl
        · exact False.elim (hc (staticCSSPauliFlip_mem_cubeIntersectingChecks
            D_field sys h_sys_supp A ξ₁.2.1 ξ₁.2.2 h1_supp c h_b1))
      have h2_false : staticCSSPauliFlip D_field ξ₂.2.1 ξ₂.2.2 c = false := by
        cases h_b2 : staticCSSPauliFlip D_field ξ₂.2.1 ξ₂.2.2 c
        · rfl
        · exact False.elim (hc (staticCSSPauliFlip_mem_cubeIntersectingChecks
            D_field sys h_sys_supp A ξ₂.2.1 ξ₂.2.2 h2_supp c h_b2))
      rw [h1_false, h2_false]
  have h_card_S : (worldlineScaleCubeJumpFinset D_field r A).card ≤ 2 ^ S.card := by
    calc (worldlineScaleCubeJumpFinset D_field r A).card
      _ ≤ S.powerset.card := Finset.card_le_card_of_injOn f hf_maps hf_inj
      _ = 2 ^ S.card := Finset.card_powerset S
  refine ⟨h_card_S, le_trans h_card_S (Nat.pow_le_pow_right (by norm_num) ?_)⟩
  exact card_cubeIntersectingChecks_le_kpCollarMaxCheckCard sys h_geom C_RCA hr hA

private lemma zmod2_add_self_bridge (x : ZMod 2) : x + x = 0 := by
  fin_cases x <;> decide

private lemma zmod2_ne_zero_iff_eq_one_bridge (x : ZMod 2) (h : x ≠ 0) : x = 1 := by
  fin_cases x
  · contradiction
  · rfl

private lemma pauliPhase_add_left_bridge {ι : Type} [Fintype ι] (a₁ a₂ z : ι → ZMod 2) :
    pauliPhase (a₁ + a₂) z = pauliPhase a₁ z * pauliPhase a₂ z := by
  unfold pauliPhase
  have h_sum : (∑ q : ι, (a₁ + a₂) q * z q) =
      (∑ q : ι, a₁ q * z q) + (∑ q : ι, a₂ q * z q) := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun q _ => add_mul (a₁ q) (a₂ q) (z q)
  rw [h_sum]
  have h11 : (1 : ZMod 2) + 1 = 0 := rfl
  rcases _root_.zmod2_eq_zero_or_one (∑ q : ι, a₁ q * z q) with h1 | h1 <;>
    rcases _root_.zmod2_eq_zero_or_one (∑ q : ι, a₂ q * z q) with h2 | h2 <;>
    rw [h1, h2]
  · norm_num
  · norm_num
  · norm_num
  · rw [h11]; norm_num

private lemma pauliPhase_add_right_bridge {ι : Type} [Fintype ι] (a z₁ z₂ : ι → ZMod 2) :
    pauliPhase a (z₁ + z₂) = pauliPhase a z₁ * pauliPhase a z₂ := by
  unfold pauliPhase
  have h_sum : (∑ q : ι, a q * (z₁ + z₂) q) =
      (∑ q : ι, a q * z₁ q) + (∑ q : ι, a q * z₂ q) := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun q _ => mul_add (a q) (z₁ q) (z₂ q)
  rw [h_sum]
  have h11 : (1 : ZMod 2) + 1 = 0 := rfl
  rcases _root_.zmod2_eq_zero_or_one (∑ q : ι, a q * z₁ q) with h1 | h1 <;>
    rcases _root_.zmod2_eq_zero_or_one (∑ q : ι, a q * z₂ q) with h2 | h2 <;>
    rw [h1, h2]
  · norm_num
  · norm_num
  · norm_num
  · rw [h11]; norm_num

private lemma sum_pauliPhase_eq_diag_bridge {ι : Type} [Fintype ι] [DecidableEq ι] (z : ι → ZMod 2) :
    (∑ a : ι → ZMod 2, pauliPhase a z) = if z = 0 then (Fintype.card (ι → ZMod 2) : ℂ) else 0 := by
  split_ifs with hz
  · subst hz; simp [pauliPhase]
  · have h_ex : ∃ q₀ : ι, z q₀ ≠ 0 := by by_contra! h_all; exact hz (funext h_all)
    rcases h_ex with ⟨q₀, hzq₀⟩
    have hzq₀_one : z q₀ = 1 := zmod2_ne_zero_iff_eq_one_bridge _ hzq₀
    let e₀ : ι → ZMod 2 := fun q => if q = q₀ then 1 else 0
    have he₀_phase : pauliPhase e₀ z = -1 := by
      dsimp [pauliPhase, e₀]
      have h_sum : (∑ q : ι, (if q = q₀ then (1 : ZMod 2) else 0) * z q) = z q₀ := by simp
      rw [h_sum, hzq₀_one, if_neg (by decide : (1 : ZMod 2) ≠ 0)]
    have h_shift : (∑ a : ι → ZMod 2, pauliPhase a z) = -(∑ a : ι → ZMod 2, pauliPhase a z) := by
      conv_lhs => rw [← Equiv.sum_comp (Equiv.addRight e₀) (fun a => pauliPhase a z)]
      rw [← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun a _ => ?_
      change pauliPhase (a + e₀) z = -pauliPhase a z
      rw [pauliPhase_add_left_bridge, he₀_phase, mul_neg_one]
    have h_two : (2 : ℂ) * (∑ a : ι → ZMod 2, pauliPhase a z) = 0 := by linear_combination h_shift
    exact (mul_eq_zero.mp h_two).resolve_left two_ne_zero

private abbrev SubSlot3DBridge (L q_code : ℕ) (A : Finset (Box3D L)) : Type := ↥A × Fin q_code

private def extSlotChainBridge {L q_code : ℕ} (A : Finset (Box3D L))
    (a : SubSlot3DBridge L q_code A → ZMod 2) : BoxSlot3D L q_code → ZMod 2 :=
  fun p => if hp : p.1 ∈ A then a (⟨p.1, hp⟩, p.2) else 0

private def localSlotConfigToSubBridge {L q_code : ℕ} (A : Finset (Box3D L))
    (α : LocalConfig (SiteCSS[L, q_code]) A) : SubSlot3DBridge L q_code A → ZMod 2 :=
  fun p => boolToZMod2 (α p.1 p.2)

private lemma localSlotConfigToSubBridge_injective {L q_code : ℕ} (A : Finset (Box3D L)) :
    Function.Injective (localSlotConfigToSubBridge (L := L) (q_code := q_code) A) := by
  intro α β h
  funext x s
  have hxs := congr_fun h (x, s)
  dsimp [localSlotConfigToSubBridge] at hxs
  revert hxs; cases α x s <;> cases β x s <;> decide

private lemma pauliPhase_extSlotChainBridge {L q_code : ℕ} (A : Finset (Box3D L))
    (a : SubSlot3DBridge L q_code A → ZMod 2)
    (ψ : ManyBodyConfig (SiteCSS[L, q_code])) :
    pauliPhase (extSlotChainBridge A a) (codeConfigBits ψ) =
      pauliPhase a (localSlotConfigToSubBridge A (restrictConfig A ψ)) := by
  dsimp [pauliPhase]
  have h_sum : (∑ p : BoxSlot3D L q_code, extSlotChainBridge A a p * codeConfigBits ψ p) =
      ∑ p : SubSlot3DBridge L q_code A, a p * localSlotConfigToSubBridge A (restrictConfig A ψ) p := by
    rw [Fintype.sum_prod_type, Fintype.sum_prod_type, ← Finset.sum_subset (Finset.subset_univ A)]
    · rw [← Finset.sum_attach A]
      refine Finset.sum_congr rfl fun vA _ => Finset.sum_congr rfl fun s _ => ?_
      simp [extSlotChainBridge, codeConfigBits, localSlotConfigToSubBridge, restrictConfig, vA.2]
    · intro v _ hv_not
      refine Finset.sum_eq_zero fun s _ => ?_
      dsimp [extSlotChainBridge]
      rw [dif_neg hv_not, zero_mul]
  rw [h_sum]

private def localDiffSlotChainBridge {L q_code : ℕ} (A : Finset (Box3D L))
    (α β : LocalConfig (SiteCSS[L, q_code]) A) : BoxSlot3D L q_code → ZMod 2 :=
  extSlotChainBridge A (localSlotConfigToSubBridge A α + localSlotConfigToSubBridge A β)

private lemma flipCodeConfig_localDiffSlotChainBridge {L q_code : ℕ} (A : Finset (Box3D L))
    (α β : LocalConfig (SiteCSS[L, q_code]) A)
    (ψ : ManyBodyConfig (SiteCSS[L, q_code])) (hβ : restrictConfig A ψ = β) :
    flipCodeConfig (localDiffSlotChainBridge A α β) ψ = spliceConfig A α ψ := by
  funext v s
  dsimp [flipCodeConfig, spliceConfig, localDiffSlotChainBridge, extSlotChainBridge]
  by_cases hvA : v ∈ A
  · rw [dif_pos hvA, dif_pos hvA]
    dsimp [localSlotConfigToSubBridge]
    have hβ_eq : β ⟨v, hvA⟩ s = ψ v s := by rw [← hβ]; rfl
    rw [hβ_eq]; cases ψ v s <;> cases α ⟨v, hvA⟩ s <;> rfl
  · rw [dif_neg hvA, dif_neg hvA]; dsimp [zmod2ToBool]; cases ψ v s <;> rfl

/-- Local Weyl–Pauli expansion of any operator `M` supported on `A : Finset (Box3D L)` into a finite linear combination of `weylPauliZ (a_fam i) * weylPauliX (b_fam i)` whose bitstrings `(a_fam i, b_fam i)` have slot support contained in `A` (Part II, Proposition 3.4(iii) (`prop:pauli-diag-off`), Equation `eq:V-off-jump-decomp`). -/
lemma exists_local_weylPauli_expansion_on_cube
    {L q_code : ℕ} (A : Finset (Box3D L))
    {M : ℬ_CSS[L, q_code]}
    (hM : IsSupportedOn (SiteCSS[L, q_code]) A M) :
    ∃ (ι : Type) (_ : Fintype ι) (w : ι → ℂ) (a_fam b_fam : ι → BoxSlot3D L q_code → ZMod 2),
      (∀ i : ι, ∀ slot : BoxSlot3D L q_code, a_fam i slot ≠ 0 ∨ b_fam i slot ≠ 0 → slot.1 ∈ A) ∧
      M = ∑ i : ι, w i • (weylPauliZ (a_fam i) * weylPauliX (b_fam i)) := by
  rcases hM with ⟨O_loc, rfl⟩
  let SubQ := SubSlot3DBridge L q_code A
  let Loc := LocalConfig (SiteCSS[L, q_code]) A
  let ι := (Loc × Loc) × (SubQ → ZMod 2)
  let N : ℂ := (Fintype.card (SubQ → ZMod 2) : ℂ)
  have hN_ne : N ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  refine ⟨ι, inferInstance,
    fun i => (O_loc (_root_.deltaLp i.1.1)).ofLp i.1.2 * N⁻¹ *
      pauliPhase i.2 (localSlotConfigToSubBridge A i.1.2),
    fun i => extSlotChainBridge A i.2,
    fun i => localDiffSlotChainBridge A i.1.1 i.1.2,
    fun i slot h_ne => ?_, ?_⟩
  · by_contra hv_not
    rcases h_ne with ha | hb
    · apply ha
      dsimp [extSlotChainBridge]
      exact dif_neg hv_not
    · apply hb
      dsimp [localDiffSlotChainBridge, extSlotChainBridge]
      exact dif_neg hv_not
  · ext φ ψ
    rw [ContinuousLinearMap.sum_apply, _root_.ofLp_sum]
    change (O_loc (WithLp.toLp 2 fun α => φ.ofLp (spliceConfig A α ψ))).ofLp (restrictConfig A ψ) = _
    rw [_root_.clm_apply_ofLp_eq_sum O_loc]
    conv_rhs => rw [Fintype.sum_prod_type, Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun α _ => ?_
    have h_inner_sum : ∀ β : Loc, (∑ a : SubQ → ZMod 2, ((((O_loc (_root_.deltaLp α)).ofLp β *
        N⁻¹ * pauliPhase a (localSlotConfigToSubBridge A β)) • (weylPauliZ (extSlotChainBridge A a) *
          weylPauliX (localDiffSlotChainBridge A α β))) φ).ofLp ψ) =
        if β = restrictConfig A ψ then
          φ.ofLp (spliceConfig A α ψ) * (O_loc (_root_.deltaLp α)).ofLp β
        else 0 := by
      intro β
      have h_term : ∀ a : SubQ → ZMod 2, ((((O_loc (_root_.deltaLp α)).ofLp β *
          N⁻¹ * pauliPhase a (localSlotConfigToSubBridge A β)) • (weylPauliZ (extSlotChainBridge A a) *
            weylPauliX (localDiffSlotChainBridge A α β))) φ).ofLp ψ =
          ((O_loc (_root_.deltaLp α)).ofLp β * N⁻¹ *
            φ.ofLp (flipCodeConfig (localDiffSlotChainBridge A α β) ψ)) *
            pauliPhase a (localSlotConfigToSubBridge A (restrictConfig A ψ) +
              localSlotConfigToSubBridge A β) := fun a => by
        change ((O_loc (_root_.deltaLp α)).ofLp β * N⁻¹ *
            pauliPhase a (localSlotConfigToSubBridge A β)) *
          (pauliPhase (extSlotChainBridge A a) (codeConfigBits ψ) *
            φ.ofLp (flipCodeConfig (localDiffSlotChainBridge A α β) ψ)) = _
        rw [pauliPhase_extSlotChainBridge A a ψ, pauliPhase_add_right_bridge]
        ring
      simp_rw [h_term, ← Finset.mul_sum, sum_pauliPhase_eq_diag_bridge]
      have h_zero_iff :
          localSlotConfigToSubBridge A (restrictConfig A ψ) +
            localSlotConfigToSubBridge A β = 0 ↔ β = restrictConfig A ψ := by
        constructor
        · intro h_add0
          refine localSlotConfigToSubBridge_injective A (funext fun qA => ?_)
          have hq := congr_fun h_add0 qA
          (try dsimp at hq)
          calc localSlotConfigToSubBridge A β qA
            _ = (localSlotConfigToSubBridge A (restrictConfig A ψ) qA +
                  localSlotConfigToSubBridge A (restrictConfig A ψ) qA) +
                localSlotConfigToSubBridge A β qA := by
                  rw [zmod2_add_self_bridge, zero_add]
            _ = localSlotConfigToSubBridge A (restrictConfig A ψ) qA +
                (localSlotConfigToSubBridge A (restrictConfig A ψ) qA +
                  localSlotConfigToSubBridge A β qA) := by abel
            _ = localSlotConfigToSubBridge A (restrictConfig A ψ) qA := by
                  rw [hq, add_zero]
        · intro h_eq
          subst h_eq
          funext qA
          exact zmod2_add_self_bridge _
      by_cases hβ : β = restrictConfig A ψ
      · rw [if_pos (h_zero_iff.mpr hβ), if_pos hβ]
        subst hβ
        rw [flipCodeConfig_localDiffSlotChainBridge A α (restrictConfig A ψ) ψ rfl]
        change ((O_loc (_root_.deltaLp α)).ofLp (restrictConfig A ψ) * N⁻¹ *
          φ.ofLp (spliceConfig A α ψ)) * N = _
        calc ((O_loc (_root_.deltaLp α)).ofLp (restrictConfig A ψ) * N⁻¹ *
            φ.ofLp (spliceConfig A α ψ)) * N
          _ = (N⁻¹ * N) * φ.ofLp (spliceConfig A α ψ) *
              (O_loc (_root_.deltaLp α)).ofLp (restrictConfig A ψ) := by ring
          _ = φ.ofLp (spliceConfig A α ψ) *
              (O_loc (_root_.deltaLp α)).ofLp (restrictConfig A ψ) := by
                rw [inv_mul_cancel₀ hN_ne, one_mul]
      · rw [if_neg (mt h_zero_iff.mp hβ), if_neg hβ, mul_zero]
    (try dsimp only)
    rw [Finset.sum_congr rfl (fun β _ => h_inner_sum β), Finset.sum_ite_eq',
      if_pos (Finset.mem_univ (restrictConfig A ψ))]

/-- **Canonical Jump-Monomer Decomposition of `pauliOffDiagonalTerm`** (Part II, Proposition 3.4(iii) (`prop:pauli-diag-off`), Equation `eq:V-off-jump-decomp`): On every realizable syndrome sector `σ₀ ∈ realizableSyndromes D_field`, the off-diagonal scale-cube perturbation `pauliOffDiagonalTerm sys V r A` decomposes into the finite sum of canonical syndrome-shift jump blocks `worldlineSyndromeShiftBlockOp D_field sys V ξ` over `ξ ∈ worldlineScaleCubeJumpFinset D_field r A`. -/
lemma pauliOffDiagonalTerm_mul_syndromeProjector_eq_sum_worldlineScaleCubeJumpFinset
    {L q_code r_0 m_max : ℕ}
    (D_field : Box3D L → LocalCSSDescriptor q_code r_0 m_max)
    (sys : SysCSS[L, q_code, m_max])
    (h_sys_checks : ∀ idx, sys.checkProj idx = staticCSSCheckProj D_field idx ∧
      sys.support idx = staticCSSCheckSupport D_field idx ∧ sys.weight idx = 1)
    (V : QuasiLocalPerturbation 3 L (SiteCSS[L, q_code]))
    (r : ℕ) (A : Finset (Box3D L))
    (hV_supp : IsSupportedOn (SiteCSS[L, q_code]) A (V.term r A))
    {σ₀ : IdxCSS[L, q_code, m_max] → Bool}
    (hσ₀ : σ₀ ∈ realizableSyndromes D_field) :
    pauliOffDiagonalTerm sys V r A * sys.syndromeProjector σ₀ =
      ∑ ξ ∈ worldlineScaleCubeJumpFinset D_field r A,
        worldlineSyndromeShiftBlockOp D_field sys V ξ * sys.syndromeProjector σ₀ := by
  have h_res := PerturbedThermalBarrier.syndrome_resolution_indexed sys
  rcases mem_worldlineScaleCubeJumpFinset_iff_and_injOn D_field r A with ⟨h_mem_iff, h_inj⟩
  have h_block : ∀ σ₁ : IdxCSS[L, q_code, m_max] → Bool,
      sys.syndromeProjector σ₁ * (pauliOffDiagonalTerm sys V r A * sys.syndromeProjector σ₀) =
        sys.syndromeProjector σ₁ *
          (∑ ξ ∈ worldlineScaleCubeJumpFinset D_field r A,
            worldlineSyndromeShiftBlockOp D_field sys V ξ * sys.syndromeProjector σ₀) := by
    intro σ₁
    rw [Finset.mul_sum]
    have h_term : ∀ ξ ∈ worldlineScaleCubeJumpFinset D_field r A,
        sys.syndromeProjector σ₁ *
          (worldlineSyndromeShiftBlockOp D_field sys V ξ * sys.syndromeProjector σ₀) =
        if staticCSSPauliFlip D_field ξ.2.1 ξ.2.2 = syndromeXor σ₁ σ₀ then
          sys.syndromeProjector σ₁ * (pauliOffDiagonalTerm sys V r A * sys.syndromeProjector σ₀)
        else 0 := by
      intro ξ hξ
      have hξ_1 : ξ.1 = (r, A) := ((h_mem_iff ξ).mp hξ).1
      have h_act := (worldlineSyndromeShiftBlockOp_mul_syndromeProjector D_field sys V ξ σ₀).1
      (try dsimp only at h_act)
      rw [h_act, if_pos hσ₀, hξ_1]
      (try dsimp only)
      let δ := staticCSSPauliFlip D_field ξ.2.1 ξ.2.2
      have h_xor_iff : δ = syndromeXor σ₁ σ₀ ↔ σ₁ = syndromeXor δ σ₀ := by
        constructor <;> intro h_eq <;> ext c
        · rw [h_eq]; unfold syndromeXor; cases σ₁ c <;> cases σ₀ c <;> rfl
        · rw [h_eq]; unfold syndromeXor; cases δ c <;> cases σ₀ c <;> rfl
      by_cases h_eq : δ = syndromeXor σ₁ σ₀
      · have h_σ₁ : σ₁ = syndromeXor δ σ₀ := h_xor_iff.mp h_eq
        rw [if_pos h_eq, ← h_σ₁]
        calc sys.syndromeProjector σ₁ *
              (sys.syndromeProjector σ₁ * pauliOffDiagonalTerm sys V r A * sys.syndromeProjector σ₀)
          _ = (sys.syndromeProjector σ₁ * sys.syndromeProjector σ₁) *
                (pauliOffDiagonalTerm sys V r A * sys.syndromeProjector σ₀) := by
                simp only [mul_assoc]
          _ = sys.syndromeProjector σ₁ *
                (pauliOffDiagonalTerm sys V r A * sys.syndromeProjector σ₀) := by
                rw [(h_res.2.1 σ₁).1]
      · have h_ne : σ₁ ≠ syndromeXor δ σ₀ := mt h_xor_iff.mpr h_eq
        rw [if_neg h_eq]
        calc sys.syndromeProjector σ₁ *
              (sys.syndromeProjector (syndromeXor δ σ₀) *
                pauliOffDiagonalTerm sys V r A * sys.syndromeProjector σ₀)
          _ = (sys.syndromeProjector σ₁ * sys.syndromeProjector (syndromeXor δ σ₀)) *
                (pauliOffDiagonalTerm sys V r A * sys.syndromeProjector σ₀) := by
                simp only [mul_assoc]
          _ = 0 := by rw [h_res.2.2.1 σ₁ (syndromeXor δ σ₀) h_ne, zero_mul]
    rw [Finset.sum_congr rfl h_term]
    by_cases h_ex_ξ : ∃ ξ ∈ worldlineScaleCubeJumpFinset D_field r A,
        staticCSSPauliFlip D_field ξ.2.1 ξ.2.2 = syndromeXor σ₁ σ₀
    · rcases h_ex_ξ with ⟨ξ₀, hξ₀_mem, hξ₀_flip⟩
      symm
      rw [Finset.sum_eq_single ξ₀]
      · exact if_pos hξ₀_flip
      · intro ξ hξ h_ne
        refine if_neg fun h_fl => h_ne ?_
        apply h_inj hξ hξ₀_mem
        (try dsimp only)
        exact h_fl.trans hξ₀_flip.symm
      · intro h_not
        exact False.elim (h_not hξ₀_mem)
    · push_neg at h_ex_ξ
      have h_rhs_zero :
          (∑ ξ ∈ worldlineScaleCubeJumpFinset D_field r A,
            if staticCSSPauliFlip D_field ξ.2.1 ξ.2.2 = syndromeXor σ₁ σ₀ then
              sys.syndromeProjector σ₁ * (pauliOffDiagonalTerm sys V r A * sys.syndromeProjector σ₀)
            else 0) = 0 :=
        Finset.sum_eq_zero fun ξ hξ => if_neg (h_ex_ξ ξ hξ)
      rw [h_rhs_zero, ← mul_assoc,
        syndromeProjector_mul_pauliOffDiagonalTerm_mul_syndromeProjector]
      split_ifs with h_diag
      · rfl
      · rcases exists_local_weylPauli_expansion_on_cube A hV_supp with
          ⟨ι, _, w, a_fam, b_fam, h_supp_fam, hV_exp⟩
        rw [hV_exp, Finset.mul_sum, Finset.sum_mul]
        refine Finset.sum_eq_zero fun i _ => ?_
        rw [clm_mul_smul, clm_smul_mul]
        suffices h_zero_i :
            sys.syndromeProjector σ₁ * (weylPauliZ (a_fam i) * weylPauliX (b_fam i)) *
              sys.syndromeProjector σ₀ = 0 by
          rw [h_zero_i, smul_zero]
        have h_flip_i : ∀ idx,
            (weylPauliZ (a_fam i) * weylPauliX (b_fam i)) * sys.checkProj idx =
              (if staticCSSPauliFlip D_field (a_fam i) (b_fam i) idx then
                1 - sys.checkProj idx
              else sys.checkProj idx) *
                (weylPauliZ (a_fam i) * weylPauliX (b_fam i)) := fun idx => by
          rw [(h_sys_checks idx).1]
          exact weylPauliZX_mul_staticCSSCheckProj D_field (a_fam i) (b_fam i) idx
        have h_inter := intertwine_syndromeProjector_of_checkFlip sys h_flip_i σ₀
        have h_xor_eq :
            (fun idx => xor (σ₀ idx) (staticCSSPauliFlip D_field (a_fam i) (b_fam i) idx)) =
              syndromeXor (staticCSSPauliFlip D_field (a_fam i) (b_fam i)) σ₀ := by
          ext idx
          change bne (σ₀ idx) (staticCSSPauliFlip D_field (a_fam i) (b_fam i) idx) =
            bne (staticCSSPauliFlip D_field (a_fam i) (b_fam i) idx) (σ₀ idx)
          cases σ₀ idx <;> cases staticCSSPauliFlip D_field (a_fam i) (b_fam i) idx <;> rfl
        rw [h_xor_eq] at h_inter
        rw [mul_assoc, h_inter, ← mul_assoc]
        have h_ne_shift :
            σ₁ ≠ syndromeXor (staticCSSPauliFlip D_field (a_fam i) (b_fam i)) σ₀ := by
          intro h_eq_shift
          have h_flip_eq :
              staticCSSPauliFlip D_field (a_fam i) (b_fam i) = syndromeXor σ₁ σ₀ := by
            ext c
            rw [h_eq_shift]
            unfold syndromeXor
            cases staticCSSPauliFlip D_field (a_fam i) (b_fam i) c <;> cases σ₀ c <;> rfl
          have h_xor_ne_zero : syndromeXor σ₁ σ₀ ≠ (fun _ => false) := by
            intro h_zero
            apply h_diag
            ext c
            have hc := congr_fun h_zero c
            unfold syndromeXor at hc
            cases h1 : σ₁ c <;> cases h0 : σ₀ c <;> rw [h1, h0] at hc <;> cases hc
          have h_rep_spec := canonicalJumpPauliRep_spec D_field A (syndromeXor σ₁ σ₀)
            ⟨(a_fam i, b_fam i), h_supp_fam i, h_flip_eq⟩
          let ξ₀ : WorldlineJumpMonomer L q_code :=
            ((r, A), canonicalJumpPauliRep D_field A (syndromeXor σ₁ σ₀))
          have hξ₀_in : ξ₀ ∈ worldlineScaleCubeJumpFinset D_field r A :=
            (h_mem_iff ξ₀).mpr ⟨rfl, h_rep_spec.1, by rw [h_rep_spec.2.1]; exact h_xor_ne_zero,
              h_rep_spec.2.2⟩
          exact h_ex_ξ ξ₀ hξ₀_in h_rep_spec.2.1
        rw [h_res.2.2.1 σ₁ _ h_ne_shift, zero_mul]
  calc pauliOffDiagonalTerm sys V r A * sys.syndromeProjector σ₀
    _ = 1 * (pauliOffDiagonalTerm sys V r A * sys.syndromeProjector σ₀) := (one_mul _).symm
    _ = (∑ σ₁ : IdxCSS[L, q_code, m_max] → Bool, sys.syndromeProjector σ₁) *
          (pauliOffDiagonalTerm sys V r A * sys.syndromeProjector σ₀) := by
          rw [h_res.2.2.2.1]
    _ = ∑ σ₁ : IdxCSS[L, q_code, m_max] → Bool,
          sys.syndromeProjector σ₁ *
            (pauliOffDiagonalTerm sys V r A * sys.syndromeProjector σ₀) := by
          rw [Finset.sum_mul]
    _ = ∑ σ₁ : IdxCSS[L, q_code, m_max] → Bool,
          sys.syndromeProjector σ₁ *
            (∑ ξ ∈ worldlineScaleCubeJumpFinset D_field r A,
              worldlineSyndromeShiftBlockOp D_field sys V ξ * sys.syndromeProjector σ₀) :=
          Finset.sum_congr rfl fun σ₁ _ => h_block σ₁
    _ = (∑ σ₁ : IdxCSS[L, q_code, m_max] → Bool, sys.syndromeProjector σ₁) *
          (∑ ξ ∈ worldlineScaleCubeJumpFinset D_field r A,
            worldlineSyndromeShiftBlockOp D_field sys V ξ * sys.syndromeProjector σ₀) := by
          rw [Finset.sum_mul]
    _ = ∑ ξ ∈ worldlineScaleCubeJumpFinset D_field r A,
          worldlineSyndromeShiftBlockOp D_field sys V ξ * sys.syndromeProjector σ₀ := by
          rw [h_res.2.2.2.1, one_mul]

/-- Summation over `worldlineScaleCubeFinset L R_cut` equals the nested sum over
`r ∈ Finset.Icc 1 (min R_cut L)` and `A ∈ BoxCubes 3 L r`. -/
lemma sum_scaleCubeFinset_eq_nested_sum
    {L R_cut : ℕ} {M : Type*} [AddCommMonoid M]
    (g : ℕ × Finset (Box3D L) → M) :
    (∑ p ∈ worldlineScaleCubeFinset L R_cut, g p) =
      ∑ r ∈ Finset.Icc 1 (min R_cut L), ∑ A ∈ boxCubes 3 L r, g (r, A) := by
  unfold worldlineScaleCubeFinset
  have h_disj :
      (↑(Finset.Icc 1 (min R_cut L)) : Set ℕ).PairwiseDisjoint
        (fun r => (boxCubes 3 L r).image (fun A => (r, A))) := by
    intro r₁ _ r₂ _ hr_ne
    refine Finset.disjoint_left.mpr ?_
    intro p hp₁ hp₂
    rcases Finset.mem_image.mp hp₁ with ⟨A₁, _, rfl⟩
    rcases Finset.mem_image.mp hp₂ with ⟨A₂, _, h_eq⟩
    exact hr_ne (Prod.mk.inj h_eq).1.symm
  rw [Finset.sum_biUnion h_disj]
  refine Finset.sum_congr rfl fun r _ => ?_
  refine Finset.sum_image ?_
  intro A₁ _ A₂ _ h_eq
  exact (Prod.mk.inj h_eq).2

/-- Finite set of all canonical off-diagonal jump monomers at cutoff `R_cut`
(Part II, Proposition 3.4(iii) (`prop:pauli-diag-off`), Equation `eq:V-off-jump-decomp`, and
Section 3.5 (`subsec:worldline-expansion`), Equation `eq:local-pauli-jump-xi`). -/
def worldlineAllJumpMonomerFinset
    {L q_code r_0 m_max : ℕ}
    (D_field : Box3D L → LocalCSSDescriptor q_code r_0 m_max)
    (R_cut : ℕ) : Finset (WorldlineJumpMonomer L q_code) :=
  (worldlineScaleCubeFinset L R_cut).biUnion (fun p =>
    worldlineScaleCubeJumpFinset D_field p.1 p.2)

/-- Characterization of membership in `worldlineAllJumpMonomerFinset D_field R_cut`. -/
lemma mem_worldlineAllJumpMonomerFinset_iff
    {L q_code r_0 m_max R_cut : ℕ}
    (D_field : Box3D L → LocalCSSDescriptor q_code r_0 m_max)
    (ξ : WorldlineJumpMonomer L q_code) :
    ξ ∈ worldlineAllJumpMonomerFinset D_field R_cut ↔
      ξ.1 ∈ worldlineScaleCubeFinset L R_cut ∧
      ξ ∈ worldlineScaleCubeJumpFinset D_field ξ.1.1 ξ.1.2 := by
  unfold worldlineAllJumpMonomerFinset
  rw [Finset.mem_biUnion]
  constructor
  · rintro ⟨p, hp, hξ⟩
    have h_p_eq : ξ.1 = p :=
      ((mem_worldlineScaleCubeJumpFinset_iff_and_injOn D_field p.1 p.2).1 ξ).mp hξ |>.1
    rw [h_p_eq]
    exact ⟨hp, hξ⟩
  · rintro ⟨h_p, hξ⟩
    exact ⟨ξ.1, h_p, hξ⟩

/-- **Global Cutoff Off-Diagonal Jump-Block Decomposition**
(Part II, Proposition 3.4(iii) (`prop:pauli-diag-off`), Equation `eq:V-off-jump-decomp`, and Section 3.5 (`subsec:worldline-expansion`), Equation `eq:local-pauli-jump-xi`):
On every realizable syndrome sector `σ₀ ∈ realizableSyndromes D_field`, the total cutoff
off-diagonal perturbation `∑_{r, A} pauliOffDiagonalTerm sys V r A` equals the sum over
`ξ ∈ worldlineAllJumpMonomerFinset D_field R_cut` of `worldlineSyndromeShiftBlockOp D_field sys V ξ`. -/
lemma sum_pauliOffDiagonalTerm_mul_syndromeProjector_eq_sum_worldlineAllJumpMonomerFinset
    {L q_code r_0 m_max R_cut : ℕ}
    (D_field : Box3D L → LocalCSSDescriptor q_code r_0 m_max)
    (sys : SysCSS[L, q_code, m_max])
    (h_sys_checks : ∀ idx, sys.checkProj idx = staticCSSCheckProj D_field idx ∧
      sys.support idx = staticCSSCheckSupport D_field idx ∧ sys.weight idx = 1)
    (V : QuasiLocalPerturbation 3 L (SiteCSS[L, q_code]))
    {σ₀ : IdxCSS[L, q_code, m_max] → Bool}
    (hσ₀ : σ₀ ∈ realizableSyndromes D_field) :
    (∑ r ∈ Finset.Icc 1 (min R_cut L), ∑ A ∈ boxCubes 3 L r,
      pauliOffDiagonalTerm sys V r A) * sys.syndromeProjector σ₀ =
    ∑ ξ ∈ worldlineAllJumpMonomerFinset D_field R_cut,
      worldlineSyndromeShiftBlockOp D_field sys V ξ * sys.syndromeProjector σ₀ := by
  have h_disj :
      (↑(worldlineScaleCubeFinset L R_cut) : Set (ℕ × Finset (Box3D L))).PairwiseDisjoint
        (fun p => worldlineScaleCubeJumpFinset D_field p.1 p.2) := by
    intro p₁ _ p₂ _ hp_ne
    refine Finset.disjoint_left.mpr ?_
    intro ξ hξ₁ hξ₂
    have h1 := ((mem_worldlineScaleCubeJumpFinset_iff_and_injOn D_field p₁.1 p₁.2).1 ξ).mp hξ₁ |>.1
    have h2 := ((mem_worldlineScaleCubeJumpFinset_iff_and_injOn D_field p₂.1 p₂.2).1 ξ).mp hξ₂ |>.1
    exact hp_ne (h1.symm.trans h2)
  unfold worldlineAllJumpMonomerFinset
  rw [Finset.sum_biUnion h_disj,
    ← sum_scaleCubeFinset_eq_nested_sum (fun p => pauliOffDiagonalTerm sys V p.1 p.2),
    Finset.sum_mul]
  refine Finset.sum_congr rfl fun p hp => ?_
  rcases mem_scaleCubeFinset_iff.mp hp with ⟨hr, hA⟩
  have hr_IccL : p.1 ∈ Finset.Icc 1 L :=
    Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp hr).1,
      le_trans (Finset.mem_Icc.mp hr).2 (Nat.min_le_right R_cut L)⟩
  exact pauliOffDiagonalTerm_mul_syndromeProjector_eq_sum_worldlineScaleCubeJumpFinset
    D_field sys h_sys_checks V p.1 p.2 (V.is_supported p.1 hr_IccL p.2 hA) hσ₀

/-- Equivalence between the monomer and jump validity clauses of `IsValidWorldlinePolymer`
and membership in `worldlineAllJumpMonomerFinset D_field R_cut` and `worldlineScaleCubeFinset L R_cut`. -/
lemma isValidWorldlinePolymer_monomers_and_jumps_iff
    {L q_code r_0 m_max R_cut : ℕ}
    (D_field : Box3D L → LocalCSSDescriptor q_code r_0 m_max)
    (γ : WorldlineDysonPolymer L q_code) :
    ((∀ p ∈ worldlinePolymerMonomers γ, p ∈ worldlineScaleCubeFinset L R_cut) ∧
      (∀ ξ ∈ γ.1,
        (∀ slot : BoxSlot3D L q_code, ξ.2.1 slot ≠ 0 ∨ ξ.2.2 slot ≠ 0 → slot.1 ∈ ξ.1.2) ∧
        staticCSSPauliFlip D_field ξ.2.1 ξ.2.2 ≠ (fun _ => false) ∧
        ξ.2 = canonicalJumpPauliRep D_field ξ.1.2 (staticCSSPauliFlip D_field ξ.2.1 ξ.2.2))) ↔
    (∀ ξ ∈ γ.1, ξ ∈ worldlineAllJumpMonomerFinset D_field R_cut) ∧
      (∀ ϑ ∈ γ.2, ϑ ∈ worldlineScaleCubeFinset L R_cut) := by
  constructor
  · rintro ⟨h_mon, h_jumps⟩
    refine ⟨fun ξ hξ => ?_, fun ϑ hϑ => h_mon ϑ (Finset.mem_union_right _ hϑ)⟩
    rw [mem_worldlineAllJumpMonomerFinset_iff]
    have hξ_mon : ξ.1 ∈ worldlinePolymerMonomers γ :=
      Finset.mem_union_left _ (List.mem_toFinset.mpr (List.mem_map_of_mem hξ))
    refine ⟨h_mon ξ.1 hξ_mon, ?_⟩
    exact ((mem_worldlineScaleCubeJumpFinset_iff_and_injOn D_field ξ.1.1 ξ.1.2).1 ξ).mpr
      ⟨rfl, h_jumps ξ hξ⟩
  · rintro ⟨h_jumps, h_mayer⟩
    refine ⟨fun p hp => ?_, fun ξ hξ => ?_⟩
    · unfold worldlinePolymerMonomers at hp
      rcases Finset.mem_union.mp hp with hp_j | hp_m
      · rcases List.mem_map.mp (List.mem_toFinset.mp hp_j) with ⟨ξ, hξ, rfl⟩
        exact ((mem_worldlineAllJumpMonomerFinset_iff D_field ξ).mp (h_jumps ξ hξ)).1
      · exact h_mayer p hp_m
    · have hξ_in := ((mem_worldlineAllJumpMonomerFinset_iff D_field ξ).mp (h_jumps ξ hξ)).2
      exact (((mem_worldlineScaleCubeJumpFinset_iff_and_injOn D_field ξ.1.1 ξ.1.2).1 ξ).mp hξ_in).2

/-- Net syndrome shift `worldlineJumpListFlip D_field γ.1` equals the syndrome flip of the
net loop bitstrings `(worldlinePolymerLoopX γ, worldlinePolymerLoopZ γ)`
(Part II, Section 3.5 (`subsec:worldline-expansion`), Equation `eq:local-pauli-jump-xi`, and
Lemma 3.9 (`lem:worldline-factorization-time-reversal`)). -/
lemma worldlineJumpListFlip_eq_staticCSSPauliFlip_loop
    {L q_code r_0 m_max : ℕ} [NeZero L]
    (D_field : Box3D L → LocalCSSDescriptor q_code r_0 m_max)
    (γ : WorldlineDysonPolymer L q_code) :
    worldlineJumpListFlip D_field γ.1 =
      staticCSSPauliFlip D_field (worldlinePolymerLoopX γ) (worldlinePolymerLoopZ γ) := by
  have h_list : ∀ jumps : List (WorldlineJumpMonomer L q_code),
      worldlineJumpListFlip D_field jumps =
        staticCSSPauliFlip D_field (jumps.map (fun ξ => ξ.2.1)).sum
          (jumps.map (fun ξ => ξ.2.2)).sum := by
    intro jumps
    induction jumps with
    | nil =>
      have h0 : staticCSSPauliFlip D_field 0 0 = fun _ => false :=
        (Finset.mem_filter.mp (zero_mem_syndromeClosedPauliFinset_and_sum_inv D_field 0).1).2
      change (fun _ => false) = staticCSSPauliFlip D_field 0 0
      exact h0.symm
    | cons hd tl ih =>
      let X_tl := (tl.map (fun ξ => ξ.2.1)).sum
      let Z_tl := (tl.map (fun ξ => ξ.2.2)).sum
      change syndromeXor (staticCSSPauliFlip D_field hd.2.1 hd.2.2)
          (worldlineJumpListFlip D_field tl) =
        staticCSSPauliFlip D_field (hd.2.1 + X_tl) (hd.2.2 + Z_tl)
      rw [ih]
      ext c
      exact (congr_fun (staticCSSPauliFlip_add D_field hd.2.1 X_tl hd.2.2 Z_tl) c).symm
  exact h_list γ.1

/-- **Vanishing of Open-Trajectory Sector Traces**
(Part II, Section 3.5 (`subsec:worldline-expansion`), Equation `eq:local-pauli-jump-xi`, and Lemma 3.9 (`lem:worldline-factorization-time-reversal`)):
For any list of jump monomers `jumps`, any realizable syndrome `σ₀ ∈ realizableSyndromes D_field`,
and any operator `U` that commutes with `sys.syndromeProjector σ₀`: if the net syndrome shift
`worldlineJumpListFlip D_field jumps` is non-zero, then the diagonal sector block
`sys.syndromeProjector σ₀ * (U * (jumps.reverse.map (worldlineSyndromeShiftBlockOp D_field sys V)).prod * sys.syndromeProjector σ₀)`
vanishes identically. -/
lemma syndromeProjector_mul_commute_mul_prod_jump_eq_zero_of_flip_ne_zero
    {L q_code r_0 m_max : ℕ}
    (D_field : Box3D L → LocalCSSDescriptor q_code r_0 m_max)
    (sys : SysCSS[L, q_code, m_max])
    (V : QuasiLocalPerturbation 3 L (SiteCSS[L, q_code]))
    (jumps : List (WorldlineJumpMonomer L q_code))
    {σ₀ : IdxCSS[L, q_code, m_max] → Bool}
    (hσ₀ : σ₀ ∈ realizableSyndromes D_field)
    (U : ℬ_CSS[L, q_code])
    (hU_comm : Commute (sys.syndromeProjector σ₀) U)
    (h_open : worldlineJumpListFlip D_field jumps ≠ (fun _ => false)) :
    sys.syndromeProjector σ₀ *
      (U * (jumps.reverse.map (worldlineSyndromeShiftBlockOp D_field sys V)).prod *
        sys.syndromeProjector σ₀) = 0 := by
  have h_res := PerturbedThermalBarrier.syndrome_resolution_indexed sys
  have h_abs := list_prod_reverse_worldlineSyndromeShiftBlockOp_mul_syndromeProjector
    D_field sys V jumps σ₀ hσ₀
  let σ_end := syndromeXor (worldlineJumpListFlip D_field jumps) σ₀
  have h_ne_σ : σ₀ ≠ σ_end := by
    intro h_eq
    apply h_open
    ext c
    have hc := congr_fun h_eq c
    dsimp [σ_end, syndromeXor] at hc
    cases h_fl : worldlineJumpListFlip D_field jumps c <;>
      cases h0 : σ₀ c <;> rw [h_fl, h0] at hc <;> cases hc
  let W_prod := (jumps.reverse.map (worldlineSyndromeShiftBlockOp D_field sys V)).prod
  have h_orth :
      sys.syndromeProjector σ₀ * (W_prod * sys.syndromeProjector σ₀) = 0 := by
    calc sys.syndromeProjector σ₀ * (W_prod * sys.syndromeProjector σ₀)
      _ = sys.syndromeProjector σ₀ *
            (sys.syndromeProjector σ_end * (W_prod * sys.syndromeProjector σ₀)) := by
            rw [h_abs]
      _ = (sys.syndromeProjector σ₀ * sys.syndromeProjector σ_end) *
            (W_prod * sys.syndromeProjector σ₀) := by
            simp only [mul_assoc]
      _ = 0 := by rw [h_res.2.2.1 σ₀ σ_end h_ne_σ, zero_mul]
  change sys.syndromeProjector σ₀ * (U * W_prod * sys.syndromeProjector σ₀) = 0
  calc sys.syndromeProjector σ₀ * (U * W_prod * sys.syndromeProjector σ₀)
    _ = (sys.syndromeProjector σ₀ * U) * (W_prod * sys.syndromeProjector σ₀) := by
          simp only [mul_assoc]
    _ = U * (sys.syndromeProjector σ₀ * (W_prod * sys.syndromeProjector σ₀)) := by
          rw [hU_comm.eq, mul_assoc]
    _ = 0 := by rw [h_orth, mul_zero]

/-- Normalized loop-amplitude reconstruction identity (Part II, Lemma 2.8(i)–(ii) (`lem:worldline-factorization-time-reversal`), Equation `eq:P-gamma-spanning-surface`). -/
lemma spanningSurfaceSign_mul_worldlinePolymerLoopAmplitude_eq
    {L q_code r_0 m_max : ℕ} [NeZero L]
    (D_field : Box3D L → LocalCSSDescriptor q_code r_0 m_max)
    (sys : SysCSS[L, q_code, m_max]) (C_RCA : ℝ)
    (V : QuasiLocalPerturbation 3 L (SiteCSS[L, q_code]))
    (γ : WorldlineDysonPolymer L q_code) (σ₀ : IdxCSS[L, q_code, m_max] → Bool) :
    let σ_rep := canonicalCollarRealizableSyndrome D_field
      (worldlinePolymerNativeCollar sys C_RCA γ) σ₀
    let μ := worldlinePolymerLogicalCoset D_field sys C_RCA γ
    let B_prod := (hermitianPauliZX μ.1 μ.2)† * worldlinePolymerWeightedLoopOp D_field sys V γ
    spanningSurfaceSign (worldlinePolymerSpanningSurface D_field sys C_RCA γ) σ_rep *
      worldlinePolymerLoopAmplitude D_field sys C_RCA V γ σ₀ =
    hilbertTrace (sys.syndromeProjector σ_rep * B_prod) /
      hilbertTrace (sys.syndromeProjector σ_rep) := by
  intro σ_rep μ B_prod
  unfold worldlinePolymerLoopAmplitude; (try dsimp only)
  have h_sq := (spanningSurfaceSign_insert_and_identities
    (worldlinePolymerSpanningSurface D_field sys C_RCA γ) σ_rep).2.1
  calc spanningSurfaceSign (worldlinePolymerSpanningSurface D_field sys C_RCA γ) σ_rep *
        (spanningSurfaceSign (worldlinePolymerSpanningSurface D_field sys C_RCA γ) σ_rep *
          hilbertTrace (sys.syndromeProjector σ_rep * B_prod) /
          hilbertTrace (sys.syndromeProjector σ_rep))
    _ = (spanningSurfaceSign (worldlinePolymerSpanningSurface D_field sys C_RCA γ) σ_rep *
          spanningSurfaceSign (worldlinePolymerSpanningSurface D_field sys C_RCA γ) σ_rep) *
          hilbertTrace (sys.syndromeProjector σ_rep * B_prod) /
          hilbertTrace (sys.syndromeProjector σ_rep) := by ring
    _ = hilbertTrace (sys.syndromeProjector σ_rep * B_prod) /
          hilbertTrace (sys.syndromeProjector σ_rep) := by rw [h_sq, one_mul]

/-- Additivity of monomer supports, native check collars, and net loop bitstrings under
concatenation (Part II, Lemma 3.9 (`lem:worldline-factorization-time-reversal`)). -/
lemma worldlinePolymerMonomers_append_and_union_eq
    {L q_code m_max : ℕ} [NeZero L]
    (sys : SysCSS[L, q_code, m_max]) (C_RCA : ℝ) (γ₁ γ₂ : WorldlineDysonPolymer L q_code) :
    let γ_tot : WorldlineDysonPolymer L q_code := (γ₁.1 ++ γ₂.1, γ₁.2 ∪ γ₂.2)
    worldlinePolymerMonomers γ_tot = worldlinePolymerMonomers γ₁ ∪ worldlinePolymerMonomers γ₂ ∧
    worldlinePolymerNativeCollar sys C_RCA γ_tot =
      worldlinePolymerNativeCollar sys C_RCA γ₁ ∪ worldlinePolymerNativeCollar sys C_RCA γ₂ ∧
    worldlinePolymerLoopX γ_tot = worldlinePolymerLoopX γ₁ + worldlinePolymerLoopX γ₂ ∧
    worldlinePolymerLoopZ γ_tot = worldlinePolymerLoopZ γ₁ + worldlinePolymerLoopZ γ₂ := by
  intro γ_tot
  have h_mon : worldlinePolymerMonomers γ_tot =
      worldlinePolymerMonomers γ₁ ∪ worldlinePolymerMonomers γ₂ := by
    unfold worldlinePolymerMonomers; dsimp only [γ_tot]
    rw [List.map_append, List.toFinset_append]; ext p; simp only [Finset.mem_union]; tauto
  refine ⟨h_mon, ?_, ?_, ?_⟩
  · unfold worldlinePolymerNativeCollar nativeCollarSupport; rw [h_mon]; ext c
    simp only [Finset.mem_biUnion, Finset.mem_union]
    constructor
    · rintro ⟨p, hp₁ | hp₂, hc⟩
      · exact Or.inl ⟨p, hp₁, hc⟩
      · exact Or.inr ⟨p, hp₂, hc⟩
    · rintro (⟨p, hp₁, hc⟩ | ⟨p, hp₂, hc⟩)
      · exact ⟨p, Or.inl hp₁, hc⟩
      · exact ⟨p, Or.inr hp₂, hc⟩
  · unfold worldlinePolymerLoopX; dsimp only [γ_tot]; rw [List.map_append, List.sum_append]
  · unfold worldlinePolymerLoopZ; dsimp only [γ_tot]; rw [List.map_append, List.sum_append]

/-- Disjoint-collar additivity of `sys.syndromeEnergy` under `syndromeXor`
(Part II, Lemma 3.9 (`lem:worldline-factorization-time-reversal`), Equation `eq:energy-additivity-disjoint-loops`):
when `δ₁` is supported in `S₁`, `δ₂` is supported in `S₂`, and `Disjoint S₁ S₂`, the bare
syndrome energy increment of `syndromeXor δ₁ (syndromeXor δ₂ σ₀)` over `σ₀` splits additively. -/
lemma syndromeEnergy_syndromeXor_disjoint_sets_add
    {L q_code m_max : ℕ} [NeZero L]
    (sys : SysCSS[L, q_code, m_max])
    (σ₀ δ₁ δ₂ : IdxCSS[L, q_code, m_max] → Bool)
    {S₁ S₂ : Finset (IdxCSS[L, q_code, m_max])}
    (h_disj : Disjoint S₁ S₂)
    (h₁ : ∀ c, δ₁ c = true → c ∈ S₁)
    (h₂ : ∀ c, δ₂ c = true → c ∈ S₂) :
    sys.syndromeEnergy (syndromeXor δ₁ (syndromeXor δ₂ σ₀)) - sys.syndromeEnergy σ₀ =
      (sys.syndromeEnergy (syndromeXor δ₁ σ₀) - sys.syndromeEnergy σ₀) +
        (sys.syndromeEnergy (syndromeXor δ₂ σ₀) - sys.syndromeEnergy σ₀) := by
  have h_comm : ∀ a b : IdxCSS[L, q_code, m_max] → Bool, syndromeXor a b = syndromeXor b a := by
    intro a b; ext c; unfold syndromeXor; cases a c <;> cases b c <;> rfl
  have h_assoc : syndromeXor δ₁ (syndromeXor δ₂ σ₀) = syndromeXor (syndromeXor σ₀ δ₁) δ₂ := by
    ext c; unfold syndromeXor; cases δ₁ c <;> cases δ₂ c <;> cases σ₀ c <;> rfl
  rw [h_assoc, h_comm δ₁ σ₀, h_comm δ₂ σ₀]
  refine syndromeEnergy_syndromeXor_disjoint_add sys σ₀ δ₁ δ₂ fun c hc₁ => ?_
  cases h_c₂ : δ₂ c
  · rfl
  · exact False.elim (Finset.disjoint_left.mp h_disj (h₁ c hc₁) (h₂ c h_c₂))

/-- **Footprint Fiber Summation of `worldlineUrsellPhi` over `worldlineUrsellIndexFinset`**
(Part II, Proposition 3.10(i) (`prop:tube-local-ursell-erasure`), Equation `eq:ursell-partition-sigma`):
Whenever the cluster Ursell weight is absolutely summable over valid Ursell clusters `K`,
summing `worldlineUrsellPhi D_field sys C_RCA R_cut β V d_loc ν γ_f σ` over the finite
footprint index set `worldlineUrsellIndexFinset L q_code m_max R_cut` recovers the full
tsum over all valid Ursell clusters `K`. -/
lemma sum_worldlineUrsellIndexFinset_worldlineUrsellPhi_eq_tsum_of_summable
    {L q_code r_0 m_max R_cut : ℕ} [NeZero L]
    (D_field : Box3D L → LocalCSSDescriptor q_code r_0 m_max)
    (sys : SysCSS[L, q_code, m_max]) (C_RCA β : ℝ)
    (V : QuasiLocalPerturbation 3 L (SiteCSS[L, q_code]))
    (d_loc : ℕ → Finset (Box3D L) → (IdxCSS[L, q_code, m_max] → Bool) → ℝ)
    (ν : PauliBitstringPair L q_code)
    (σ : IdxCSS[L, q_code, m_max] → Bool)
    (h_sum : Summable (fun K : WorldlineUrsellCluster L q_code =>
      if IsValidWorldlineUrsellCluster D_field sys C_RCA R_cut K then
        |worldlineClusterUrsellWeight D_field sys C_RCA β V d_loc ν K σ|
      else 0)) :
    (∑ γ_f ∈ worldlineUrsellIndexFinset L q_code m_max R_cut,
      worldlineUrsellPhi D_field sys C_RCA R_cut β V d_loc ν γ_f σ) =
    ∑' K : WorldlineUrsellCluster L q_code,
      if IsValidWorldlineUrsellCluster D_field sys C_RCA R_cut K then
        worldlineClusterUrsellWeight D_field sys C_RCA β V d_loc ν K σ
      else 0 := by
  have h_fiber_summable : ∀ γ_f ∈ worldlineUrsellIndexFinset L q_code m_max R_cut,
      Summable (fun K : WorldlineUrsellCluster L q_code =>
        if IsValidWorldlineUrsellCluster D_field sys C_RCA R_cut K ∧
            worldlineClusterMonomers K = γ_f.1 ∧
            worldlineClusterSpanningSurface D_field sys C_RCA K = γ_f.2 then
          worldlineClusterUrsellWeight D_field sys C_RCA β V d_loc ν K σ
        else 0) := by
    intro γ_f _
    refine Summable.of_norm_bounded h_sum fun K => ?_
    rw [Real.norm_eq_abs]
    split_ifs with h1 h2
    · exact le_rfl
    · exact False.elim (h2 h1.1)
    · rw [abs_zero]
      exact abs_nonneg _
    · rw [abs_zero]
  unfold worldlineUrsellPhi
  rw [← Summable.tsum_finsetSum h_fiber_summable]
  exact tsum_congr fun K =>
    sum_worldlineUrsellIndexFinset_ite_eq_ite_valid D_field sys C_RCA β V d_loc ν σ K

/-- **Vanishing of `ursellConnectedGraphCoeff` on Disconnected Polymer Clusters**
(Part II, Proposition 3.10(i) (`prop:tube-local-ursell-erasure`), Equation `eq:ursell-partition-sigma`):
Whenever `K` is not connected under `polymerClusterOverlap sys C_RCA K`, no spanning subgraph
`G ⊆ E_compat(K)` can be connected on `Finset.univ`, so `ursellConnectedGraphCoeff sys C_RCA K = 0`
and `worldlineClusterUrsellWeight` automatically vanishes without requiring an explicit connectivity
`if`-filter. -/
lemma ursellConnectedGraphCoeff_eq_zero_of_not_connected_and_valid_ite_eq
    {L q_code r_0 m_max R_cut : ℕ} [NeZero L]
    (D_field : Box3D L → LocalCSSDescriptor q_code r_0 m_max)
    (sys : SysCSS[L, q_code, m_max]) (C_RCA β : ℝ)
    (V : QuasiLocalPerturbation 3 L (SiteCSS[L, q_code]))
    (d_loc : ℕ → Finset (Box3D L) → (IdxCSS[L, q_code, m_max] → Bool) → ℝ)
    (ν : PauliBitstringPair L q_code)
    (σ : IdxCSS[L, q_code, m_max] → Bool)
    (K : WorldlineUrsellCluster L q_code) :
    (¬KPIsConnectedSubgraph (PolymerClusterOverlap sys C_RCA K) Finset.univ →
      ursellConnectedGraphCoeff sys C_RCA K = 0) ∧
    ((if IsValidWorldlineUrsellCluster D_field sys C_RCA R_cut K then
        worldlineClusterUrsellWeight D_field sys C_RCA β V d_loc ν K σ
      else 0) =
      if K ≠ [] ∧ (∀ γ ∈ K, IsValidWorldlinePolymer D_field sys C_RCA R_cut γ) then
        worldlineClusterUrsellWeight D_field sys C_RCA β V d_loc ν K σ
      else 0) := by
  have h_zero : ¬KPIsConnectedSubgraph (PolymerClusterOverlap sys C_RCA K) Finset.univ →
      ursellConnectedGraphCoeff sys C_RCA K = 0 := by
    intro h_not_conn
    unfold ursellConnectedGraphCoeff
    (try dsimp only)
    let E_compat : Finset (Fin K.length × Fin K.length) :=
      Finset.univ.filter (fun e => e.1 < e.2 ∧ PolymerClusterOverlap sys C_RCA K e.1 e.2)
    have h_filt_empty :
        E_compat.powerset.filter (fun G =>
          KPIsConnectedSubgraph (fun a b => (a, b) ∈ G ∨ (b, a) ∈ G) Finset.univ) = ∅ := by
      refine Finset.filter_eq_empty_iff.mpr fun G hG hG_conn => h_not_conn ?_
      have hG_sub := Finset.mem_powerset.mp hG
      have h_edge_imp : ∀ a b : Fin K.length,
          ((a, b) ∈ G ∨ (b, a) ∈ G) → PolymerClusterOverlap sys C_RCA K a b := by
        intro a b hab
        rcases hab with hab | hba
        · exact (Finset.mem_filter.mp (hG_sub hab)).2.2
        · rcases (Finset.mem_filter.mp (hG_sub hba)).2.2 with ⟨hne, h_ndisj⟩
          exact ⟨hne.symm, fun h_disj => h_ndisj h_disj.symm⟩
      refine ⟨hG_conn.1, fun u hu v hv => ?_⟩
      exact Relation.ReflTransGen.mono
        (fun a b h => ⟨h.1, h.2.1, h_edge_imp a b h.2.2⟩) u v (hG_conn.2 u hu v hv)
    rw [h_filt_empty, Finset.sum_empty, mul_zero]
  refine ⟨h_zero, ?_⟩
  unfold IsValidWorldlineUrsellCluster
  by_cases h_base : K ≠ [] ∧ ∀ γ ∈ K, IsValidWorldlinePolymer D_field sys C_RCA R_cut γ
  · by_cases h_conn : KPIsConnectedSubgraph (PolymerClusterOverlap sys C_RCA K) Finset.univ
    · rw [if_pos ⟨h_base.1, h_base.2, h_conn⟩, if_pos h_base]
    · rw [if_neg (fun h => h_conn h.2.2), if_pos h_base]
      unfold worldlineClusterUrsellWeight
      rw [h_zero h_conn, zero_mul]
  · rw [if_neg (fun h => h_base ⟨h.1, h.2.1⟩), if_neg h_base]

/-- **Site/Slot Disjointness from Disjoint Check Collars**
(Part II, Lemma 3.9(i) (`lem:worldline-factorization-time-reversal`)):
For any two scale-cubes `(r₁, A₁), (r₂, A₂)` with `A₁ ∈ BoxCubes 3 L r₁` and `A₂ ∈ BoxCubes 3 L r₂`,
if `1 ≤ C_RCA` and their check collars `rcaCollarChecks sys C_RCA r₁ A₁` and
`rcaCollarChecks sys C_RCA r₂ A₂` are disjoint, then no code slot `slot : BoxSlot3D L q_code`
can have `slot.1 ∈ A₁` and `slot.1 ∈ A₂`. -/
lemma slot_disjoint_of_disjoint_rcaCollarChecks
    {L q_code r_0 m_max : ℕ} [NeZero L]
    (D_field : Box3D L → LocalCSSDescriptor q_code r_0 m_max)
    (sys : SysCSS[L, q_code, m_max])
    (h_sys_supp : ∀ idx, sys.support idx = staticCSSCheckSupport D_field idx)
    {C_RCA : ℝ} (hC_RCA : 1 ≤ C_RCA)
    {r₁ r₂ : ℕ} {A₁ A₂ : Finset (Box3D L)}
    (hA₁ : A₁ ∈ boxCubes 3 L r₁) (hA₂ : A₂ ∈ boxCubes 3 L r₂)
    (h_disj : Disjoint (rcaCollarChecks sys C_RCA r₁ A₁) (rcaCollarChecks sys C_RCA r₂ A₂))
    (slot : BoxSlot3D L q_code)
    (h₁ : slot.1 ∈ A₁) :
    slot.1 ∉ A₂ := by
  intro h₂
  let c : IdxCSS[L, q_code, m_max] := Sum.inl slot
  have hc_supp : sys.support c = {slot.1} := by
    rw [h_sys_supp c]
    rfl
  have h_sub : ∀ (r : ℕ) (A : Finset (Box3D L)),
      A ∈ boxCubes 3 L r → A ⊆ rcaCollarCube C_RCA r A := by
    intro r A hA v hv
    have hr_le : r ≤ linearExpansionRadius C_RCA r := by
      unfold linearExpansionRadius
      have h_mul : (r : ℝ) ≤ C_RCA * (r : ℝ) := by
        calc (r : ℝ) = 1 * (r : ℝ) := (one_mul _).symm
          _ ≤ C_RCA * (r : ℝ) := mul_le_mul_of_nonneg_right hC_RCA (Nat.cast_nonneg r)
      have h_ceil : (r : ℝ) ≤ ((⌈C_RCA * (r : ℝ)⌉₊ : ℕ) : ℝ) :=
        h_mul.trans (Nat.le_ceil (C_RCA * (r : ℝ)))
      exact_mod_cast h_ceil
    unfold rcaCollarCube enclosingBoxCube
    rw [← boxCube_anchorOfCube hA] at hv
    simp only [boxCube, Finset.mem_filter, Finset.mem_univ, true_and] at hv ⊢
    intro i
    have hvi := hv i
    omega
  have hc₁ : c ∈ rcaCollarChecks sys C_RCA r₁ A₁ := by
    unfold rcaCollarChecks
    rw [Finset.mem_filter]
    refine ⟨Finset.mem_univ c, ?_⟩
    rw [hc_supp, Finset.singleton_subset_iff]
    exact h_sub r₁ A₁ hA₁ h₁
  have hc₂ : c ∈ rcaCollarChecks sys C_RCA r₂ A₂ := by
    unfold rcaCollarChecks
    rw [Finset.mem_filter]
    refine ⟨Finset.mem_univ c, ?_⟩
    rw [hc_supp, Finset.singleton_subset_iff]
    exact h_sub r₂ A₂ hA₂ h₂
  exact Finset.disjoint_left.mp h_disj hc₁ hc₂

/-- Commutation of Weyl–Pauli operators `weylPauliZ a₁ * weylPauliX b₁` and `weylPauliZ a₂ * weylPauliX b₂`
supported on scale-cubes with disjoint slots (Part II, Lemma 3.9(i) (`lem:worldline-factorization-time-reversal`)). -/
lemma weylPauliZX_comm_of_disjoint_slot_support
    {L q_code : ℕ}
    {A₁ A₂ : Finset (Box3D L)}
    (h_slot_disj : ∀ slot : BoxSlot3D L q_code, slot.1 ∈ A₁ → slot.1 ∉ A₂)
    (a₁ b₁ a₂ b₂ : BoxSlot3D L q_code → ZMod 2)
    (h₁ : ∀ slot : BoxSlot3D L q_code, a₁ slot ≠ 0 ∨ b₁ slot ≠ 0 → slot.1 ∈ A₁)
    (h₂ : ∀ slot : BoxSlot3D L q_code, a₂ slot ≠ 0 ∨ b₂ slot ≠ 0 → slot.1 ∈ A₂) :
    Commute (weylPauliZ a₁ * weylPauliX b₁) (weylPauliZ a₂ * weylPauliX b₂) := by
  have h_symp : (∑ slot : BoxSlot3D L q_code, (a₂ slot * b₁ slot + a₁ slot * b₂ slot)) = 0 := by
    refine Finset.sum_eq_zero fun slot _ => ?_
    by_cases h_in₁ : slot.1 ∈ A₁
    · have h_not₂ : slot.1 ∉ A₂ := h_slot_disj slot h_in₁
      have ha₂ : a₂ slot = 0 := by_contra fun hne => h_not₂ (h₂ slot (Or.inl hne))
      have hb₂ : b₂ slot = 0 := by_contra fun hne => h_not₂ (h₂ slot (Or.inr hne))
      rw [ha₂, hb₂]; ring
    · have ha₁ : a₁ slot = 0 := by_contra fun hne => h_in₁ (h₁ slot (Or.inl hne))
      have hb₁ : b₁ slot = 0 := by_contra fun hne => h_in₁ (h₁ slot (Or.inr hne))
      rw [ha₁, hb₁]; ring
  rw [commute_iff_eq, weylPauliZX_comm_signScalar a₁ b₁ a₂ b₂, h_symp, signScalar_zero, one_smul]

/-- Commutation of finite linear combinations of Weyl–Pauli operators supported on scale-cubes
`(r₁, A₁)` and `(r₂, A₂)` with disjoint `rcaCollarChecks` (Part II, Lemma 3.9(i) (`lem:worldline-factorization-time-reversal`)). -/
lemma commute_weylPauli_sum_of_disjoint_rcaCollarChecks
    {L q_code r_0 m_max : ℕ} [NeZero L]
    (D_field : Box3D L → LocalCSSDescriptor q_code r_0 m_max)
    (sys : SysCSS[L, q_code, m_max])
    (h_sys_supp : ∀ idx, sys.support idx = staticCSSCheckSupport D_field idx)
    {C_RCA : ℝ} (hC_RCA : 1 ≤ C_RCA)
    {r₁ r₂ : ℕ} {A₁ A₂ : Finset (Box3D L)}
    (hA₁ : A₁ ∈ boxCubes 3 L r₁) (hA₂ : A₂ ∈ boxCubes 3 L r₂)
    (h_disj : Disjoint (rcaCollarChecks sys C_RCA r₁ A₁) (rcaCollarChecks sys C_RCA r₂ A₂))
    {ι₁ ι₂ : Type*} (S₁ : Finset ι₁) (S₂ : Finset ι₂)
    (w₁ : ι₁ → ℂ) (w₂ : ι₂ → ℂ)
    (a₁ b₁ : ι₁ → BoxSlot3D L q_code → ZMod 2)
    (a₂ b₂ : ι₂ → BoxSlot3D L q_code → ZMod 2)
    (h_supp₁ : ∀ i ∈ S₁, ∀ slot : BoxSlot3D L q_code, a₁ i slot ≠ 0 ∨ b₁ i slot ≠ 0 → slot.1 ∈ A₁)
    (h_supp₂ : ∀ j ∈ S₂, ∀ slot : BoxSlot3D L q_code, a₂ j slot ≠ 0 ∨ b₂ j slot ≠ 0 → slot.1 ∈ A₂) :
    Commute
      (∑ i ∈ S₁, w₁ i • (weylPauliZ (a₁ i) * weylPauliX (b₁ i)))
      (∑ j ∈ S₂, w₂ j • (weylPauliZ (a₂ j) * weylPauliX (b₂ j))) := by
  have h_slot_disj : ∀ slot : BoxSlot3D L q_code, slot.1 ∈ A₁ → slot.1 ∉ A₂ :=
    slot_disjoint_of_disjoint_rcaCollarChecks D_field sys h_sys_supp hC_RCA hA₁ hA₂ h_disj
  refine Commute.sum_left _ _ _ fun i hi => ?_
  refine Commute.sum_right _ _ _ fun j hj => ?_
  exact (weylPauliZX_comm_of_disjoint_slot_support h_slot_disj
    (a₁ i) (b₁ i) (a₂ j) (b₂ j) (h_supp₁ i hi) (h_supp₂ j hj)).smul_left (w₁ i) |>.smul_right (w₂ j)

/-- Local Weyl–Pauli expansion of `worldlineSyndromeShiftBlockOp D_field sys V ξ` on realizable
syndrome sectors (Part II, Proposition 3.4(iii) (`prop:pauli-diag-off`), Equation `eq:V-off-jump-decomp`,
and Section 3.5 (`subsec:worldline-expansion`), Equation `eq:local-pauli-jump-xi`):
whenever `V.term ξ.1.1 ξ.1.2` is supported on `ξ.1.2` and `staticCSSPauliFlip D_field ξ.2.1 ξ.2.2 ≠ (fun _ => false)`,
there exists a finite Weyl–Pauli sum `M = ∑ i ∈ S, w i • (weylPauliZ (a_fam i) * weylPauliX (b_fam i))`
whose bitstrings are supported on `ξ.1.2` and have syndrome shift `staticCSSPauliFlip D_field ξ.2.1 ξ.2.2`,
such that `worldlineSyndromeShiftBlockOp D_field sys V ξ * sys.syndromeProjector σ₀ = M * sys.syndromeProjector σ₀`
for every `σ₀ ∈ realizableSyndromes D_field`. -/
lemma exists_weylPauli_expansion_worldlineSyndromeShiftBlockOp_mul_syndromeProjector
    {L q_code r_0 m_max : ℕ}
    (D_field : Box3D L → LocalCSSDescriptor q_code r_0 m_max)
    (sys : SysCSS[L, q_code, m_max])
    (h_sys_checks : ∀ idx, sys.checkProj idx = staticCSSCheckProj D_field idx ∧
      sys.support idx = staticCSSCheckSupport D_field idx ∧ sys.weight idx = 1)
    (V : QuasiLocalPerturbation 3 L (SiteCSS[L, q_code]))
    (ξ : WorldlineJumpMonomer L q_code)
    (hV_supp : IsSupportedOn (SiteCSS[L, q_code]) ξ.1.2 (V.term ξ.1.1 ξ.1.2))
    (h_ne_zero : staticCSSPauliFlip D_field ξ.2.1 ξ.2.2 ≠ (fun _ => false)) :
    ∃ (ι : Type) (_ : Fintype ι) (S : Finset ι) (w : ι → ℂ)
      (a_fam b_fam : ι → BoxSlot3D L q_code → ZMod 2),
      (∀ i ∈ S, ∀ slot : BoxSlot3D L q_code, a_fam i slot ≠ 0 ∨ b_fam i slot ≠ 0 → slot.1 ∈ ξ.1.2) ∧
      (∀ i ∈ S, staticCSSPauliFlip D_field (a_fam i) (b_fam i) =
        staticCSSPauliFlip D_field ξ.2.1 ξ.2.2) ∧
      (∀ σ₀ ∈ realizableSyndromes D_field,
        worldlineSyndromeShiftBlockOp D_field sys V ξ * sys.syndromeProjector σ₀ =
          (∑ i ∈ S, w i • (weylPauliZ (a_fam i) * weylPauliX (b_fam i))) *
            sys.syndromeProjector σ₀) := by
  rcases exists_local_weylPauli_expansion_on_cube ξ.1.2 hV_supp with
    ⟨ι, _, w, a_fam, b_fam, h_supp_fam, hV_exp⟩
  let δ := staticCSSPauliFlip D_field ξ.2.1 ξ.2.2
  let S : Finset ι := Finset.univ.filter (fun i => staticCSSPauliFlip D_field (a_fam i) (b_fam i) = δ)
  refine ⟨ι, inferInstance, S, w, a_fam, b_fam,
    fun i _ => h_supp_fam i,
    fun i hi => (Finset.mem_filter.mp hi).2,
    fun σ₀ hσ₀ => ?_⟩
  have h_res := PerturbedThermalBarrier.syndrome_resolution_indexed sys
  have h_act := (worldlineSyndromeShiftBlockOp_mul_syndromeProjector D_field sys V ξ σ₀).1
  (try dsimp only at h_act)
  rw [h_act, if_pos hσ₀]
  have h_ne_σ : syndromeXor δ σ₀ ≠ σ₀ := by
    intro h_eq
    apply h_ne_zero
    ext c
    have hc := congr_fun h_eq c
    dsimp [syndromeXor] at hc
    change δ c = false
    revert hc
    cases δ c <;> cases σ₀ c <;> decide
  rw [syndromeProjector_mul_pauliOffDiagonalTerm_mul_syndromeProjector,
    if_neg h_ne_σ, hV_exp, Finset.mul_sum, Finset.sum_mul, Finset.sum_mul]
  have h_term : ∀ i : ι,
      sys.syndromeProjector (syndromeXor δ σ₀) *
        (w i • (weylPauliZ (a_fam i) * weylPauliX (b_fam i))) *
        sys.syndromeProjector σ₀ =
      if staticCSSPauliFlip D_field (a_fam i) (b_fam i) = δ then
        (w i • (weylPauliZ (a_fam i) * weylPauliX (b_fam i))) * sys.syndromeProjector σ₀
      else 0 := by
    intro i
    have h_flip_i : ∀ idx,
        (weylPauliZ (a_fam i) * weylPauliX (b_fam i)) * sys.checkProj idx =
          (if staticCSSPauliFlip D_field (a_fam i) (b_fam i) idx then
            1 - sys.checkProj idx
          else sys.checkProj idx) *
            (weylPauliZ (a_fam i) * weylPauliX (b_fam i)) := fun idx => by
      rw [(h_sys_checks idx).1]
      exact weylPauliZX_mul_staticCSSCheckProj D_field (a_fam i) (b_fam i) idx
    have h_inter := intertwine_syndromeProjector_of_checkFlip sys h_flip_i σ₀
    have h_xor_eq :
        (fun idx => xor (σ₀ idx) (staticCSSPauliFlip D_field (a_fam i) (b_fam i) idx)) =
          syndromeXor (staticCSSPauliFlip D_field (a_fam i) (b_fam i)) σ₀ := by
      ext idx
      change bne (σ₀ idx) (staticCSSPauliFlip D_field (a_fam i) (b_fam i) idx) =
        bne (staticCSSPauliFlip D_field (a_fam i) (b_fam i) idx) (σ₀ idx)
      cases σ₀ idx <;> cases staticCSSPauliFlip D_field (a_fam i) (b_fam i) idx <;> rfl
    rw [h_xor_eq] at h_inter
    rw [clm_mul_smul, clm_smul_mul, mul_assoc, h_inter, ← mul_assoc]
    by_cases h_eq : staticCSSPauliFlip D_field (a_fam i) (b_fam i) = δ
    · rw [if_pos h_eq, h_eq, (h_res.2.1 (syndromeXor δ σ₀)).1, ← h_eq, ← h_inter, ← clm_smul_mul]
    · have h_ne_shift :
          syndromeXor δ σ₀ ≠
            syndromeXor (staticCSSPauliFlip D_field (a_fam i) (b_fam i)) σ₀ := by
        intro h_eq_shift
        apply h_eq
        ext c
        have hc := congr_fun h_eq_shift c
        dsimp [syndromeXor] at hc
        revert hc
        cases staticCSSPauliFlip D_field (a_fam i) (b_fam i) c <;>
          cases δ c <;> cases σ₀ c <;> decide
      rw [if_neg h_eq, h_res.2.2.1 _ _ h_ne_shift, zero_mul, smul_zero]
  rw [Finset.sum_congr rfl fun i _ => h_term i, ← Finset.sum_filter]

/-- **Commutation of `worldlineSyndromeShiftBlockOp` for Collar-Disjoint Jump Monomers**
(Part II, Lemma 3.9(i) (`lem:worldline-factorization-time-reversal`)):
Whenever two valid jump monomers `ξ₁, ξ₂` have disjoint `rcaCollarChecks` (`C_RCA ≥ 1`),
their syndrome-shift jump block operators `worldlineSyndromeShiftBlockOp D_field sys V ξ₁`
and `worldlineSyndromeShiftBlockOp D_field sys V ξ₂` commute on every realizable syndrome sector
`σ₀ ∈ realizableSyndromes D_field`. -/
lemma commute_worldlineSyndromeShiftBlockOp_mul_syndromeProjector_of_disjoint_rcaCollarChecks
    {L q_code r_0 m_max : ℕ} [NeZero L]
    (D_field : Box3D L → LocalCSSDescriptor q_code r_0 m_max)
    (sys : SysCSS[L, q_code, m_max])
    (h_sys_checks : ∀ idx, sys.checkProj idx = staticCSSCheckProj D_field idx ∧
      sys.support idx = staticCSSCheckSupport D_field idx ∧ sys.weight idx = 1)
    {C_RCA : ℝ} (hC_RCA : 1 ≤ C_RCA)
    (V : QuasiLocalPerturbation 3 L (SiteCSS[L, q_code]))
    (ξ₁ ξ₂ : WorldlineJumpMonomer L q_code)
    (hA₁ : ξ₁.1.2 ∈ boxCubes 3 L ξ₁.1.1) (hA₂ : ξ₂.1.2 ∈ boxCubes 3 L ξ₂.1.1)
    (hV_supp₁ : IsSupportedOn (SiteCSS[L, q_code]) ξ₁.1.2 (V.term ξ₁.1.1 ξ₁.1.2))
    (hV_supp₂ : IsSupportedOn (SiteCSS[L, q_code]) ξ₂.1.2 (V.term ξ₂.1.1 ξ₂.1.2))
    (h_ne₁ : staticCSSPauliFlip D_field ξ₁.2.1 ξ₁.2.2 ≠ (fun _ => false))
    (h_ne₂ : staticCSSPauliFlip D_field ξ₂.2.1 ξ₂.2.2 ≠ (fun _ => false))
    (h_disj : Disjoint (rcaCollarChecks sys C_RCA ξ₁.1.1 ξ₁.1.2)
      (rcaCollarChecks sys C_RCA ξ₂.1.1 ξ₂.1.2))
    {σ₀ : IdxCSS[L, q_code, m_max] → Bool}
    (hσ₀ : σ₀ ∈ realizableSyndromes D_field) :
    worldlineSyndromeShiftBlockOp D_field sys V ξ₁ *
      (worldlineSyndromeShiftBlockOp D_field sys V ξ₂ * sys.syndromeProjector σ₀) =
    worldlineSyndromeShiftBlockOp D_field sys V ξ₂ *
      (worldlineSyndromeShiftBlockOp D_field sys V ξ₁ * sys.syndromeProjector σ₀) := by
  rcases exists_weylPauli_expansion_worldlineSyndromeShiftBlockOp_mul_syndromeProjector
      D_field sys h_sys_checks V ξ₁ hV_supp₁ h_ne₁ with
    ⟨ι₁, _, S₁, w₁, a₁, b₁, h_supp₁, _, hM₁⟩
  rcases exists_weylPauli_expansion_worldlineSyndromeShiftBlockOp_mul_syndromeProjector
      D_field sys h_sys_checks V ξ₂ hV_supp₂ h_ne₂ with
    ⟨ι₂, _, S₂, w₂, a₂, b₂, h_supp₂, _, hM₂⟩
  let M₁ := ∑ i ∈ S₁, w₁ i • (weylPauliZ (a₁ i) * weylPauliX (b₁ i))
  let M₂ := ∑ j ∈ S₂, w₂ j • (weylPauliZ (a₂ j) * weylPauliX (b₂ j))
  have h_comm : M₁ * M₂ = M₂ * M₁ :=
    (commute_weylPauli_sum_of_disjoint_rcaCollarChecks
      D_field sys (fun idx => (h_sys_checks idx).2.1) hC_RCA hA₁ hA₂ h_disj
      S₁ S₂ w₁ w₂ a₁ b₁ a₂ b₂ h_supp₁ h_supp₂).eq
  let δ₁ := staticCSSPauliFlip D_field ξ₁.2.1 ξ₁.2.2
  let δ₂ := staticCSSPauliFlip D_field ξ₂.2.1 ξ₂.2.2
  have h_mem₁ : syndromeXor δ₁ σ₀ ∈ realizableSyndromes D_field :=
    syndromeXor_staticCSSPauliFlip_mem_realizableSyndromes D_field ξ₁.2.1 ξ₁.2.2 σ₀ hσ₀
  have h_mem₂ : syndromeXor δ₂ σ₀ ∈ realizableSyndromes D_field :=
    syndromeXor_staticCSSPauliFlip_mem_realizableSyndromes D_field ξ₂.2.1 ξ₂.2.2 σ₀ hσ₀
  have h_abs₁ := (worldlineSyndromeShiftBlockOp_mul_syndromeProjector D_field sys V ξ₁ σ₀).2
  have h_abs₂ := (worldlineSyndromeShiftBlockOp_mul_syndromeProjector D_field sys V ξ₂ σ₀).2
  (try dsimp only at h_abs₁ h_abs₂)
  calc worldlineSyndromeShiftBlockOp D_field sys V ξ₁ *
        (worldlineSyndromeShiftBlockOp D_field sys V ξ₂ * sys.syndromeProjector σ₀)
    _ = worldlineSyndromeShiftBlockOp D_field sys V ξ₁ *
          (sys.syndromeProjector (syndromeXor δ₂ σ₀) *
            (worldlineSyndromeShiftBlockOp D_field sys V ξ₂ * sys.syndromeProjector σ₀)) := by
          rw [h_abs₂]
    _ = (worldlineSyndromeShiftBlockOp D_field sys V ξ₁ *
          sys.syndromeProjector (syndromeXor δ₂ σ₀)) *
          (worldlineSyndromeShiftBlockOp D_field sys V ξ₂ * sys.syndromeProjector σ₀) := by
          rw [mul_assoc]
    _ = (M₁ * sys.syndromeProjector (syndromeXor δ₂ σ₀)) *
          (worldlineSyndromeShiftBlockOp D_field sys V ξ₂ * sys.syndromeProjector σ₀) := by
          rw [hM₁ (syndromeXor δ₂ σ₀) h_mem₂]
    _ = M₁ * (sys.syndromeProjector (syndromeXor δ₂ σ₀) *
          (worldlineSyndromeShiftBlockOp D_field sys V ξ₂ * sys.syndromeProjector σ₀)) := by
          rw [mul_assoc]
    _ = M₁ * (worldlineSyndromeShiftBlockOp D_field sys V ξ₂ * sys.syndromeProjector σ₀) := by
          rw [h_abs₂]
    _ = (M₁ * M₂) * sys.syndromeProjector σ₀ := by
          rw [hM₂ σ₀ hσ₀, mul_assoc]
    _ = (M₂ * M₁) * sys.syndromeProjector σ₀ := by
          rw [h_comm]
    _ = M₂ * (worldlineSyndromeShiftBlockOp D_field sys V ξ₁ * sys.syndromeProjector σ₀) := by
          rw [mul_assoc, ← hM₁ σ₀ hσ₀]
    _ = M₂ * (sys.syndromeProjector (syndromeXor δ₁ σ₀) *
          (worldlineSyndromeShiftBlockOp D_field sys V ξ₁ * sys.syndromeProjector σ₀)) := by
          rw [h_abs₁]
    _ = (M₂ * sys.syndromeProjector (syndromeXor δ₁ σ₀)) *
          (worldlineSyndromeShiftBlockOp D_field sys V ξ₁ * sys.syndromeProjector σ₀) := by
          rw [mul_assoc]
    _ = (worldlineSyndromeShiftBlockOp D_field sys V ξ₂ *
          sys.syndromeProjector (syndromeXor δ₁ σ₀)) *
          (worldlineSyndromeShiftBlockOp D_field sys V ξ₁ * sys.syndromeProjector σ₀) := by
          rw [← hM₂ (syndromeXor δ₁ σ₀) h_mem₁]
    _ = worldlineSyndromeShiftBlockOp D_field sys V ξ₂ *
          (sys.syndromeProjector (syndromeXor δ₁ σ₀) *
            (worldlineSyndromeShiftBlockOp D_field sys V ξ₁ * sys.syndromeProjector σ₀)) := by
          rw [mul_assoc]
    _ = worldlineSyndromeShiftBlockOp D_field sys V ξ₂ *
          (worldlineSyndromeShiftBlockOp D_field sys V ξ₁ * sys.syndromeProjector σ₀) := by
          rw [h_abs₁]

/-- Local Weyl–Pauli expansion of the ordered product `(jumps.reverse.map (worldlineSyndromeShiftBlockOp D_field sys V)).prod`
along any jump monomer list `jumps` on realizable syndrome sectors
(Part II, Section 3.5 (`subsec:worldline-expansion`) and Lemma 3.9(i) (`lem:worldline-factorization-time-reversal`)). -/
lemma exists_weylPauli_expansion_list_prod_reverse_worldlineSyndromeShiftBlockOp
    {L q_code r_0 m_max : ℕ}
    (D_field : Box3D L → LocalCSSDescriptor q_code r_0 m_max)
    (sys : SysCSS[L, q_code, m_max])
    (h_sys_checks : ∀ idx, sys.checkProj idx = staticCSSCheckProj D_field idx ∧
      sys.support idx = staticCSSCheckSupport D_field idx ∧ sys.weight idx = 1)
    (V : QuasiLocalPerturbation 3 L (SiteCSS[L, q_code]))
    (jumps : List (WorldlineJumpMonomer L q_code))
    (h_jumps : ∀ ξ ∈ jumps,
      IsSupportedOn (SiteCSS[L, q_code]) ξ.1.2 (V.term ξ.1.1 ξ.1.2) ∧
      staticCSSPauliFlip D_field ξ.2.1 ξ.2.2 ≠ (fun _ => false)) :
    ∃ (ι : Type) (_ : Fintype ι) (S : Finset ι) (w : ι → ℂ)
      (a_fam b_fam : ι → BoxSlot3D L q_code → ZMod 2),
      (∀ i ∈ S, ∀ slot : BoxSlot3D L q_code, a_fam i slot ≠ 0 ∨ b_fam i slot ≠ 0 →
        ∃ ξ ∈ jumps, slot.1 ∈ ξ.1.2) ∧
      (∀ i ∈ S, staticCSSPauliFlip D_field (a_fam i) (b_fam i) =
        worldlineJumpListFlip D_field jumps) ∧
      (∀ σ₀ ∈ realizableSyndromes D_field,
        (jumps.reverse.map (worldlineSyndromeShiftBlockOp D_field sys V)).prod *
          sys.syndromeProjector σ₀ =
        (∑ i ∈ S, w i • (weylPauliZ (a_fam i) * weylPauliX (b_fam i))) *
          sys.syndromeProjector σ₀) := by
  induction jumps with
  | nil =>
    refine ⟨Unit, inferInstance, {()}, fun _ => 1, fun _ => 0, fun _ => 0,
      fun _ _ slot h_ne => ?_, fun _ _ => ?_, fun σ₀ _ => ?_⟩
    · rcases h_ne with h | h <;> exact False.elim (h rfl)
    · ext idx
      rcases idx with ⟨v, s⟩ | ⟨v, i⟩ | ⟨v, i⟩ <;> simp [staticCSSPauliFlip, worldlineJumpListFlip]
    · simp [weylPauliZ_zero, weylPauliX_zero]
  | cons hd tl ih =>
    rcases h_jumps hd List.mem_cons_self with ⟨hV_hd, h_ne_hd⟩
    rcases exists_weylPauli_expansion_worldlineSyndromeShiftBlockOp_mul_syndromeProjector
        D_field sys h_sys_checks V hd hV_hd h_ne_hd with
      ⟨ι₁, _, S₁, w₁, a₁, b₁, h_supp₁, h_flip₁, hM₁⟩
    rcases ih (fun ξ hξ => h_jumps ξ (List.mem_cons_of_mem hd hξ)) with
      ⟨ι₂, _, S₂, w₂, a₂, b₂, h_supp₂, h_flip₂, hM₂⟩
    refine ⟨ι₂ × ι₁, inferInstance, S₂ ×ˢ S₁,
      fun p => w₂ p.1 * w₁ p.2 * signScalar (∑ slot : BoxSlot3D L q_code, a₁ p.2 slot * b₂ p.1 slot),
      fun p => a₂ p.1 + a₁ p.2,
      fun p => b₂ p.1 + b₁ p.2,
      fun p hp slot h_ne => ?_, fun p hp => ?_, fun σ₀ hσ₀ => ?_⟩
    · rcases Finset.mem_product.mp hp with ⟨hp₂, hp₁⟩
      have h_or : (a₂ p.1 slot ≠ 0 ∨ b₂ p.1 slot ≠ 0) ∨ (a₁ p.2 slot ≠ 0 ∨ b₁ p.2 slot ≠ 0) := by
        by_contra! h_all
        rcases h_ne with ha | hb
        · apply ha; change a₂ p.1 slot + a₁ p.2 slot = 0
          rw [h_all.1.1, h_all.2.1, add_zero]
        · apply hb; change b₂ p.1 slot + b₁ p.2 slot = 0
          rw [h_all.1.2, h_all.2.2, add_zero]
      rcases h_or with h₂ | h₁
      · rcases h_supp₂ p.1 hp₂ slot h₂ with ⟨ξ, hξ, h_in⟩
        exact ⟨ξ, List.mem_cons_of_mem hd hξ, h_in⟩
      · exact ⟨hd, List.mem_cons_self, h_supp₁ p.2 hp₁ slot h₁⟩
    · rcases Finset.mem_product.mp hp with ⟨hp₂, hp₁⟩
      rw [staticCSSPauliFlip_add D_field (a₂ p.1) (a₁ p.2) (b₂ p.1) (b₁ p.2),
        h_flip₂ p.1 hp₂, h_flip₁ p.2 hp₁]
      ext c
      change bne (worldlineJumpListFlip D_field tl c)
          (staticCSSPauliFlip D_field hd.2.1 hd.2.2 c) =
        bne (staticCSSPauliFlip D_field hd.2.1 hd.2.2 c)
          (worldlineJumpListFlip D_field tl c)
      cases worldlineJumpListFlip D_field tl c <;>
        cases staticCSSPauliFlip D_field hd.2.1 hd.2.2 c <;> rfl
    · have h_prod_rev :
          ((hd :: tl).reverse.map (worldlineSyndromeShiftBlockOp D_field sys V)).prod =
            (tl.reverse.map (worldlineSyndromeShiftBlockOp D_field sys V)).prod *
              worldlineSyndromeShiftBlockOp D_field sys V hd := by
        rw [List.reverse_cons, List.map_append, List.prod_append, List.map_cons,
          List.map_nil, List.prod_cons, List.prod_nil, mul_one]
      let δ_hd := staticCSSPauliFlip D_field hd.2.1 hd.2.2
      have h_mem_hd : syndromeXor δ_hd σ₀ ∈ realizableSyndromes D_field :=
        syndromeXor_staticCSSPauliFlip_mem_realizableSyndromes D_field hd.2.1 hd.2.2 σ₀ hσ₀
      have h_abs_hd := (worldlineSyndromeShiftBlockOp_mul_syndromeProjector D_field sys V hd σ₀).2
      (try dsimp only at h_abs_hd)
      let M₁ := ∑ i₁ ∈ S₁, w₁ i₁ • (weylPauliZ (a₁ i₁) * weylPauliX (b₁ i₁))
      let M₂ := ∑ i₂ ∈ S₂, w₂ i₂ • (weylPauliZ (a₂ i₂) * weylPauliX (b₂ i₂))
      have h_prod_M : M₂ * M₁ =
          ∑ p ∈ S₂ ×ˢ S₁,
            (w₂ p.1 * w₁ p.2 * signScalar (∑ slot, a₁ p.2 slot * b₂ p.1 slot)) •
              (weylPauliZ (a₂ p.1 + a₁ p.2) * weylPauliX (b₂ p.1 + b₁ p.2)) := by
        dsimp [M₂, M₁]
        rw [Finset.sum_mul_sum, ← Finset.sum_product']
        refine Finset.sum_congr rfl fun p _ => ?_
        rw [clm_smul_mul, clm_mul_smul, weylPauliZX_mul_weylPauliZX, smul_smul, smul_smul, mul_assoc]
      calc ((hd :: tl).reverse.map (worldlineSyndromeShiftBlockOp D_field sys V)).prod *
            sys.syndromeProjector σ₀
        _ = (tl.reverse.map (worldlineSyndromeShiftBlockOp D_field sys V)).prod *
              (sys.syndromeProjector (syndromeXor δ_hd σ₀) *
                (worldlineSyndromeShiftBlockOp D_field sys V hd * sys.syndromeProjector σ₀)) := by
              rw [h_prod_rev, mul_assoc, h_abs_hd]
        _ = ((tl.reverse.map (worldlineSyndromeShiftBlockOp D_field sys V)).prod *
              sys.syndromeProjector (syndromeXor δ_hd σ₀)) *
              (worldlineSyndromeShiftBlockOp D_field sys V hd * sys.syndromeProjector σ₀) := by
              rw [mul_assoc]
        _ = (M₂ * sys.syndromeProjector (syndromeXor δ_hd σ₀)) *
              (worldlineSyndromeShiftBlockOp D_field sys V hd * sys.syndromeProjector σ₀) := by
              rw [hM₂ (syndromeXor δ_hd σ₀) h_mem_hd]
        _ = M₂ * (sys.syndromeProjector (syndromeXor δ_hd σ₀) *
              (worldlineSyndromeShiftBlockOp D_field sys V hd * sys.syndromeProjector σ₀)) := by
              rw [mul_assoc]
        _ = M₂ * (worldlineSyndromeShiftBlockOp D_field sys V hd * sys.syndromeProjector σ₀) := by
              rw [h_abs_hd]
        _ = (M₂ * M₁) * sys.syndromeProjector σ₀ := by
              rw [hM₁ σ₀ hσ₀, mul_assoc]
        _ = (∑ p ∈ S₂ ×ˢ S₁,
              (w₂ p.1 * w₁ p.2 * signScalar (∑ slot, a₁ p.2 slot * b₂ p.1 slot)) •
                (weylPauliZ (a₂ p.1 + a₁ p.2) * weylPauliX (b₂ p.1 + b₁ p.2))) *
              sys.syndromeProjector σ₀ := by
              rw [h_prod_M]

/-- Single-jump $\mathrm{RCA}_1$ collar-scalar factorization: for any jump monomer $\xi$ at scale
$1 \le \xi.1.1 \le L^*$, `worldlineSyndromeShiftBlockOp D_field sys V ξ` acting on any realizable
syndrome projector `sys.syndromeProjector σ₀` equals a collar-local scalar $c_\xi(\sigma_0)$
(depending only on $\sigma_0|_{\mathcal{C}(A_\xi^+)}$) times `worldlineJumpOp ξ * sys.syndromeProjector σ₀`. -/
lemma exists_collar_scalar_worldlineSyndromeShiftBlockOp_eq_smul_worldlineJumpOp
    {L q_code r_0 m_max L_star : ℕ} [NeZero L]
    {C_RCA : ℝ}
    (D_field : Box3D L → LocalCSSDescriptor q_code r_0 m_max)
    (h_valid : ValidDescriptorField D_field)
    (sys : SysCSS[L, q_code, m_max])
    (h_sys_checks : ∀ idx, sys.checkProj idx = staticCSSCheckProj D_field idx ∧
      sys.support idx = staticCSSCheckSupport D_field idx ∧ sys.weight idx = 1)
    (h_tqo1 : SatisfiesTQO1 sys L_star)
    (h_tqo2 : SatisfiesSectorFilteredLinearTQO2 sys 1 L_star C_RCA)
    (V : QuasiLocalPerturbation 3 L (SiteCSS[L, q_code]))
    (ξ : WorldlineJumpMonomer L q_code)
    (hr1 : 1 ≤ ξ.1.1) (hr_Lstar : ξ.1.1 ≤ L_star)
    (hA : ξ.1.2 ∈ boxCubes 3 L ξ.1.1)
    (hV_supp : IsSupportedOn (SiteCSS[L, q_code]) ξ.1.2 (V.term ξ.1.1 ξ.1.2))
    (hξ_supp : ∀ slot : BoxSlot3D L q_code, ξ.2.1 slot ≠ 0 ∨ ξ.2.2 slot ≠ 0 → slot.1 ∈ ξ.1.2)
    (h_ne : staticCSSPauliFlip D_field ξ.2.1 ξ.2.2 ≠ (fun _ => false)) :
    ∃ c_ξ : (IdxCSS[L, q_code, m_max] → Bool) → ℂ,
      (∀ σ₁ σ₂ : IdxCSS[L, q_code, m_max] → Bool,
        (∀ c ∈ rcaCollarChecks sys C_RCA ξ.1.1 ξ.1.2, σ₁ c = σ₂ c) → c_ξ σ₁ = c_ξ σ₂) ∧
      (∀ σ₀ ∈ realizableSyndromes D_field,
        worldlineSyndromeShiftBlockOp D_field sys V ξ * sys.syndromeProjector σ₀ =
          c_ξ σ₀ • (worldlineJumpOp ξ * sys.syndromeProjector σ₀)) := by
  rcases exists_weylPauli_expansion_worldlineSyndromeShiftBlockOp_mul_syndromeProjector
      D_field sys h_sys_checks V ξ hV_supp h_ne with
    ⟨ι, _, S, w, a_fam, b_fam, h_supp, h_flip, hM⟩
  let x0 := anchorOfCube ξ.1.1 ξ.1.2
  have hA_eq : boxCube x0 ξ.1.1 = ξ.1.2 := boxCube_anchorOfCube hA
  let a' : ι → BoxSlot3D L q_code → ZMod 2 := fun i => ξ.2.1 + a_fam i
  let b' : ι → BoxSlot3D L q_code → ZMod 2 := fun i => ξ.2.2 + b_fam i
  have h_term_rca : ∀ i ∈ S,
      ∃ (α : Finset (IdxCSS[L, q_code, m_max])) (c₀ : ℝ),
        α ⊆ rcaCollarChecks sys C_RCA ξ.1.1 ξ.1.2 ∧
        ∀ σ ∈ realizableSyndromes D_field,
          hermitianPauliZX (a' i) (b' i) * sys.syndromeProjector σ =
            ((spanningSurfaceSign α σ * c₀ : ℝ) : ℂ) • sys.syndromeProjector σ := by
    intro i hi
    have h_ab_supp : ∀ slot : BoxSlot3D L q_code,
        a' i slot ≠ 0 ∨ b' i slot ≠ 0 → slot.1 ∈ boxCube x0 ξ.1.1 := by
      intro slot h_or
      rw [hA_eq]
      have h_cases : (ξ.2.1 slot ≠ 0 ∨ ξ.2.2 slot ≠ 0) ∨ (a_fam i slot ≠ 0 ∨ b_fam i slot ≠ 0) := by
        by_contra! h_all
        rcases h_or with ha | hb
        · apply ha; change ξ.2.1 slot + a_fam i slot = 0; rw [h_all.1.1, h_all.2.1, add_zero]
        · apply hb; change ξ.2.2 slot + b_fam i slot = 0; rw [h_all.1.2, h_all.2.2, add_zero]
      rcases h_cases with h1 | h2
      · exact hξ_supp slot h1
      · exact h_supp i hi slot h2
    have h_ab_closed : staticCSSPauliFlip D_field (a' i) (b' i) = fun _ => false := by
      rw [staticCSSPauliFlip_add D_field ξ.2.1 (a_fam i) ξ.2.2 (b_fam i), h_flip i hi]
      ext c; unfold syndromeXor; simp
    rcases hermitianPauliZX_syndrome_eigenvalue_and_collar_surface
        D_field h_valid sys h_sys_checks h_tqo1 h_tqo2 hr1 hr_Lstar x0 (a' i) (b' i)
        h_ab_supp h_ab_closed with ⟨α, c₀, hα_sub, _, _, hα_eig⟩
    rw [hA_eq] at hα_sub
    have hW_comm : ∀ σ, Commute (hermitianPauliZX (a' i) (b' i)) (sys.syndromeProjector σ) :=
      (indexed_check_commuting_perturbation_commutes_with_syndromeProjector sys _
        (hermitianPauliZX_props D_field sys h_sys_checks (boxCube x0 ξ.1.1) (a' i) (b' i)
          h_ab_supp h_ab_closed).2.2.2.1).1
    refine ⟨α, c₀, hα_sub, fun σ hσ => ?_⟩
    rw [(hW_comm σ).eq, hα_eig σ hσ]
  choose α_fn c0_fn hα_fn_sub h_eig_fn using fun i : {i // i ∈ S} => h_term_rca i.1 i.2
  let z_phase : ι → ℂ := fun i =>
    signScalar (∑ slot : BoxSlot3D L q_code, a' i slot * ξ.2.2 slot) *
      (if (∑ p : BoxSlot3D L q_code, a' i p * b' i p) = 0 then 1 else -Complex.I)
  let c_ξ : (IdxCSS[L, q_code, m_max] → Bool) → ℂ := fun σ =>
    ∑ i ∈ S.attach, w i.1 * z_phase i.1 * ((spanningSurfaceSign (α_fn i) σ * c0_fn i : ℝ) : ℂ)
  refine ⟨c_ξ, fun σ₁ σ₂ h_ag => Finset.sum_congr rfl fun i _ => ?_, fun σ₀ hσ₀ => ?_⟩
  · have h_sign : spanningSurfaceSign (α_fn i) σ₁ = spanningSurfaceSign (α_fn i) σ₂ := by
      unfold spanningSurfaceSign
      rw [Finset.filter_congr fun c hc => by rw [h_ag c (hα_fn_sub i hc)]]
    rw [h_sign]
  · rw [hM σ₀ hσ₀, Finset.sum_mul, ← Finset.sum_attach S]
    have h_sum_smul : ∀ (s : Finset {i // i ∈ S}) (g : {i // i ∈ S} → ℂ) (X : ℬ_CSS[L, q_code]),
        (∑ i ∈ s, g i) • X = ∑ i ∈ s, g i • X := by
      intro s g X; induction s using Finset.induction_on with
      | empty => rw [Finset.sum_empty, Finset.sum_empty]; ext ψ; simp
      | @insert a t ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, ← ih]; ext ψ; simp [add_smul]
    dsimp only [c_ξ]; rw [h_sum_smul]
    refine Finset.sum_congr rfl fun i _ => ?_
    have h_pauli_decomp : weylPauliZ (a_fam i.1) * weylPauliX (b_fam i.1) =
        z_phase i.1 • (worldlineJumpOp ξ * hermitianPauliZX (a' i.1) (b' i.1)) := by
      have h_z2 : ∀ u v : ZMod 2, u + (u + v) = v := by decide
      have h_add_a : ξ.2.1 + a' i.1 = a_fam i.1 := by ext slot; exact h_z2 _ _
      have h_add_b : ξ.2.2 + b' i.1 = b_fam i.1 := by ext slot; exact h_z2 _ _
      have h_mul_zx : worldlineJumpOp ξ * (weylPauliZ (a' i.1) * weylPauliX (b' i.1)) =
          signScalar (∑ slot, a' i.1 slot * ξ.2.2 slot) • (weylPauliZ (a_fam i.1) * weylPauliX (b_fam i.1)) := by
        unfold worldlineJumpOp; rw [weylPauliZX_mul_weylPauliZX, h_add_a, h_add_b]
      have h_herm : (if (∑ p, a' i.1 p * b' i.1 p) = 0 then (1 : ℂ) else -Complex.I) •
          hermitianPauliZX (a' i.1) (b' i.1) = weylPauliZ (a' i.1) * weylPauliX (b' i.1) := by
        unfold hermitianPauliZX; split_ifs
        · rw [one_smul]
        · rw [smul_smul, neg_mul, Complex.I_mul_I, neg_neg, one_smul]
      dsimp [z_phase]; rw [mul_smul, ← clm_mul_smul, h_herm, h_mul_zx, smul_smul]
      have h_sq : signScalar (∑ slot, a' i.1 slot * ξ.2.2 slot) *
          signScalar (∑ slot, a' i.1 slot * ξ.2.2 slot) = 1 := by
        rcases _root_.zmod2_eq_zero_or_one (∑ slot, a' i.1 slot * ξ.2.2 slot) with h0 | h1 <;>
          [rw [h0]; rw [h1]] <;> simp [signScalar]
      rw [h_sq, one_smul]
    rw [h_pauli_decomp, smul_smul, clm_smul_mul, mul_assoc (worldlineJumpOp ξ),
      h_eig_fn i σ₀ hσ₀, clm_mul_smul, smul_smul, mul_assoc]

/-- Syndrome-projector intertwining identity for `worldlineJumpOp ξ`. -/
lemma worldlineJumpOp_mul_syndromeProjector_eq {L q_code r_0 m_max : ℕ}
    (D_field : Box3D L → LocalCSSDescriptor q_code r_0 m_max) (sys : SysCSS[L, q_code, m_max])
    (h_sys_checks : ∀ idx, sys.checkProj idx = staticCSSCheckProj D_field idx ∧
      sys.support idx = staticCSSCheckSupport D_field idx ∧ sys.weight idx = 1)
    (ξ : WorldlineJumpMonomer L q_code) (σ₀ : IdxCSS[L, q_code, m_max] → Bool) :
    worldlineJumpOp ξ * sys.syndromeProjector σ₀ =
      sys.syndromeProjector (syndromeXor (staticCSSPauliFlip D_field ξ.2.1 ξ.2.2) σ₀) *
        (worldlineJumpOp ξ * sys.syndromeProjector σ₀) := by
  have h_res := PerturbedThermalBarrier.syndrome_resolution_indexed sys
  have h_flip : ∀ idx, worldlineJumpOp ξ * sys.checkProj idx =
      (if staticCSSPauliFlip D_field ξ.2.1 ξ.2.2 idx then 1 - sys.checkProj idx else sys.checkProj idx) *
        worldlineJumpOp ξ := fun idx => by
    unfold worldlineJumpOp; rw [(h_sys_checks idx).1]
    exact weylPauliZX_mul_staticCSSCheckProj D_field ξ.2.1 ξ.2.2 idx
  have h_inter := intertwine_syndromeProjector_of_checkFlip sys h_flip σ₀
  have h_xor_eq : (fun idx => xor (σ₀ idx) (staticCSSPauliFlip D_field ξ.2.1 ξ.2.2 idx)) =
      syndromeXor (staticCSSPauliFlip D_field ξ.2.1 ξ.2.2) σ₀ := by
    ext idx; change bne (σ₀ idx) (staticCSSPauliFlip D_field ξ.2.1 ξ.2.2 idx) =
      bne (staticCSSPauliFlip D_field ξ.2.1 ξ.2.2 idx) (σ₀ idx)
    cases σ₀ idx <;> cases staticCSSPauliFlip D_field ξ.2.1 ξ.2.2 idx <;> rfl
  rw [h_xor_eq] at h_inter
  calc worldlineJumpOp ξ * sys.syndromeProjector σ₀
    _ = worldlineJumpOp ξ * (sys.syndromeProjector σ₀ * sys.syndromeProjector σ₀) := by
        rw [(h_res.2.1 σ₀).1]
    _ = (worldlineJumpOp ξ * sys.syndromeProjector σ₀) * sys.syndromeProjector σ₀ := by
        rw [← mul_assoc]
    _ = sys.syndromeProjector (syndromeXor (staticCSSPauliFlip D_field ξ.2.1 ξ.2.2) σ₀) *
          (worldlineJumpOp ξ * sys.syndromeProjector σ₀) := by
        conv_lhs => rw [h_inter, mul_assoc]

/-- Multi-step $\mathrm{RCA}_1$ collar-scalar factorization along any list of jump monomers. -/
lemma exists_collar_scalar_list_prod_reverse_worldlineSyndromeShiftBlockOp_eq_smul_worldlineJumpOp
    {L q_code r_0 m_max L_star : ℕ} [NeZero L] {C_RCA : ℝ}
    (D_field : Box3D L → LocalCSSDescriptor q_code r_0 m_max) (h_valid : ValidDescriptorField D_field)
    (sys : SysCSS[L, q_code, m_max])
    (h_sys_checks : ∀ idx, sys.checkProj idx = staticCSSCheckProj D_field idx ∧
      sys.support idx = staticCSSCheckSupport D_field idx ∧ sys.weight idx = 1)
    (h_tqo1 : SatisfiesTQO1 sys L_star) (h_tqo2 : SatisfiesSectorFilteredLinearTQO2 sys 1 L_star C_RCA)
    (V : QuasiLocalPerturbation 3 L (SiteCSS[L, q_code])) (jumps : List (WorldlineJumpMonomer L q_code))
    (h_jumps : ∀ ξ ∈ jumps, 1 ≤ ξ.1.1 ∧ ξ.1.1 ≤ L_star ∧ ξ.1.2 ∈ boxCubes 3 L ξ.1.1 ∧
      IsSupportedOn (SiteCSS[L, q_code]) ξ.1.2 (V.term ξ.1.1 ξ.1.2) ∧
      (∀ slot : BoxSlot3D L q_code, ξ.2.1 slot ≠ 0 ∨ ξ.2.2 slot ≠ 0 → slot.1 ∈ ξ.1.2) ∧
      staticCSSPauliFlip D_field ξ.2.1 ξ.2.2 ≠ (fun _ => false)) :
    ∃ C_jumps : (IdxCSS[L, q_code, m_max] → Bool) → ℂ,
      (∀ σ₁ σ₂ : IdxCSS[L, q_code, m_max] → Bool,
        (∀ ξ ∈ jumps, ∀ c ∈ rcaCollarChecks sys C_RCA ξ.1.1 ξ.1.2, σ₁ c = σ₂ c) →
        C_jumps σ₁ = C_jumps σ₂) ∧
      (∀ σ₀ ∈ realizableSyndromes D_field,
        (jumps.reverse.map (worldlineSyndromeShiftBlockOp D_field sys V)).prod * sys.syndromeProjector σ₀ =
        C_jumps σ₀ • ((jumps.reverse.map worldlineJumpOp).prod * sys.syndromeProjector σ₀)) := by
  induction jumps with
  | nil => refine ⟨fun _ => 1, fun _ _ _ => rfl, fun σ₀ _ => by simp⟩
  | cons hd tl ih =>
    rcases h_jumps hd List.mem_cons_self with ⟨hr1, hr_Lstar, hA_hd, hV_hd, hξ_hd, h_ne_hd⟩
    rcases exists_collar_scalar_worldlineSyndromeShiftBlockOp_eq_smul_worldlineJumpOp
        D_field h_valid sys h_sys_checks h_tqo1 h_tqo2 V hd hr1 hr_Lstar hA_hd hV_hd hξ_hd h_ne_hd with
      ⟨c_hd, hc_hd_ag, hc_hd_eq⟩
    rcases ih (fun ξ hξ => h_jumps ξ (List.mem_cons_of_mem hd hξ)) with ⟨C_tl, hC_tl_ag, hC_tl_eq⟩
    let δ_hd := staticCSSPauliFlip D_field hd.2.1 hd.2.2
    refine ⟨fun σ => C_tl (syndromeXor δ_hd σ) * c_hd σ, fun σ₁ σ₂ h_ag => ?_, fun σ₀ hσ₀ => ?_⟩
    · have h1 : C_tl (syndromeXor δ_hd σ₁) = C_tl (syndromeXor δ_hd σ₂) :=
        hC_tl_ag _ _ fun ξ hξ c hc => by unfold syndromeXor; rw [h_ag ξ (List.mem_cons_of_mem hd hξ) c hc]
      have h2 : c_hd σ₁ = c_hd σ₂ := hc_hd_ag _ _ (h_ag hd List.mem_cons_self)
      (try dsimp only); rw [h1, h2]
    · have h_mem_hd : syndromeXor δ_hd σ₀ ∈ realizableSyndromes D_field :=
        syndromeXor_staticCSSPauliFlip_mem_realizableSyndromes D_field hd.2.1 hd.2.2 σ₀ hσ₀
      have h_prod_B : ((hd :: tl).reverse.map (worldlineSyndromeShiftBlockOp D_field sys V)).prod =
          (tl.reverse.map (worldlineSyndromeShiftBlockOp D_field sys V)).prod *
            worldlineSyndromeShiftBlockOp D_field sys V hd := by
        rw [List.reverse_cons, List.map_append, List.prod_append, List.map_cons,
          List.map_nil, List.prod_cons, List.prod_nil, mul_one]
      have h_prod_J : ((hd :: tl).reverse.map worldlineJumpOp).prod =
          (tl.reverse.map worldlineJumpOp).prod * worldlineJumpOp hd := by
        rw [List.reverse_cons, List.map_append, List.prod_append, List.map_cons,
          List.map_nil, List.prod_cons, List.prod_nil, mul_one]
      have h_inter_hd : worldlineJumpOp hd * sys.syndromeProjector σ₀ =
          sys.syndromeProjector (syndromeXor δ_hd σ₀) * (worldlineJumpOp hd * sys.syndromeProjector σ₀) :=
        worldlineJumpOp_mul_syndromeProjector_eq D_field sys h_sys_checks hd σ₀
      calc ((hd :: tl).reverse.map (worldlineSyndromeShiftBlockOp D_field sys V)).prod * sys.syndromeProjector σ₀
        _ = (tl.reverse.map (worldlineSyndromeShiftBlockOp D_field sys V)).prod *
              (c_hd σ₀ • (worldlineJumpOp hd * sys.syndromeProjector σ₀)) := by
              rw [h_prod_B, mul_assoc, hc_hd_eq σ₀ hσ₀]
        _ = c_hd σ₀ • (((tl.reverse.map (worldlineSyndromeShiftBlockOp D_field sys V)).prod *
              sys.syndromeProjector (syndromeXor δ_hd σ₀)) * (worldlineJumpOp hd * sys.syndromeProjector σ₀)) := by
              conv_lhs => rw [clm_mul_smul, h_inter_hd, ← mul_assoc]
        _ = (C_tl (syndromeXor δ_hd σ₀) * c_hd σ₀) •
              ((tl.reverse.map worldlineJumpOp).prod *
                (sys.syndromeProjector (syndromeXor δ_hd σ₀) * (worldlineJumpOp hd * sys.syndromeProjector σ₀))) := by
              rw [hC_tl_eq (syndromeXor δ_hd σ₀) h_mem_hd, clm_smul_mul, smul_smul, mul_comm (c_hd σ₀), mul_assoc]
        _ = (C_tl (syndromeXor δ_hd σ₀) * c_hd σ₀) •
              (((hd :: tl).reverse.map worldlineJumpOp).prod * sys.syndromeProjector σ₀) := by
              rw [← h_inter_hd, h_prod_J, mul_assoc]

private lemma signScalar_sum_boolToZMod2_eq_spanningSurfaceSign {L q_code m_max : ℕ}
    (α : Finset (IdxCSS[L, q_code, m_max])) (σ : IdxCSS[L, q_code, m_max] → Bool) :
    signScalar (∑ c ∈ α, boolToZMod2 (σ c)) = ((spanningSurfaceSign α σ : ℝ) : ℂ) := by
  induction α using Finset.induction_on with
  | empty => simp [spanningSurfaceSign, signScalar_zero]
  | @insert c₀ s hc₀ ih =>
    rw [Finset.sum_insert hc₀, signScalar_add, ih]
    unfold spanningSurfaceSign; rw [Finset.filter_insert]
    cases hσ : σ c₀
    · simp [boolToZMod2, signScalar_zero]
    · have hc₀_filt : c₀ ∉ s.filter (fun c => σ c = true) := fun h => hc₀ (Finset.mem_filter.mp h).1
      rw [if_pos rfl, Finset.card_insert_of_notMem hc₀_filt]
      change (-1 : ℂ) * ((if (s.filter (fun c => σ c = true)).card % 2 = 1 then (-1 : ℝ) else 1 : ℝ) : ℂ) =
        ((if ((s.filter (fun c => σ c = true)).card + 1) % 2 = 1 then (-1 : ℝ) else 1 : ℝ) : ℂ)
      by_cases h_mod : (s.filter (fun c => σ c = true)).card % 2 = 1
      · rw [if_pos h_mod, if_neg (by omega)]; norm_num
      · rw [if_neg h_mod, if_pos (by omega)]; norm_num

/-- Every valid worldline polymer $\gamma$ has a syndrome-closed logical coset representative
`worldlinePolymerLogicalCoset D_field sys C_RCA γ ∈ syndromeClosedPauliFinset D_field` and
satisfies `IsSpanningCheckSurfaceForPolymer` with its canonical spanning surface
`worldlinePolymerSpanningSurface D_field sys C_RCA γ` (Part II, Lemma 2.8(i)–(ii) (`lem:worldline-factorization-time-reversal`), Equation `eq:P-gamma-spanning-surface`). -/
lemma isSpanningCheckSurfaceForPolymer_of_isValidWorldlinePolymer
    {L q_code r_0 m_max R_cut : ℕ} [NeZero L]
    {C_RCA : ℝ}
    (D_field : Box3D L → LocalCSSDescriptor q_code r_0 m_max)
    (h_valid : ValidDescriptorField D_field)
    (sys : SysCSS[L, q_code, m_max])
    (h_sys_checks : ∀ idx, sys.checkProj idx = staticCSSCheckProj D_field idx ∧
      sys.support idx = staticCSSCheckSupport D_field idx ∧ sys.weight idx = 1)
    (γ : WorldlineDysonPolymer L q_code)
    (hγ : IsValidWorldlinePolymer D_field sys C_RCA R_cut γ) :
    worldlinePolymerLogicalCoset D_field sys C_RCA γ ∈ syndromeClosedPauliFinset D_field ∧
    IsSpanningCheckSurfaceForPolymer D_field sys γ
      (worldlinePolymerLogicalCoset D_field sys C_RCA γ)
      (worldlinePolymerSpanningSurface D_field sys C_RCA γ) := by
  let a := worldlinePolymerLoopX γ
  let b := worldlinePolymerLoopZ γ
  let μ := worldlinePolymerLogicalCoset D_field sys C_RCA γ
  rcases exists_finset_sum_add_bareLogicalProjection D_field (a, b) with ⟨α₀, hα₀⟩
  let q := μ + (a, b)
  have hq_eq : q = ∑ c ∈ α₀, (staticCSSCheckPauliZ D_field c, staticCSSCheckPauliX D_field c) := hα₀
  have h_res := PerturbedThermalBarrier.syndrome_resolution_indexed sys
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
  have hU_right : ∀ x y : BoxSlot3D L q_code → ZMod 2,
      (weylPauliZ x * weylPauliX y) * (weylPauliX y * weylPauliZ x) = 1 := fun x y => by
    calc (weylPauliZ x * weylPauliX y) * (weylPauliX y * weylPauliZ x)
      _ = weylPauliZ x * (weylPauliX y * weylPauliX y) * weylPauliZ x := by simp only [mul_assoc]
      _ = 1 := by rw [weylPauliX_sq_eq_one y, mul_one, weylPauliZ_sq_eq_one x]
  have hU_left : ∀ x y : BoxSlot3D L q_code → ZMod 2,
      (weylPauliX y * weylPauliZ x) * (weylPauliZ x * weylPauliX y) = 1 := fun x y => by
    calc (weylPauliX y * weylPauliZ x) * (weylPauliZ x * weylPauliX y)
      _ = weylPauliX y * (weylPauliZ x * weylPauliZ x) * weylPauliX y := by simp only [mul_assoc]
      _ = 1 := by rw [weylPauliZ_sq_eq_one x, mul_one, weylPauliX_sq_eq_one y]
  have hZ_P0 : ∀ s : Finset (IdxCSS[L, q_code, m_max]),
      weylPauliZ (∑ c ∈ s, staticCSSCheckPauliZ D_field c) * sys.P0 = sys.P0 := by
    intro s; induction s using Finset.induction_on with
    | empty => rw [Finset.sum_empty, weylPauliZ_zero, one_mul]
    | @insert c t hc ih =>
      rw [Finset.sum_insert hc, weylPauliZ_add, mul_assoc, ih,
        (weylPauli_staticCSSCheckPauli_mul_P0 D_field sys h_sys_checks c).1]
  have hX_P0 : ∀ s : Finset (IdxCSS[L, q_code, m_max]),
      weylPauliX (∑ c ∈ s, staticCSSCheckPauliX D_field c) * sys.P0 = sys.P0 := by
    intro s; induction s using Finset.induction_on with
    | empty => rw [Finset.sum_empty, weylPauliX_zero, one_mul]
    | @insert c t hc ih =>
      rw [Finset.sum_insert hc, weylPauliX_add, mul_assoc, ih,
        (weylPauli_staticCSSCheckPauli_mul_P0 D_field sys h_sys_checks c).2]
  have hq_P0 : (weylPauliZ q.1 * weylPauliX q.2) * sys.P0 = sys.P0 := by
    have hq1 : q.1 = ∑ c ∈ α₀, staticCSSCheckPauliZ D_field c := by rw [hq_eq, Prod.fst_sum]
    have hq2 : q.2 = ∑ c ∈ α₀, staticCSSCheckPauliX D_field c := by rw [hq_eq, Prod.snd_sum]
    rw [hq1, hq2, mul_assoc, hX_P0 α₀, hZ_P0 α₀]
  have hq_closed : staticCSSPauliFlip D_field q.1 q.2 = fun _ => false := by
    by_contra h_ne
    have h_orth : sys.P0 * sys.syndromeProjector (staticCSSPauliFlip D_field q.1 q.2) = 0 := by
      rw [← h_res.1]; exact h_res.2.2.1 (fun _ => false) _ (Ne.symm h_ne)
    have hP0_zero : sys.P0 = 0 := by
      calc sys.P0 = sys.P0 * ((weylPauliZ q.1 * weylPauliX q.2) * sys.P0) := by
            rw [hq_P0, ← h_res.1, (h_res.2.1 (fun _ => false)).1, h_res.1]
        _ = (sys.P0 * sys.syndromeProjector (staticCSSPauliFlip D_field q.1 q.2)) *
              (weylPauliZ q.1 * weylPauliX q.2) := by rw [hU_inter q.1 q.2, ← mul_assoc]
        _ = 0 := by rw [h_orth, zero_mul]
    exact sys_P0_ne_zero_of_validDescriptorField D_field h_valid sys h_sys_checks hP0_zero
  have hμ_closed : μ ∈ syndromeClosedPauliFinset D_field := by
    rw [syndromeClosedPauliFinset, Finset.mem_filter]; refine ⟨Finset.mem_univ _, ?_⟩
    have h_z2 : ∀ u v : ZMod 2, u = (u + v) + v := by decide
    have hμ1 : μ.1 = q.1 + a := by ext s; exact h_z2 _ _
    have hμ2 : μ.2 = q.2 + b := by ext s; exact h_z2 _ _
    rw [hμ1, hμ2, staticCSSPauliFlip_add D_field q.1 a q.2 b, hq_closed, hγ.2.2.1.2]
    ext c; rfl
  rcases list_prod_map_worldlineJumpOpZX_eq_signScalar_smul γ.1.reverse with ⟨s_loop, hs_loop⟩
  have h_sum_X : (γ.1.reverse.map (fun ξ => ξ.2.1)).sum = a := by
    dsimp [a, worldlinePolymerLoopX]; rw [List.map_reverse, List.sum_reverse]
  have h_sum_Z : (γ.1.reverse.map (fun ξ => ξ.2.2)).sum = b := by
    dsimp [b, worldlinePolymerLoopZ]; rw [List.map_reverse, List.sum_reverse]
  rw [h_sum_X, h_sum_Z] at hs_loop
  have hs_loop' : worldlinePolymerLoopOp γ = signScalar s_loop • (weylPauliZ a * weylPauliX b) := hs_loop
  have h_tr_conj : ∀ (u v c d : BoxSlot3D L q_code → ZMod 2) (z : ℂ),
      hilbertTrace (sys.syndromeProjector (staticCSSPauliFlip D_field u v) *
        (z • (weylPauliZ c * weylPauliX d))) =
      (signScalar (∑ slot, (u slot * d slot + c slot * v slot))).re *
        hilbertTrace (sys.P0 * (z • (weylPauliZ c * weylPauliX d))) := by
    intro u v c d z
    let U := weylPauliZ u * weylPauliX v
    let U_inv := weylPauliX v * weylPauliZ u
    let W := weylPauliZ c * weylPauliX d
    let s_uv := signScalar (∑ slot, (u slot * d slot + c slot * v slot))
    have h_proj_eq : sys.syndromeProjector (staticCSSPauliFlip D_field u v) = U * sys.P0 * U_inv := by
      calc sys.syndromeProjector (staticCSSPauliFlip D_field u v)
        _ = (sys.syndromeProjector (staticCSSPauliFlip D_field u v) * U) * U_inv := by
            rw [mul_assoc, hU_right u v, mul_one]
        _ = U * sys.P0 * U_inv := by rw [← hU_inter u v]
    have h_inv_comm : U_inv * (z • W) = (s_uv.re : ℂ) • ((z • W) * U_inv) := by
      have hs_im : (s_uv.re : ℂ) = s_uv := by
        dsimp [s_uv]; rcases _root_.zmod2_eq_zero_or_one (∑ slot, (u slot * d slot + c slot * v slot)) with h0 | h1 <;>
          [rw [h0]; rw [h1]] <;> simp [signScalar]
      rw [hs_im]
      calc U_inv * (z • W)
        _ = z • (U_inv * (W * U) * U_inv) := by
            rw [clm_mul_smul]; congr 1
            calc U_inv * W = U_inv * (W * (U * U_inv)) := by rw [hU_right u v, mul_one]
              _ = U_inv * (W * U) * U_inv := by simp only [mul_assoc]
        _ = s_uv • ((z • W) * U_inv) := by
            have h_comm_WU : W * U = s_uv • (U * W) := weylPauliZX_comm_signScalar c d u v
            rw [h_comm_WU, clm_mul_smul, clm_smul_mul, ← mul_assoc U_inv U W,
              hU_left u v, one_mul, smul_comm, ← clm_smul_mul]
    calc hilbertTrace (sys.syndromeProjector (staticCSSPauliFlip D_field u v) * (z • W))
      _ = hilbertTrace ((U * sys.P0) * (U_inv * (z • W))) := by rw [h_proj_eq]; simp only [mul_assoc]
      _ = s_uv.re * hilbertTrace (((U * sys.P0) * (z • W)) * U_inv) := by
          rw [h_inv_comm, clm_mul_smul, (hilbertTrace_add_and_complex_smul_decomp _ 0 0 0 s_uv.re 0).2.1]
          simp only [mul_assoc]
      _ = s_uv.re * hilbertTrace (sys.P0 * (z • W)) := by
          rw [hilbertTrace_mul_comm_aux ((U * sys.P0) * (z • W)) U_inv,
            ← mul_assoc U_inv (U * sys.P0) (z • W), ← mul_assoc U_inv U sys.P0,
            hU_left u v, one_mul]
  have hP0_tr_pos : 0 < hilbertTrace sys.P0 := by
    rw [← h_res.1]
    exact hilbertTrace_pos_of_isStarProjection_ne_zero (h_res.2.1 (fun _ => false))
      (by rw [h_res.1]; exact sys_P0_ne_zero_of_validDescriptorField D_field h_valid sys h_sys_checks)
  have h_glob_α₀ : IsSpanningCheckSurfaceForPolymer D_field sys γ μ α₀ := by
    unfold IsSpanningCheckSurfaceForPolymer; (try dsimp only)
    rcases hermitianPauliZX_isSelfAdjoint_and_sq_eq_one μ.1 μ.2 with ⟨hM_sa, _⟩
    have hM_adj : (hermitianPauliZX μ.1 μ.2)† = hermitianPauliZX μ.1 μ.2 :=
      ContinuousLinearMap.isSelfAdjoint_iff'.mp hM_sa
    let z₁ : ℂ := if (∑ p, μ.1 p * μ.2 p) = 0 then 1 else Complex.I
    have hz₁ : hermitianPauliZX μ.1 μ.2 = z₁ • (weylPauliZ μ.1 * weylPauliX μ.2) := by
      dsimp [z₁]; unfold hermitianPauliZX; split_ifs <;> [exact (one_smul ℂ _).symm; rfl]
    let s_tot := s_loop + ∑ p, a p * μ.2 p
    let z₀ : ℂ := z₁ * signScalar s_tot
    have hL_eq : (hermitianPauliZX μ.1 μ.2)† * worldlinePolymerLoopOp γ =
        z₀ • (weylPauliZ q.1 * weylPauliX q.2) := by
      rw [hM_adj, hz₁, hs_loop', clm_smul_mul, clm_mul_smul]
      change z₁ • (signScalar s_loop • ((weylPauliZ μ.1 * weylPauliX μ.2) * (weylPauliZ a * weylPauliX b))) = _
      rw [weylPauliZX_mul_weylPauliZX, smul_smul, smul_smul, mul_assoc z₁, ← signScalar_add]; rfl
    have hz₀_ne : z₀.re ≠ 0 ∨ (Complex.I * z₀).re ≠ 0 := by
      dsimp [z₀, z₁]
      rcases _root_.zmod2_eq_zero_or_one s_tot with h0 | h1 <;> [rw [h0]; rw [h1]] <;>
        (split_ifs <;> norm_num [signScalar])
    have hq_comm_P0 : sys.P0 * (weylPauliZ q.1 * weylPauliX q.2) = sys.P0 := by
      have hq_mem : q ∈ syndromeClosedPauliFinset D_field :=
        Finset.mem_filter.mpr ⟨Finset.mem_univ _, hq_closed⟩
      rw [← (weylPauliZX_comm_checkProj_and_syndromeProjector_of_syndromeClosed
        D_field sys h_sys_checks hq_mem).2.2.eq, hq_P0]
    have h_tr_P0 : ∀ w : ℂ, hilbertTrace (sys.P0 * (w • ((hermitianPauliZX μ.1 μ.2)† * worldlinePolymerLoopOp γ))) =
        (w * z₀).re * hilbertTrace sys.P0 := fun w => by
      rw [hL_eq, smul_smul, clm_mul_smul, hq_comm_P0, ← h_res.1,
        hilbertTrace_complex_smul_syndromeProjector, h_res.1]
    have h_sign_eq : ∀ u v : BoxSlot3D L q_code → ZMod 2,
        (signScalar (∑ slot, (u slot * q.2 slot + q.1 slot * v slot))).re =
          spanningSurfaceSign α₀ (staticCSSPauliFlip D_field u v) := by
      intro u v
      have h_sum_eq : (∑ slot, (u slot * q.2 slot + q.1 slot * v slot)) =
          ∑ c ∈ α₀, boolToZMod2 (staticCSSPauliFlip D_field u v c) := by
        have hq1 : q.1 = ∑ c ∈ α₀, staticCSSCheckPauliZ D_field c := by rw [hq_eq, Prod.fst_sum]
        have hq2 : q.2 = ∑ c ∈ α₀, staticCSSCheckPauliX D_field c := by rw [hq_eq, Prod.snd_sum]
        rw [hq1, hq2]
        simp_rw [Finset.sum_apply, Finset.mul_sum, Finset.sum_mul, ← Finset.sum_add_distrib]
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun c _ => (boolToZMod2_staticCSSPauliFlip_eq_sum_checkPauli D_field (u, v) c).symm
      have h_c := congrArg Complex.re (signScalar_sum_boolToZMod2_eq_spanningSurfaceSign α₀ (staticCSSPauliFlip D_field u v))
      rw [← h_sum_eq] at h_c; simpa using h_c
    refine ⟨?_, fun σ hσ => ?_⟩
    · rcases hz₀_ne with hz1 | hzI
      · left; have h1 := h_tr_P0 1; rw [one_smul, one_mul] at h1; rw [h1]
        exact mul_ne_zero hz1 (ne_of_gt hP0_tr_pos)
      · right; rw [h_tr_P0 Complex.I]; exact mul_ne_zero hzI (ne_of_gt hP0_tr_pos)
    · rcases (Finset.mem_filter.mp hσ).2 with ⟨u, v, rfl⟩
      have h1 := h_tr_conj u v q.1 q.2 z₀
      have hI := h_tr_conj u v q.1 q.2 (Complex.I * z₀)
      rw [h_sign_eq u v] at h1 hI
      rw [hL_eq, smul_smul]
      exact ⟨h1, hI⟩
  refine ⟨hμ_closed, ?_⟩
  unfold worldlinePolymerSpanningSurface
  by_cases h_loc : ∃ α : Finset (IdxCSS[L, q_code, m_max]),
      α ⊆ worldlinePolymerBoundingBoxCollar sys C_RCA γ ∧
      IsSpanningCheckSurfaceForPolymer D_field sys γ (0, 0) α
  · rw [dif_pos h_loc]
    have h_span_loc := (Classical.choose_spec h_loc).2
    let α_loc := Classical.choose h_loc
    have h_zero_adj : (hermitianPauliZX (0 : BoxSlot3D L q_code → ZMod 2)
        (0 : BoxSlot3D L q_code → ZMod 2))† = 1 := by
      unfold hermitianPauliZX
      rw [if_pos (by simp), weylPauliZ_zero, weylPauliX_zero, mul_one,
        ← ContinuousLinearMap.star_eq_adjoint, star_one]
    have h_sum_loc : ∀ p : PauliBitstringPair L q_code,
        (∑ slot, (p.1 slot * b slot + a slot * p.2 slot)) =
          ∑ c ∈ α_loc, boolToZMod2 (staticCSSPauliFlip D_field p.1 p.2 c) := by
      intro p
      have hσ_p : staticCSSPauliFlip D_field p.1 p.2 ∈ realizableSyndromes D_field :=
        Finset.mem_filter.mpr ⟨Finset.mem_univ _, p.1, p.2, rfl⟩
      have h_loc_p := h_span_loc.2 (staticCSSPauliFlip D_field p.1 p.2) hσ_p
      have h_tr_eq : ∀ w : ℂ,
          spanningSurfaceSign α_loc (staticCSSPauliFlip D_field p.1 p.2) *
            hilbertTrace (sys.P0 * (w • ((hermitianPauliZX 0 0)† * worldlinePolymerLoopOp γ))) =
          (signScalar (∑ slot, (p.1 slot * b slot + a slot * p.2 slot))).re *
            hilbertTrace (sys.P0 * (w • ((hermitianPauliZX 0 0)† * worldlinePolymerLoopOp γ))) := by
        intro w
        have h_lhs : hilbertTrace (sys.syndromeProjector (staticCSSPauliFlip D_field p.1 p.2) *
            (w • ((hermitianPauliZX 0 0)† * worldlinePolymerLoopOp γ))) =
            (signScalar (∑ slot, (p.1 slot * b slot + a slot * p.2 slot))).re *
              hilbertTrace (sys.P0 * (w • ((hermitianPauliZX 0 0)† * worldlinePolymerLoopOp γ))) := by
          rw [h_zero_adj, one_mul, hs_loop', smul_smul]
          exact h_tr_conj p.1 p.2 a b (w * signScalar s_loop)
        by_cases hw : w = 1
        · rw [hw, one_smul] at h_lhs ⊢; exact h_loc_p.1.symm.trans h_lhs
        · have : hilbertTrace (sys.syndromeProjector (staticCSSPauliFlip D_field p.1 p.2) *
              (w • ((hermitianPauliZX 0 0)† * worldlinePolymerLoopOp γ))) =
              spanningSurfaceSign α_loc (staticCSSPauliFlip D_field p.1 p.2) *
                hilbertTrace (sys.P0 * (w • ((hermitianPauliZX 0 0)† * worldlinePolymerLoopOp γ))) := by
            rw [(hilbertTrace_add_and_complex_smul_decomp 0 0 _ _ 0 w).2.2,
              (hilbertTrace_add_and_complex_smul_decomp 0 0 _ _ 0 w).2.2, h_loc_p.1, h_loc_p.2]; ring
          exact this.symm.trans h_lhs
      have h_re_eq : spanningSurfaceSign α_loc (staticCSSPauliFlip D_field p.1 p.2) =
          (signScalar (∑ slot, (p.1 slot * b slot + a slot * p.2 slot))).re := by
        rcases h_span_loc.1 with h_ne1 | h_neI
        · have h1 := h_tr_eq 1; rw [one_smul] at h1; exact mul_right_cancel₀ h_ne1 h1
        · exact mul_right_cancel₀ h_neI (h_tr_eq Complex.I)
      have h_c := congrArg Complex.re (signScalar_sum_boolToZMod2_eq_spanningSurfaceSign α_loc (staticCSSPauliFlip D_field p.1 p.2))
      simp only [Complex.ofReal_re] at h_c
      have h_re_eq' : (signScalar (∑ slot, (p.1 slot * b slot + a slot * p.2 slot))).re =
          (signScalar (∑ c ∈ α_loc, boolToZMod2 (staticCSSPauliFlip D_field p.1 p.2 c))).re :=
        h_re_eq.symm.trans h_c.symm
      have h_z2_inj : ∀ u v : ZMod 2, (signScalar u).re = (signScalar v).re → u = v := by
        intro u v h
        rcases _root_.zmod2_eq_zero_or_one u with rfl | rfl <;>
          rcases _root_.zmod2_eq_zero_or_one v with rfl | rfl <;>
          first | rfl | norm_num [signScalar] at h
      exact h_z2_inj _ _ h_re_eq'
    have hab_eq_sum : (a, b) = ∑ c ∈ α_loc, (staticCSSCheckPauliZ D_field c, staticCSSCheckPauliX D_field c) := by
      ext slot
      · have h1 := h_sum_loc (0, Pi.single slot 1)
        (try dsimp only at h1)
        simp only [Pi.zero_apply, zero_mul, zero_add, mul_ite, Pi.single_apply, mul_one, mul_zero,
          Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte] at h1
        change a slot = (∑ c ∈ α_loc, (staticCSSCheckPauliZ D_field c, staticCSSCheckPauliX D_field c)).1 slot
        rw [h1, Prod.fst_sum, Finset.sum_apply]
        refine Finset.sum_congr rfl fun c _ => ?_
        have h_flip := boolToZMod2_staticCSSPauliFlip_eq_sum_checkPauli D_field (0, Pi.single slot (1 : ZMod 2)) c
        (try dsimp only at h_flip ⊢)
        rw [h_flip]
        simp only [Pi.zero_apply, zero_mul, zero_add, Pi.single_apply, mul_ite, mul_one, mul_zero,
          Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
      · have h2 := h_sum_loc (Pi.single slot 1, 0)
        (try dsimp only at h2)
        simp only [Pi.zero_apply, mul_zero, add_zero, Pi.single_apply, ite_mul, one_mul, zero_mul,
          Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte] at h2
        change b slot = (∑ c ∈ α_loc, (staticCSSCheckPauliZ D_field c, staticCSSCheckPauliX D_field c)).2 slot
        rw [h2, Prod.snd_sum, Finset.sum_apply]
        refine Finset.sum_congr rfl fun c _ => ?_
        have h_flip := boolToZMod2_staticCSSPauliFlip_eq_sum_checkPauli D_field (Pi.single slot (1 : ZMod 2), 0) c
        (try dsimp only at h_flip ⊢)
        rw [h_flip]
        simp only [Pi.zero_apply, mul_zero, add_zero, Pi.single_apply, ite_mul, one_mul, zero_mul,
          Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
    have hab_mem : (a, b) ∈ stabilizerPauliSubmodule D_field := by
      rw [hab_eq_sum]; exact Submodule.sum_mem _ fun c _ => Submodule.subset_span ⟨c, rfl⟩
    have hμ_zero : worldlinePolymerLogicalCoset D_field sys C_RCA γ = (0, 0) :=
      bareLogicalProjection_eq_zero_of_mem_stabilizerPauliSubmodule D_field hab_mem
    rw [hμ_zero]
    exact h_span_loc
  · have h_glob : ∃ α : Finset (IdxCSS[L, q_code, m_max]),
        IsSpanningCheckSurfaceForPolymer D_field sys γ μ α := ⟨α₀, h_glob_α₀⟩
    rw [dif_neg h_loc, dif_pos h_glob]
    exact Classical.choose_spec h_glob

/-- Exact sector-trace evaluation of `spanningSurfaceSign α(γ) σ * worldlinePolymerLoopAmplitude`
for every valid worldline polymer $\gamma$ at cutoff $R_{\mathrm{cut}} \le L^*$ (Part II, Lemma 2.8(i)–(ii) (`lem:worldline-factorization-time-reversal`), Equation `eq:P-gamma-spanning-surface`). -/
lemma spanningSurfaceSign_mul_worldlinePolymerLoopAmplitude_eq_of_valid
    {L q_code r_0 m_max L_star R_cut : ℕ} [NeZero L] {C_RCA : ℝ}
    (D_field : Box3D L → LocalCSSDescriptor q_code r_0 m_max) (h_valid : ValidDescriptorField D_field)
    (sys : SysCSS[L, q_code, m_max])
    (h_sys_checks : ∀ idx, sys.checkProj idx = staticCSSCheckProj D_field idx ∧
      sys.support idx = staticCSSCheckSupport D_field idx ∧ sys.weight idx = 1)
    (h_tqo1 : SatisfiesTQO1 sys L_star) (h_tqo2 : SatisfiesSectorFilteredLinearTQO2 sys 1 L_star C_RCA)
    (hR_le : R_cut ≤ L_star) (V : QuasiLocalPerturbation 3 L (SiteCSS[L, q_code]))
    (hV_supp : ∀ r ∈ Finset.Icc 1 (min R_cut L), ∀ A ∈ boxCubes 3 L r,
      IsSupportedOn (SiteCSS[L, q_code]) A (V.term r A))
    (γ : WorldlineDysonPolymer L q_code) (hγ : IsValidWorldlinePolymer D_field sys C_RCA R_cut γ)
    {σ : IdxCSS[L, q_code, m_max] → Bool} (hσ : σ ∈ realizableSyndromes D_field) :
    spanningSurfaceSign (worldlinePolymerSpanningSurface D_field sys C_RCA γ) σ *
      worldlinePolymerLoopAmplitude D_field sys C_RCA V γ
        (restrictSyndromeToCollar (worldlinePolymerNativeCollar sys C_RCA γ) σ) =
    hilbertTrace (sys.syndromeProjector σ *
      ((hermitianPauliZX (worldlinePolymerLogicalCoset D_field sys C_RCA γ).1
        (worldlinePolymerLogicalCoset D_field sys C_RCA γ).2)† *
        worldlinePolymerWeightedLoopOp D_field sys V γ)) /
      hilbertTrace (sys.syndromeProjector σ) := by
  unfold worldlinePolymerLoopAmplitude; (try dsimp only)
  rcases canonicalCollarRealizableSyndrome_spec
    D_field (worldlinePolymerNativeCollar sys C_RCA γ) hσ with ⟨hσ_rep_mem, _, hσ_rep_ag⟩
  have h_span := (isSpanningCheckSurfaceForPolymer_of_isValidWorldlinePolymer
    D_field h_valid sys h_sys_checks γ hγ).2
  generalize h_rep_def : canonicalCollarRealizableSyndrome D_field (worldlinePolymerNativeCollar sys C_RCA γ)
    (restrictSyndromeToCollar (worldlinePolymerNativeCollar sys C_RCA γ) σ) = σ_rep at hσ_rep_mem hσ_rep_ag ⊢
  generalize h_μ_def : worldlinePolymerLogicalCoset D_field sys C_RCA γ = μ at h_span ⊢
  generalize h_α_def : worldlinePolymerSpanningSurface D_field sys C_RCA γ = α at h_span ⊢
  generalize h_L_def : (hermitianPauliZX μ.1 μ.2)† * worldlinePolymerLoopOp γ = L_op
  have h_jumps_cond : ∀ ξ ∈ γ.1, 1 ≤ ξ.1.1 ∧ ξ.1.1 ≤ L_star ∧ ξ.1.2 ∈ boxCubes 3 L ξ.1.1 ∧
      IsSupportedOn (SiteCSS[L, q_code]) ξ.1.2 (V.term ξ.1.1 ξ.1.2) ∧
      (∀ slot : BoxSlot3D L q_code, ξ.2.1 slot ≠ 0 ∨ ξ.2.2 slot ≠ 0 → slot.1 ∈ ξ.1.2) ∧
      staticCSSPauliFlip D_field ξ.2.1 ξ.2.2 ≠ (fun _ => false) := by
    intro ξ hξ
    have hp_mem : ξ.1 ∈ worldlinePolymerMonomers γ :=
      Finset.mem_union_left _ (List.mem_toFinset.mpr (List.mem_map_of_mem hξ))
    rcases mem_scaleCubeFinset_iff.mp (hγ.1 ξ.1 hp_mem) with ⟨hr, hA⟩
    rcases Finset.mem_Icc.mp hr with ⟨hr1, hr_min⟩
    exact ⟨hr1, le_trans hr_min (le_trans (Nat.min_le_left R_cut L) hR_le),
      hA, hV_supp ξ.1.1 hr ξ.1.2 hA, (hγ.2.1 ξ hξ).1, (hγ.2.1 ξ hξ).2.1⟩
  rcases exists_collar_scalar_list_prod_reverse_worldlineSyndromeShiftBlockOp_eq_smul_worldlineJumpOp
      D_field h_valid sys h_sys_checks h_tqo1 h_tqo2 V γ.1 h_jumps_cond with ⟨C_jumps, hC_ag, hC_eq⟩
  have hC_rep_eq : C_jumps σ_rep = C_jumps σ :=
    hC_ag σ_rep σ fun ξ hξ c hc => hσ_rep_ag c (Finset.mem_biUnion.mpr
      ⟨ξ.1, Finset.mem_union_left _ (List.mem_toFinset.mpr (List.mem_map_of_mem hξ)), hc⟩)
  have h_res := PerturbedThermalBarrier.syndrome_resolution_indexed sys
  have h_tr_reduce : ∀ η ∈ realizableSyndromes D_field,
      hilbertTrace (sys.syndromeProjector η *
        ((hermitianPauliZX μ.1 μ.2)† * worldlinePolymerWeightedLoopOp D_field sys V γ)) =
      (C_jumps η).re * hilbertTrace (sys.syndromeProjector η * L_op) +
        (C_jumps η).im * hilbertTrace (sys.syndromeProjector η * (Complex.I • L_op)) := by
    intro η hη
    have h_idem := (h_res.2.1 η).1
    have h_op_eq : sys.syndromeProjector η *
        ((hermitianPauliZX μ.1 μ.2)† * worldlinePolymerWeightedLoopOp D_field sys V γ) *
        sys.syndromeProjector η = sys.syndromeProjector η * (C_jumps η • L_op) * sys.syndromeProjector η := by
      calc sys.syndromeProjector η * ((hermitianPauliZX μ.1 μ.2)† * worldlinePolymerWeightedLoopOp D_field sys V γ) *
            sys.syndromeProjector η
        _ = sys.syndromeProjector η * (hermitianPauliZX μ.1 μ.2)† *
              (worldlinePolymerWeightedLoopOp D_field sys V γ * sys.syndromeProjector η) := by simp only [mul_assoc]
        _ = sys.syndromeProjector η * (hermitianPauliZX μ.1 μ.2)† *
              (C_jumps η • (worldlinePolymerLoopOp γ * sys.syndromeProjector η)) :=
              congrArg (sys.syndromeProjector η * (hermitianPauliZX μ.1 μ.2)† * ·) (hC_eq η hη)
        _ = sys.syndromeProjector η * (C_jumps η • L_op) * sys.syndromeProjector η := by
              rw [clm_mul_smul, clm_mul_smul, clm_smul_mul, ← h_L_def]; simp only [mul_assoc]
    have h_cyc : ∀ M : ℬ_CSS[L, q_code],
        hilbertTrace (sys.syndromeProjector η * M * sys.syndromeProjector η) =
          hilbertTrace (sys.syndromeProjector η * M) := fun M => by
      conv_lhs => rw [hilbertTrace_mul_comm_aux _ (sys.syndromeProjector η), ← mul_assoc, h_idem]
    rw [← h_cyc, h_op_eq, h_cyc (C_jumps η • L_op),
      (hilbertTrace_add_and_complex_smul_decomp 0 0 (sys.syndromeProjector η) L_op 0 (C_jumps η)).2.2]
  have h_span_rep := h_span.2 σ_rep hσ_rep_mem
  have h_span_σ := h_span.2 σ hσ
  rw [h_L_def] at h_span_rep h_span_σ
  have h_tr_denom_rep := (hilbertTrace_syndromeProjector_eq_P0_of_realizableSyndromes
    D_field h_valid sys h_sys_checks hσ_rep_mem).1
  have h_tr_denom_σ := (hilbertTrace_syndromeProjector_eq_P0_of_realizableSyndromes
    D_field h_valid sys h_sys_checks hσ).1
  have h_sign_sq : spanningSurfaceSign α σ_rep * spanningSurfaceSign α σ_rep = 1 :=
    (spanningSurfaceSign_insert_and_identities α σ_rep).2.1
  rw [h_tr_reduce σ_rep hσ_rep_mem, h_tr_reduce σ hσ, hC_rep_eq,
    h_span_rep.1, h_span_rep.2, h_span_σ.1, h_span_σ.2, h_tr_denom_rep, h_tr_denom_σ]
  have h_factor : spanningSurfaceSign α σ_rep *
      ((C_jumps σ).re * (spanningSurfaceSign α σ_rep * hilbertTrace (sys.P0 * L_op)) +
        (C_jumps σ).im * (spanningSurfaceSign α σ_rep * hilbertTrace (sys.P0 * (Complex.I • L_op)))) =
      (spanningSurfaceSign α σ_rep * spanningSurfaceSign α σ_rep) *
        ((C_jumps σ).re * hilbertTrace (sys.P0 * L_op) +
          (C_jumps σ).im * hilbertTrace (sys.P0 * (Complex.I • L_op))) := by ring
  rw [h_factor, h_sign_sq, one_mul, ← mul_div_assoc]
  congr 1; ring

/-- For every valid worldline polymer $\gamma$ and every syndrome-closed Pauli pair
$\nu \in \text{syndromeClosedPauliFinset } D\_\text{field}$, the symplectic character of
`worldlinePolymerLogicalCoset D_field sys C_RCA γ` equals that of `(worldlinePolymerLoopX γ, worldlinePolymerLoopZ γ)`. -/
lemma symplecticPauliSign_worldlinePolymerLogicalCoset_eq_loop
    {L q_code r_0 m_max R_cut : ℕ} [NeZero L] {C_RCA : ℝ}
    (D_field : Box3D L → LocalCSSDescriptor q_code r_0 m_max) (h_valid : ValidDescriptorField D_field)
    (sys : SysCSS[L, q_code, m_max])
    (h_sys_checks : ∀ idx, sys.checkProj idx = staticCSSCheckProj D_field idx ∧
      sys.support idx = staticCSSCheckSupport D_field idx ∧ sys.weight idx = 1)
    {γ : WorldlineDysonPolymer L q_code} (hγ : IsValidWorldlinePolymer D_field sys C_RCA R_cut γ)
    {ν : PauliBitstringPair L q_code} (hν : ν ∈ syndromeClosedPauliFinset D_field) :
    symplecticPauliSign ν (worldlinePolymerLogicalCoset D_field sys C_RCA γ) =
      symplecticPauliSign ν (worldlinePolymerLoopX γ, worldlinePolymerLoopZ γ) := by
  have h_span := (isSpanningCheckSurfaceForPolymer_of_isValidWorldlinePolymer
    D_field h_valid sys h_sys_checks γ hγ).2
  let μ := worldlinePolymerLogicalCoset D_field sys C_RCA γ
  let a := worldlinePolymerLoopX γ; let b := worldlinePolymerLoopZ γ
  let L_op := (hermitianPauliZX μ.1 μ.2)† * worldlinePolymerLoopOp γ
  let U := weylPauliZ ν.1 * weylPauliX ν.2; let U_inv := weylPauliX ν.2 * weylPauliZ ν.1
  have hU_right : U * U_inv = 1 := by
    calc (weylPauliZ ν.1 * weylPauliX ν.2) * (weylPauliX ν.2 * weylPauliZ ν.1)
      _ = weylPauliZ ν.1 * (weylPauliX ν.2 * weylPauliX ν.2) * weylPauliZ ν.1 := by simp only [mul_assoc]
      _ = 1 := by rw [weylPauliX_sq_eq_one ν.2, mul_one, weylPauliZ_sq_eq_one ν.1]
  have hU_left : U_inv * U = 1 := by
    calc (weylPauliX ν.2 * weylPauliZ ν.1) * (weylPauliZ ν.1 * weylPauliX ν.2)
      _ = weylPauliX ν.2 * (weylPauliZ ν.1 * weylPauliZ ν.1) * weylPauliX ν.2 := by simp only [mul_assoc]
      _ = 1 := by rw [weylPauliZ_sq_eq_one ν.1, mul_one, weylPauliX_sq_eq_one ν.2]
  have hU_P0 : sys.P0 * U = U * sys.P0 :=
    (weylPauliZX_comm_checkProj_and_syndromeProjector_of_syndromeClosed D_field sys h_sys_checks hν).2.2.symm.eq
  have h_pauli_comm : ∀ x y : BoxSlot3D L q_code → ZMod 2,
      (weylPauliZ x * weylPauliX y) * U =
        ((symplecticPauliSign ν (x, y) : ℝ) : ℂ) • (U * (weylPauliZ x * weylPauliX y)) := fun x y => by
    rw [weylPauliZX_comm_signScalar x y ν.1 ν.2,
      ← (signScalar_symplectic_eq_symplecticPauliSign_and_mul ν ν ν (x, y) (x, y) (x, y)).1]
    exact congrArg (· • (U * (weylPauliZ x * weylPauliX y)))
      (congrArg signScalar (Finset.sum_congr rfl fun _ _ => by ring))
  have h_herm_comm : (hermitianPauliZX μ.1 μ.2)† * U =
      ((symplecticPauliSign ν μ : ℝ) : ℂ) • (U * (hermitianPauliZX μ.1 μ.2)†) := by
    rw [ContinuousLinearMap.isSelfAdjoint_iff'.mp (hermitianPauliZX_isSelfAdjoint_and_sq_eq_one μ.1 μ.2).1]
    dsimp [hermitianPauliZX]; split_ifs
    · exact h_pauli_comm μ.1 μ.2
    · rw [clm_smul_mul, h_pauli_comm μ.1 μ.2, clm_mul_smul, smul_comm]
  have h_loop_comm : worldlinePolymerLoopOp γ * U =
      ((symplecticPauliSign ν (a, b) : ℝ) : ℂ) • (U * worldlinePolymerLoopOp γ) := by
    rcases list_prod_map_worldlineJumpOpZX_eq_signScalar_smul γ.1.reverse with ⟨s_loop, hs_loop⟩
    have h_sum_X : (γ.1.reverse.map (fun ξ => ξ.2.1)).sum = a := by
      dsimp [a, worldlinePolymerLoopX]; rw [List.map_reverse, List.sum_reverse]
    have h_sum_Z : (γ.1.reverse.map (fun ξ => ξ.2.2)).sum = b := by
      dsimp [b, worldlinePolymerLoopZ]; rw [List.map_reverse, List.sum_reverse]
    rw [h_sum_X, h_sum_Z] at hs_loop
    change worldlinePolymerLoopOpZX γ * U = ((symplecticPauliSign ν (a, b) : ℝ) : ℂ) • (U * worldlinePolymerLoopOpZX γ)
    unfold worldlinePolymerLoopOpZX; rw [hs_loop, clm_smul_mul, h_pauli_comm a b, clm_mul_smul, smul_comm]
  have h_L_comm : ∀ w : ℂ, (w • L_op) * U =
      (((symplecticPauliSign ν μ * symplecticPauliSign ν (a, b) : ℝ) : ℂ)) • (U * (w • L_op)) := fun w => by
    calc (w • L_op) * U
      _ = w • ((hermitianPauliZX μ.1 μ.2)† * (worldlinePolymerLoopOp γ * U)) := by dsimp [L_op]; rw [clm_smul_mul, mul_assoc]
      _ = w • (((symplecticPauliSign ν (a, b) : ℝ) : ℂ) • (((hermitianPauliZX μ.1 μ.2)† * U) * worldlinePolymerLoopOp γ)) := by
          rw [h_loop_comm, clm_mul_smul, ← mul_assoc]
      _ = (((symplecticPauliSign ν μ * symplecticPauliSign ν (a, b) : ℝ) : ℂ)) • (U * (w • L_op)) := by
          rw [h_herm_comm, clm_smul_mul, clm_mul_smul, smul_smul, smul_smul, smul_smul]
          dsimp [L_op]; rw [mul_assoc]; congr 1; push_cast; ring
  have h_tr_conj : ∀ w : ℂ, hilbertTrace (sys.P0 * (w • L_op)) =
      (symplecticPauliSign ν μ * symplecticPauliSign ν (a, b)) * hilbertTrace (sys.P0 * (w • L_op)) := fun w => by
    calc hilbertTrace (sys.P0 * (w • L_op))
      _ = hilbertTrace ((sys.P0 * ((w • L_op) * U)) * U_inv) := by
          conv_lhs => rw [← mul_one (sys.P0 * (w • L_op)), ← hU_right]
          simp only [mul_assoc]
      _ = (symplecticPauliSign ν μ * symplecticPauliSign ν (a, b)) *
            hilbertTrace ((U * (sys.P0 * (w • L_op))) * U_inv) := by
          rw [h_L_comm w, clm_mul_smul, clm_smul_mul,
            (hilbertTrace_add_and_complex_smul_decomp _ 0 0 0 (symplecticPauliSign ν μ * symplecticPauliSign ν (a, b)) 0).2.1,
            ← mul_assoc sys.P0 U, hU_P0, mul_assoc U sys.P0]
      _ = (symplecticPauliSign ν μ * symplecticPauliSign ν (a, b)) * hilbertTrace (sys.P0 * (w • L_op)) := by
          rw [hilbertTrace_mul_comm_aux (U * (sys.P0 * (w • L_op))) U_inv, ← mul_assoc U_inv U, hU_left, one_mul]
  have h_prod_one : symplecticPauliSign ν μ * symplecticPauliSign ν (a, b) = 1 := by
    rcases h_span.1 with h_ne1 | h_neI
    · have h1 := h_tr_conj 1; rw [one_smul] at h1; exact mul_right_cancel₀ h_ne1 (h1.symm.trans (one_mul _).symm)
    · exact mul_right_cancel₀ h_neI ((h_tr_conj Complex.I).symm.trans (one_mul _).symm)
  have h_sq_ab : symplecticPauliSign ν (a, b) * symplecticPauliSign ν (a, b) = 1 := by
    unfold symplecticPauliSign; split_ifs <;> ring
  calc symplecticPauliSign ν μ
    _ = (symplecticPauliSign ν μ * symplecticPauliSign ν (a, b)) * symplecticPauliSign ν (a, b) := by
        rw [mul_assoc, h_sq_ab, mul_one]
    _ = symplecticPauliSign ν (a, b) := by rw [h_prod_one, one_mul]

end DirectWorldlineCluster
end
