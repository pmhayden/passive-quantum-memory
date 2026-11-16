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

import Proofs.SpacetimeWorldlineKP.PeriodicWorldlineDysonExpansion

/-!
# Space-Time Cell Adjacency Degrees, Arborescence Resummation, and Monomer Activities

Proves the abstract finite-subset Dobrushin–Kotecký–Preiss partition-ratio induction (`kotecky_preiss_partition_ratio_le`, `kotecky_preiss_partition_sdiff_le`) and pinned witness bound (`polymerPinnedSum_eq_prod_mul_partitionZ`, `kotecky_preiss_pinned_witness_bound`). Constructs the space-time check-slice polymer graph (`KPSpacetimeGridCell`, `KPFinTimeSliceAdj`, `KPSpacetimeCellAdj`, `KPScaleCubeOverlap`), bounds RCA collar check multiplicities (`kpRCACollarCube`, `kpRCACollarChecks`, `kpRCADiagNat`, `card_kpRCACollarChecks_le`), and resums Penrose arborescence forests recursively (`forestPolymerSum_le_kpForestWeight`) to verify the space-time Kotecký–Preiss witness ratio bound.

## References

* Part II, Sections 3.4–3.5 (`subsec:cluster-primer`, `subsec:worldline-expansion`), Proposition 3.10 (`prop:tube-local-ursell-erasure`)
* Kotecký–Preiss (1986), Cluster expansion for abstract polymer models
-/

noncomputable section

open scoped Classical BigOperators InnerProduct ComplexConjugate
open Filter Topology Asymptotics ContinuousLinearMap KMSPinchedGibbs PerturbedThermalBarrier

set_option linter.constructorNameAsVariable false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000

instance : Fact (1 < 2) := ⟨by decide⟩
@[simp] lemma zmod2_val_one : (1 : ZMod 2).val = 1 := rfl

/-- Insertion recursion for `polymerPartitionZ` at $\gamma_0 \notin \Lambda$. -/
private theorem polymerPartitionZ_insert_eq {Polymer : Type*} [DecidableEq Polymer]
    (compat : Polymer → Polymer → Prop) (w : Polymer → ℝ)
    (h_symm : ∀ γ₁ γ₂ : Polymer, compat γ₁ γ₂ → compat γ₂ γ₁)
    (Λ : Finset Polymer) {γ₀ : Polymer} (hγ₀ : γ₀ ∉ Λ) :
    polymerPartitionZ compat w (insert γ₀ Λ) =
      polymerPartitionZ compat w Λ +
        w γ₀ * polymerPartitionZ compat w (Λ.filter (fun γ => compat γ₀ γ)) := by
  unfold polymerPartitionZ
  let S := (insert γ₀ Λ).powerset.filter (IsCompatiblePolymerSet compat)
  let Λ' := Λ.filter (fun γ => compat γ₀ γ)
  rw [← Finset.sum_filter_add_sum_filter_not S (fun G => γ₀ ∈ G) (fun G => ∏ γ ∈ G, w γ), add_comm]
  have h_not_in : S.filter (fun G => γ₀ ∉ G) = Λ.powerset.filter (IsCompatiblePolymerSet compat) := by
    ext G; simp only [S, Finset.mem_filter, Finset.mem_powerset]
    refine ⟨fun ⟨⟨hG_sub, hG_compat⟩, hγ₀_not⟩ => ⟨(Finset.subset_insert_iff_of_notMem hγ₀_not).mp hG_sub, hG_compat⟩,
      fun ⟨hG_sub, hG_compat⟩ => ⟨⟨Finset.Subset.trans hG_sub (Finset.subset_insert γ₀ Λ), hG_compat⟩, fun h_in => hγ₀ (hG_sub h_in)⟩⟩
  rw [h_not_in, Finset.mul_sum]; congr 1; symm
  refine Finset.sum_bij (fun G_rest _ => insert γ₀ G_rest) ?_ ?_ ?_ ?_
  · intro G_rest hG_rest
    rcases Finset.mem_filter.mp hG_rest with ⟨hG_pow, hG_compat⟩
    have hG_sub_Λ' : G_rest ⊆ Λ' := Finset.mem_powerset.mp hG_pow
    have hG_sub_Λ : G_rest ⊆ Λ := Finset.Subset.trans hG_sub_Λ' (Finset.filter_subset _ Λ)
    refine Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr (Finset.insert_subset_insert γ₀ hG_sub_Λ), ?_⟩,
      Finset.mem_insert_self γ₀ G_rest⟩
    intro γ₁ h₁ γ₂ h₂ hne
    rcases Finset.mem_insert.mp h₁ with rfl | h₁_rest <;> rcases Finset.mem_insert.mp h₂ with rfl | h₂_rest
    · exact False.elim (hne rfl)
    · exact (Finset.mem_filter.mp (hG_sub_Λ' h₂_rest)).2
    · exact h_symm γ₂ γ₁ (Finset.mem_filter.mp (hG_sub_Λ' h₁_rest)).2
    · exact hG_compat γ₁ h₁_rest γ₂ h₂_rest hne
  · intro G₁ hG₁ G₂ hG₂ h_eq
    have h₁_sub := Finset.Subset.trans (Finset.mem_powerset.mp (Finset.mem_filter.mp hG₁).1) (Finset.filter_subset _ Λ)
    have h₂_sub := Finset.Subset.trans (Finset.mem_powerset.mp (Finset.mem_filter.mp hG₂).1) (Finset.filter_subset _ Λ)
    calc G₁ = (insert γ₀ G₁).erase γ₀ := (Finset.erase_insert fun h => hγ₀ (h₁_sub h)).symm
      _ = (insert γ₀ G₂).erase γ₀ := by rw [h_eq]
      _ = G₂ := Finset.erase_insert fun h => hγ₀ (h₂_sub h)
  · intro G hG
    rcases Finset.mem_filter.mp hG with ⟨hG_S, hγ₀_in⟩
    rcases Finset.mem_filter.mp hG_S with ⟨hG_pow, hG_compat⟩
    have hG_sub : G ⊆ insert γ₀ Λ := Finset.mem_powerset.mp hG_pow
    refine ⟨G.erase γ₀, Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr ?_, hG_compat.mono (Finset.erase_subset γ₀ G)⟩,
      Finset.insert_erase hγ₀_in⟩
    intro γ hγ; rcases Finset.mem_erase.mp hγ with ⟨hne, hγ_G⟩
    rcases Finset.mem_insert.mp (hG_sub hγ_G) with rfl | h_in_Λ
    · exact False.elim (hne rfl)
    · exact Finset.mem_filter.mpr ⟨h_in_Λ, hG_compat γ₀ hγ₀_in γ hγ_G (Ne.symm hne)⟩
  · intro G_rest hG_rest
    have hG_sub := Finset.Subset.trans (Finset.mem_powerset.mp (Finset.mem_filter.mp hG_rest).1) (Finset.filter_subset _ Λ)
    exact (Finset.prod_insert fun h => hγ₀ (hG_sub h)).symm

/-- Deletion-inclusion recursion for `polymerPartitionZ` at $\gamma_0 \in \Lambda$. -/
theorem polymerPartitionZ_eq_erase_add {Polymer : Type*} [DecidableEq Polymer]
    (compat : Polymer → Polymer → Prop) (w : Polymer → ℝ)
    (h_symm : ∀ γ₁ γ₂ : Polymer, compat γ₁ γ₂ → compat γ₂ γ₁)
    (h_irrefl : ∀ γ : Polymer, ¬compat γ γ)
    (Λ : Finset Polymer) {γ₀ : Polymer} (hγ₀ : γ₀ ∈ Λ) :
    polymerPartitionZ compat w Λ =
      polymerPartitionZ compat w (Λ.erase γ₀) +
        w γ₀ * polymerPartitionZ compat w (Λ.filter (fun γ => compat γ₀ γ)) := by
  have h_filt : (Λ.erase γ₀).filter (fun γ => compat γ₀ γ) = Λ.filter (fun γ => compat γ₀ γ) := by
    ext γ; simp only [Finset.mem_filter, Finset.mem_erase]
    refine ⟨fun ⟨⟨_, h_mem⟩, h_c⟩ => ⟨h_mem, h_c⟩, fun ⟨h_mem, h_c⟩ => ⟨⟨fun h_eq => h_irrefl γ₀ (h_eq ▸ h_c), h_mem⟩, h_c⟩⟩
  calc polymerPartitionZ compat w Λ
    _ = polymerPartitionZ compat w (insert γ₀ (Λ.erase γ₀)) := by rw [Finset.insert_erase hγ₀]
    _ = polymerPartitionZ compat w (Λ.erase γ₀) +
          w γ₀ * polymerPartitionZ compat w ((Λ.erase γ₀).filter (fun γ => compat γ₀ γ)) :=
        polymerPartitionZ_insert_eq compat w h_symm (Λ.erase γ₀) (Finset.notMem_erase γ₀ Λ)
    _ = polymerPartitionZ compat w (Λ.erase γ₀) +
          w γ₀ * polymerPartitionZ compat w (Λ.filter (fun γ => compat γ₀ γ)) := by rw [h_filt]

/-- Single-step Dobrushin–Kotecký–Preiss partition-ratio inequality (`kotecky_preiss_partition_ratio_le`,
Part II, Proposition 3.10 (`prop:tube-local-ursell-erasure`)). -/
theorem kotecky_preiss_partition_ratio_le {Polymer : Type*} [Fintype Polymer] [DecidableEq Polymer]
    {compat : Polymer → Polymer → Prop} {w a d : Polymer → ℝ}
    (h_kp : SatisfiesKoteckyPreissCondition compat w a d)
    (Λ : Finset Polymer) (γ₀ : Polymer) :
    polymerPartitionZ compat w Λ ≤
      Real.exp (a γ₀) * polymerPartitionZ compat w (Λ.erase γ₀) := by
  rcases h_kp with ⟨h_symm, h_irrefl, h_nonneg, h_kp_sum⟩
  have hw : ∀ γ : Polymer, 0 ≤ w γ := fun γ => (h_nonneg γ).1
  have ha0 : 0 ≤ a γ₀ := (h_nonneg γ₀).2.1
  have hd0 : 0 ≤ d γ₀ := (h_nonneg γ₀).2.2
  have hZ_erase_pos : 0 < polymerPartitionZ compat w (Λ.erase γ₀) :=
    polymerPartitionZ_pos compat hw (Λ.erase γ₀)
  by_cases hγ₀ : γ₀ ∈ Λ
  · have h_rec := polymerPartitionZ_eq_erase_add compat w h_symm h_irrefl Λ hγ₀
    have h_sub : Λ.filter (fun γ => compat γ₀ γ) ⊆ Λ.erase γ₀ := fun γ hγ =>
      Finset.mem_erase.mpr ⟨fun h_eq => h_irrefl γ₀ (h_eq ▸ (Finset.mem_filter.mp hγ).2),
        (Finset.mem_filter.mp hγ).1⟩
    have hZ_mono := polymerPartitionZ_mono compat hw h_sub
    have hγ₀_in_incompat : γ₀ ∈ Finset.univ.filter (fun γ' => ¬compat γ₀ γ') :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ γ₀, h_irrefl γ₀⟩
    have hw_exp_le_sum := Finset.single_le_sum (f := fun γ' : Polymer => w γ' * Real.exp (a γ' + d γ'))
      (fun γ' _ => mul_nonneg (hw γ') (le_of_lt (Real.exp_pos (a γ' + d γ')))) hγ₀_in_incompat
    have hw_le_a : w γ₀ ≤ a γ₀ := by
      have h_one_le_exp : 1 ≤ Real.exp (a γ₀ + d γ₀) := Real.one_le_exp (by linarith)
      have hw_le_prod : w γ₀ ≤ w γ₀ * Real.exp (a γ₀ + d γ₀) := by nlinarith [hw γ₀]
      linarith [h_kp_sum γ₀]
    have h_one_add_a : 1 + a γ₀ ≤ Real.exp (a γ₀) := by linarith [Real.add_one_le_exp (a γ₀)]
    calc polymerPartitionZ compat w Λ
      _ = polymerPartitionZ compat w (Λ.erase γ₀) +
            w γ₀ * polymerPartitionZ compat w (Λ.filter (fun γ => compat γ₀ γ)) := h_rec
      _ ≤ (1 + w γ₀) * polymerPartitionZ compat w (Λ.erase γ₀) := by nlinarith [hw γ₀]
      _ ≤ (1 + a γ₀) * polymerPartitionZ compat w (Λ.erase γ₀) := by nlinarith [le_of_lt hZ_erase_pos]
      _ ≤ Real.exp (a γ₀) * polymerPartitionZ compat w (Λ.erase γ₀) :=
          mul_le_mul_of_nonneg_right h_one_add_a (le_of_lt hZ_erase_pos)
  · rw [Finset.erase_eq_of_notMem hγ₀]
    have h_one_le : 1 ≤ Real.exp (a γ₀) := Real.one_le_exp ha0
    have hZ_nonneg := le_of_lt (polymerPartitionZ_pos compat hw Λ)
    nlinarith

/-- Iterated Dobrushin–Kotecký–Preiss partition-ratio inequality over finite subsets
(`kotecky_preiss_partition_sdiff_le`, Part II, Proposition 3.10 (`prop:tube-local-ursell-erasure`)). -/
theorem kotecky_preiss_partition_sdiff_le {Polymer : Type*} [Fintype Polymer] [DecidableEq Polymer]
    {compat : Polymer → Polymer → Prop} {w a d : Polymer → ℝ}
    (h_kp : SatisfiesKoteckyPreissCondition compat w a d)
    (Λ I : Finset Polymer) :
    polymerPartitionZ compat w Λ ≤
      Real.exp (∑ γ ∈ I, a γ) * polymerPartitionZ compat w (Λ \ I) := by
  induction I using Finset.induction_on generalizing Λ with
  | empty => simp
  | @insert γ₀ I hγ₀ ih =>
    have h_sdiff : Λ \ insert γ₀ I = (Λ.erase γ₀) \ I := by
      ext x; simp only [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_erase, not_or]; tauto
    calc polymerPartitionZ compat w Λ
      _ ≤ Real.exp (a γ₀) * polymerPartitionZ compat w (Λ.erase γ₀) :=
          kotecky_preiss_partition_ratio_le h_kp Λ γ₀
      _ ≤ Real.exp (a γ₀) * (Real.exp (∑ γ ∈ I, a γ) * polymerPartitionZ compat w ((Λ.erase γ₀) \ I)) :=
          mul_le_mul_of_nonneg_left (ih (Λ.erase γ₀)) (le_of_lt (Real.exp_pos _))
      _ = Real.exp (∑ γ ∈ insert γ₀ I, a γ) * polymerPartitionZ compat w (Λ \ insert γ₀ I) := by
          rw [Finset.sum_insert hγ₀, Real.exp_add, mul_assoc, h_sdiff]

/-- Factorization of a pinned compatible-polymer sum (`polymerPinnedSum_eq_prod_mul_partitionZ`). -/
theorem polymerPinnedSum_eq_prod_mul_partitionZ {Polymer : Type*} [DecidableEq Polymer]
    (compat : Polymer → Polymer → Prop) (w : Polymer → ℝ)
    (h_symm : ∀ γ₁ γ₂ : Polymer, compat γ₁ γ₂ → compat γ₂ γ₁)
    {Λ G_pin : Finset Polymer} (h_sub : G_pin ⊆ Λ) (h_compat : IsCompatiblePolymerSet compat G_pin) :
    polymerPinnedSum compat w Λ G_pin =
      (∏ γ ∈ G_pin, w γ) *
        polymerPartitionZ compat w (Λ.filter (fun γ' => γ' ∉ G_pin ∧ ∀ γ ∈ G_pin, compat γ γ')) := by
  unfold polymerPinnedSum polymerPartitionZ; rw [Finset.mul_sum]; symm
  refine Finset.sum_bij (fun G_rest _ => G_pin ∪ G_rest) ?_ ?_ ?_ ?_
  · intro G_rest hG_rest
    rcases Finset.mem_filter.mp hG_rest with ⟨hG_pow, hG_compat⟩
    have hG_sub_filt := Finset.mem_powerset.mp hG_pow
    have hG_sub_Λ := Finset.Subset.trans hG_sub_filt (Finset.filter_subset _ Λ)
    refine Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr (Finset.union_subset h_sub hG_sub_Λ), ?_⟩,
      Finset.subset_union_left⟩
    intro γ₁ h₁ γ₂ h₂ hne
    rcases Finset.mem_union.mp h₁ with h₁_pin | h₁_rest <;> rcases Finset.mem_union.mp h₂ with h₂_pin | h₂_rest
    · exact h_compat γ₁ h₁_pin γ₂ h₂_pin hne
    · exact (Finset.mem_filter.mp (hG_sub_filt h₂_rest)).2.2 γ₁ h₁_pin
    · exact h_symm γ₂ γ₁ ((Finset.mem_filter.mp (hG_sub_filt h₁_rest)).2.2 γ₂ h₂_pin)
    · exact hG_compat γ₁ h₁_rest γ₂ h₂_rest hne
  · intro G₁ hG₁ G₂ hG₂ h_eq
    have h₁_sub := Finset.mem_powerset.mp (Finset.mem_filter.mp hG₁).1
    have h₂_sub := Finset.mem_powerset.mp (Finset.mem_filter.mp hG₂).1
    ext x
    have hx₁ : x ∈ G₁ → x ∉ G_pin := fun hx => (Finset.mem_filter.mp (h₁_sub hx)).2.1
    have hx₂ : x ∈ G₂ → x ∉ G_pin := fun hx => (Finset.mem_filter.mp (h₂_sub hx)).2.1
    have h_u : x ∈ G_pin ∪ G₁ ↔ x ∈ G_pin ∪ G₂ := by rw [h_eq]
    simp only [Finset.mem_union] at h_u; tauto
  · intro G hG
    rcases Finset.mem_filter.mp hG with ⟨hG_filt, hG_pin_sub⟩
    rcases Finset.mem_filter.mp hG_filt with ⟨hG_pow, hG_compat⟩
    have hG_sub_Λ := Finset.mem_powerset.mp hG_pow
    refine ⟨G \ G_pin, Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr ?_, hG_compat.mono Finset.sdiff_subset⟩,
      Finset.union_sdiff_of_subset hG_pin_sub⟩
    intro γ' hγ'; rcases Finset.mem_sdiff.mp hγ' with ⟨hγ'_G, hγ'_not_pin⟩
    refine Finset.mem_filter.mpr ⟨hG_sub_Λ hγ'_G, hγ'_not_pin, fun γ hγ_pin => ?_⟩
    exact hG_compat γ (hG_pin_sub hγ_pin) γ' hγ'_G (fun h => by subst h; exact hγ'_not_pin hγ_pin)
  · intro G_rest hG_rest
    have hG_sub_filt := Finset.mem_powerset.mp (Finset.mem_filter.mp hG_rest).1
    exact (Finset.prod_union (Finset.disjoint_right.mpr fun γ' hγ' => (Finset.mem_filter.mp (hG_sub_filt hγ')).2.1)).symm

/-- Kotecký–Preiss pinned polymer ratio bound (`kotecky_preiss_pinned_witness_bound`,
Part II, Proposition 3.10 (`prop:tube-local-ursell-erasure`)). -/
theorem kotecky_preiss_pinned_witness_bound {Polymer : Type*} [Fintype Polymer] [DecidableEq Polymer]
    {compat : Polymer → Polymer → Prop} {w a d : Polymer → ℝ}
    (h_kp : SatisfiesKoteckyPreissCondition compat w a d)
    (G_pin : Finset Polymer) (h_compat : IsCompatiblePolymerSet compat G_pin)
    (h_w_le : ∀ γ ∈ G_pin, w γ * Real.exp (a γ + d γ) ≤ 1) :
    polymerPinnedSum compat w Finset.univ G_pin ≤
      Real.exp (-(∑ γ ∈ G_pin, d γ)) * polymerPartitionZ compat w Finset.univ := by
  rcases h_kp with ⟨h_symm, _, h_nonneg, _⟩
  have hw : ∀ γ : Polymer, 0 ≤ w γ := fun γ => (h_nonneg γ).1
  have h_prod_le : (∏ γ ∈ G_pin, w γ) ≤ Real.exp (-(∑ γ ∈ G_pin, d γ)) := by
    have h_term : ∀ γ ∈ G_pin, w γ ≤ Real.exp (-d γ) := fun γ hγ => by
      have ha : 0 ≤ a γ := (h_nonneg γ).2.1
      have h_mul : w γ * Real.exp (d γ) ≤ 1 :=
        le_trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by linarith)) (hw γ)) (h_w_le γ hγ)
      calc w γ = (w γ * Real.exp (d γ)) * Real.exp (-d γ) := by
            rw [mul_assoc, ← Real.exp_add, add_neg_cancel, Real.exp_zero, mul_one]
        _ ≤ 1 * Real.exp (-d γ) := mul_le_mul_of_nonneg_right h_mul (le_of_lt (Real.exp_pos (-d γ)))
        _ = Real.exp (-d γ) := one_mul _
    calc ∏ γ ∈ G_pin, w γ
      _ ≤ ∏ γ ∈ G_pin, Real.exp (-d γ) := Finset.prod_le_prod₀ (fun i _ => hw i) h_term
      _ = Real.exp (∑ γ ∈ G_pin, -d γ) := (Real.exp_sum G_pin (fun γ => -d γ)).symm
      _ = Real.exp (-(∑ γ ∈ G_pin, d γ)) := by rw [Finset.sum_neg_distrib]
  rw [polymerPinnedSum_eq_prod_mul_partitionZ compat w h_symm (Finset.subset_univ G_pin) h_compat]
  exact mul_le_mul h_prod_le (polymerPartitionZ_mono compat hw (Finset.subset_univ _))
    (le_of_lt (polymerPartitionZ_pos compat hw _)) (le_of_lt (Real.exp_pos _))

namespace SpacetimeWorldlineKP

/-- Pointwise Boolean XOR of two syndrome configurations (`syndromeXor`). -/
def syndromeXor {ι : Type} (σ₁ σ₂ : ι → Bool) : ι → Bool :=
  fun i => bne (σ₁ i) (σ₂ i)

/-- Disjoint additivity of `syndromeEnergy` under `syndromeXor`. -/
theorem syndromeEnergy_syndromeXor_eq_add_of_disjoint
    {D L : ℕ} {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (sys : IndexedCommutingProjectorHamiltonian D L Site ι)
    {σ₁ σ₂ : ι → Bool}
    (h_disj : ∀ idx : ι, ¬(σ₁ idx = true ∧ σ₂ idx = true)) :
    sys.syndromeEnergy (syndromeXor σ₁ σ₂) =
      sys.syndromeEnergy σ₁ + sys.syndromeEnergy σ₂ := by
  unfold IndexedCommutingProjectorHamiltonian.syndromeEnergy
  have h_union :
      Finset.univ.filter (fun i : ι => syndromeXor σ₁ σ₂ i = true) =
        Finset.univ.filter (fun i : ι => σ₁ i = true) ∪
          Finset.univ.filter (fun i : ι => σ₂ i = true) := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union, syndromeXor]
    have h := h_disj i
    cases h1 : σ₁ i <;> cases h2 : σ₂ i <;> simp_all
  have h_disj_fin :
      Disjoint (Finset.univ.filter (fun i : ι => σ₁ i = true))
        (Finset.univ.filter (fun i : ι => σ₂ i = true)) := by
    rw [Finset.disjoint_left]
    intro i h1 h2
    exact h_disj i ⟨(Finset.mem_filter.mp h1).2, (Finset.mem_filter.mp h2).2⟩
  rw [h_union, Finset.sum_union h_disj_fin]

/-- **Static-vs-Jump Cardinality Dichotomy (`static_or_jump_half_card_le`)** -/
theorem static_or_jump_half_card_le
    {m n w_card α_stat α_jump : ℝ} (hm : 0 ≤ m) (hn : 0 ≤ n) (h_sum : w_card ≤ m + n)
    (hα_stat : 0 ≤ α_stat) (hα_jump : 0 ≤ α_jump) :
    ((1 / 2 : ℝ) * w_card ≤ m ∨ (1 / 2 : ℝ) * w_card ≤ n) ∧
    min α_stat α_jump * ((1 / 2 : ℝ) * w_card) ≤ α_stat * m + α_jump * n := by
  have h_or : (1 / 2 : ℝ) * w_card ≤ m ∨ (1 / 2 : ℝ) * w_card ≤ n := by
    by_cases hm_half : (1 / 2 : ℝ) * w_card ≤ m
    · exact Or.inl hm_half
    · exact Or.inr (by linarith)
  refine ⟨h_or, ?_⟩
  have h_min_nonneg : 0 ≤ min α_stat α_jump := le_min hα_stat hα_jump
  rcases h_or with hm_half | hn_half
  · linarith [mul_le_mul_of_nonneg_left hm_half h_min_nonneg,
      mul_le_mul_of_nonneg_right (min_le_left α_stat α_jump) hm, mul_nonneg hα_jump hn]
  · linarith [mul_le_mul_of_nonneg_left hn_half h_min_nonneg,
      mul_le_mul_of_nonneg_right (min_le_right α_stat α_jump) hn, mul_nonneg hα_stat hm]

/-- **Pinned Polymer Witness Ratio Bound (`pinned_polymer_witness_bound_of_kotecky_preiss`, Part II, Section 3.4 (`subsec:cluster-primer`), Proposition 3.10 (`prop:tube-local-ursell-erasure`))** -/
theorem pinned_polymer_witness_bound_of_kotecky_preiss {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    {ι : Type} [Fintype ι] [DecidableEq ι] (sys : IndexedCommutingProjectorHamiltonian D L Site ι)
    (H : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site) (hH : IsSelfAdjoint H) (β : ℝ)
    {Polymer : Type} [Fintype Polymer] [DecidableEq Polymer] (compat : Polymer → Polymer → Prop)
    {w a d a₀ : Polymer → ℝ} {W : Finset ι} {PinnedW : Finset Polymer}
    (h_maj : HasPolymerWitnessMajorant sys H hH β compat w a d W PinnedW) {α_KP : ℝ}
    (h_a0 : ∀ γ ∈ PinnedW, (∑ γ' ∈ Finset.univ.filter (fun γ' => ¬compat γ γ'), a γ') ≤ a₀ γ)
    (h_sum_le : (∑ γ ∈ PinnedW, w γ * Real.exp (a₀ γ)) ≤ Real.exp (-α_KP * (W.card : ℝ))) :
    gibbsFailureProb H hH β (positiveCheckWitnessProj sys W) ≤ Real.exp (-α_KP * (W.card : ℝ)) := by
  refine le_trans h_maj.2 (le_trans (Finset.sum_le_sum fun γ hγ => ?_) h_sum_le)
  exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (h_a0 γ hγ)) (h_maj.1.2.2.1 γ).1

/-! ## 1. Space-Time Cell Polymer Graph & Degree Bounds -/

abbrev kpCollarMaxCheckCard (R_pert r_0 w_0 : ℕ) (C_rca : ℝ) : ℕ :=
  (2 * (R_pert + 2 * linearExpansionRadius C_rca R_pert + r_0) + 1) ^ 3 * (w_0 + 1) + 1

abbrev kpRCACollarCube {L : ℕ} [NeZero L] (C_rca : ℝ) (r : ℕ) (A : Finset (Box3D L)) : Finset (Box3D L) :=
  enclosingBoxCube (anchorOfCube r A) r (linearExpansionRadius C_rca r)

abbrev kpRCACollarChecks {L q_code m_max : ℕ} [NeZero L]
    (sys : IndexedCommutingProjectorHamiltonian 3 L (UniformSite3D L (CodeSlotConfig q_code)) (StaticCSSCheckIdx L q_code m_max))
    (C_rca : ℝ) (r : ℕ) (A : Finset (Box3D L)) : Finset (StaticCSSCheckIdx L q_code m_max) :=
  Finset.univ.filter (fun c => sys.support c ⊆ kpRCACollarCube C_rca r A)

abbrev KPSpacetimeGridCell (L q_code m_max M : ℕ) : Type := StaticCSSCheckIdx L q_code m_max × Fin M
abbrev KPFinTimeSliceAdj (M : ℕ) (t₁ t₂ : Fin M) : Prop := t₁ = t₂ ∨ (t₁.val + 1) % M = t₂.val ∨ (t₂.val + 1) % M = t₁.val

abbrev KPSpacetimeCellAdj {L q_code m_max : ℕ} [NeZero L]
    (sys : IndexedCommutingProjectorHamiltonian 3 L (UniformSite3D L (CodeSlotConfig q_code)) (StaticCSSCheckIdx L q_code m_max))
    (C_rca : ℝ) (R_pert M : ℕ) (p₁ p₂ : KPSpacetimeGridCell L q_code m_max M) : Prop :=
  KPFinTimeSliceAdj M p₁.2 p₂.2 ∧ (p₁.1 = p₂.1 ∨ ∃ r ∈ Finset.Icc 1 (min R_pert L), ∃ A ∈ boxCubes 3 L r,
    p₁.1 ∈ kpRCACollarChecks sys C_rca r A ∧ p₂.1 ∈ kpRCACollarChecks sys C_rca r A)

lemma kpSpacetimeCellAdj_refl {L q_code m_max : ℕ} [NeZero L]
    (sys : IndexedCommutingProjectorHamiltonian 3 L (UniformSite3D L (CodeSlotConfig q_code)) (StaticCSSCheckIdx L q_code m_max))
    (C_rca : ℝ) (R_pert M : ℕ) (p : KPSpacetimeGridCell L q_code m_max M) :
    KPSpacetimeCellAdj sys C_rca R_pert M p p := ⟨Or.inl rfl, Or.inl rfl⟩

lemma kpSpacetimeCellAdj_symm {L q_code m_max : ℕ} [NeZero L]
    (sys : IndexedCommutingProjectorHamiltonian 3 L (UniformSite3D L (CodeSlotConfig q_code)) (StaticCSSCheckIdx L q_code m_max))
    (C_rca : ℝ) (R_pert M : ℕ) (p₁ p₂ : KPSpacetimeGridCell L q_code m_max M)
    (h : KPSpacetimeCellAdj sys C_rca R_pert M p₁ p₂) : KPSpacetimeCellAdj sys C_rca R_pert M p₂ p₁ := by
  refine ⟨?_, ?_⟩
  · rcases h.1 with h₀ | h₁ | h₂
    · exact Or.inl h₀.symm
    · exact Or.inr (Or.inr h₁)
    · exact Or.inr (Or.inl h₂)
  · rcases h.2 with h_eq | ⟨r, hr, A, hA, h₁, h₂⟩
    · exact Or.inl h_eq.symm
    · exact Or.inr ⟨r, hr, A, hA, h₂, h₁⟩

lemma card_filter_kpFinTimeSliceAdj_le (M : ℕ) (t₁ : Fin M) :
    (Finset.univ.filter (KPFinTimeSliceAdj M t₁)).card ≤ 3 := by
  have hM : 0 < M := t₁.pos
  let t_next : Fin M := ⟨(t₁.val + 1) % M, Nat.mod_lt _ hM⟩
  let t_prev : Fin M := ⟨(t₁.val + M - 1) % M, Nat.mod_lt _ hM⟩
  have h_sub : Finset.univ.filter (KPFinTimeSliceAdj M t₁) ⊆ {t₁, t_next, t_prev} := fun t₂ ht₂ => by
    rcases (Finset.mem_filter.mp ht₂).2 with rfl | h_next | h_prev
    · simp
    · simp only [Finset.mem_insert, Finset.mem_singleton]; right; left; exact Fin.ext h_next.symm
    · simp only [Finset.mem_insert, Finset.mem_singleton]; right; right; apply Fin.ext
      by_cases h_lt : t₂.val + 1 < M
      · rw [Nat.mod_eq_of_lt h_lt] at h_prev; have h_eq : t₁.val + M - 1 = t₂.val + M := by omega
        dsimp [t_prev]; rw [h_eq, Nat.add_mod_right, Nat.mod_eq_of_lt t₂.isLt]
      · have h_eq_M : t₂.val + 1 = M := by have := t₂.isLt; omega
        rw [h_eq_M, Nat.mod_self] at h_prev; have h_eq : t₁.val + M - 1 = t₂.val := by omega
        dsimp [t_prev]; rw [h_eq, Nat.mod_eq_of_lt t₂.isLt]
  exact le_trans (Finset.card_le_card h_sub) (le_trans (Finset.card_insert_le _ _)
    (Nat.add_le_add_right (le_trans (Finset.card_insert_le _ _) (by simp)) 1))

def kpStaticCSSCheckAnchor {L q_code m_max : ℕ} : StaticCSSCheckIdx L q_code m_max → Box3D L
  | Sum.inl (v, _) => v | Sum.inr (Sum.inl (v, _)) => v | Sum.inr (Sum.inr (v, _)) => v

lemma kpStaticCSSCheckAnchor_mem_support {L q_code r_0 m_max : ℕ}
    (D_field : Box3D L → LocalCSSDescriptor q_code r_0 m_max) (c : StaticCSSCheckIdx L q_code m_max) :
    kpStaticCSSCheckAnchor c ∈ staticCSSCheckSupport D_field c := by
  rcases c with ⟨v, _⟩ | ⟨v, _⟩ | ⟨v, _⟩
  · exact Finset.mem_singleton_self v
  · exact _root_.mem_boxBall_self v r_0
  · exact _root_.mem_boxBall_self v r_0

lemma card_filter_mem_kpRCACollarChecks_le
    {L q_code r_0 m_max w_0 R_pert : ℕ} [NeZero L] (D_field : Box3D L → LocalCSSDescriptor q_code r_0 m_max)
    (sys : IndexedCommutingProjectorHamiltonian 3 L (UniformSite3D L (CodeSlotConfig q_code)) (StaticCSSCheckIdx L q_code m_max))
    (h_sys_checks : ∀ idx, sys.checkProj idx = staticCSSCheckProj D_field idx ∧
      sys.support idx = staticCSSCheckSupport D_field idx ∧ sys.weight idx = 1)
    {C_rca : ℝ} (hC_rca : 0 ≤ C_rca) {r : ℕ} (hr : r ∈ Finset.Icc 1 (min R_pert L)) (c : StaticCSSCheckIdx L q_code m_max) :
    ((boxCubes 3 L r).filter (fun A => c ∈ kpRCACollarChecks sys C_rca r A)).card ≤
      (2 * (R_pert + 2 * linearExpansionRadius C_rca R_pert + r_0) + 1) ^ 3 * (w_0 + 1) := by
  have hr_R : r ≤ R_pert := le_trans (Finset.mem_Icc.mp hr).2 (Nat.min_le_left R_pert L)
  have h_sub : (boxCubes 3 L r).filter (fun A => c ∈ kpRCACollarChecks sys C_rca r A) ⊆
      (boxCubes 3 L r).filter (fun A => kpStaticCSSCheckAnchor c ∈ kpRCACollarCube C_rca r A) := by
    intro A hA; rw [Finset.mem_filter] at hA ⊢
    exact ⟨hA.1, (Finset.mem_filter.mp hA.2).2 ((h_sys_checks c).2.1 ▸ kpStaticCSSCheckAnchor_mem_support D_field c)⟩
  have h_c1 := le_trans (Finset.card_le_card h_sub)
    (card_filter_mem_enclosingBoxCube_le_pow r (linearExpansionRadius C_rca r) (kpStaticCSSCheckAnchor c))
  have h_rad : linearExpansionRadius C_rca r ≤ linearExpansionRadius C_rca R_pert :=
    Nat.ceil_mono (mul_le_mul_of_nonneg_left (Nat.cast_le.mpr hr_R) hC_rca)
  have h_base : 2 * linearExpansionRadius C_rca r ≤ 2 * (R_pert + 2 * linearExpansionRadius C_rca R_pert + r_0) + 1 := by omega
  exact le_trans h_c1 (le_trans (Nat.pow_le_pow_left h_base 3) (Nat.le_mul_of_pos_right _ (Nat.succ_pos w_0)))

lemma card_kpRCACollarChecks_le
    {L q_code r_0 m_max w_0 R_pert : ℕ} [NeZero L] (D_field : Box3D L → LocalCSSDescriptor q_code r_0 m_max)
    (sys : IndexedCommutingProjectorHamiltonian 3 L (UniformSite3D L (CodeSlotConfig q_code)) (StaticCSSCheckIdx L q_code m_max))
    (h_sys_checks : ∀ idx, sys.checkProj idx = staticCSSCheckProj D_field idx ∧
      sys.support idx = staticCSSCheckSupport D_field idx ∧ sys.weight idx = 1)
    (h_geom : sys.IsGeometricallyLocal r_0 w_0) {C_rca : ℝ} (hC_rca : 0 ≤ C_rca)
    {r : ℕ} (hr : r ∈ Finset.Icc 1 (min R_pert L)) (A : Finset (Box3D L)) :
    (kpRCACollarChecks sys C_rca r A).card ≤ kpCollarMaxCheckCard R_pert r_0 w_0 C_rca := by
  have hL_pos : 0 < L := NeZero.pos L
  have hr_R : r ≤ R_pert := le_trans (Finset.mem_Icc.mp hr).2 (Nat.min_le_left R_pert L)
  let R := linearExpansionRadius C_rca r; let B := kpRCACollarCube C_rca r A
  let xB : Box3D L := fun i => ⟨(anchorOfCube r A i).val - (R - r) / 2, Nat.sub_lt_of_lt (anchorOfCube r A i).isLt⟩
  have hB_eq : boxCube xB R = B := rfl
  let g : (Fin 3 → Fin R) → Box3D L := fun k i =>
    ⟨min (L - 1) ((xB i).val + (k i).val), Nat.lt_of_le_of_lt (Nat.min_le_left _ _) (Nat.sub_lt hL_pos zero_lt_one)⟩
  have hB_sub : B ⊆ Finset.univ.image g := fun y hy => by
    rw [← hB_eq, mem_boxCube] at hy
    have hk_lt : ∀ i : Fin 3, (y i).val - (xB i).val < R := fun i => by have := (hy i).1; have := (hy i).2; omega
    let k : Fin 3 → Fin R := fun i => ⟨(y i).val - (xB i).val, hk_lt i⟩
    have hy_eq : g k = y := by funext i; apply Fin.ext; have := (hy i).1; have := (y i).isLt; dsimp [g, k]; omega
    exact Finset.mem_image.mpr ⟨k, Finset.mem_univ k, hy_eq⟩
  have hB_card : B.card ≤ R ^ 3 := by
    calc B.card
      _ ≤ (Finset.univ : Finset (Fin 3 → Fin R)).card := le_trans (Finset.card_le_card hB_sub) Finset.card_image_le
      _ = R ^ 3 := by rw [Finset.card_univ, Fintype.card_fun, Fintype.card_fin, Fintype.card_fin]
  have h_col_sub : kpRCACollarChecks sys C_rca r A ⊆
      B.biUnion (fun y => Finset.univ.filter (fun c => y ∈ sys.support c)) := fun c hc => by
    have h_anc : kpStaticCSSCheckAnchor c ∈ sys.support c := (h_sys_checks c).2.1 ▸ kpStaticCSSCheckAnchor_mem_support D_field c
    exact Finset.mem_biUnion.mpr ⟨kpStaticCSSCheckAnchor c, (Finset.mem_filter.mp hc).2 h_anc, Finset.mem_filter.mpr ⟨Finset.mem_univ c, h_anc⟩⟩
  have h_card_col : (kpRCACollarChecks sys C_rca r A).card ≤ B.card * w_0 :=
    smul_eq_mul B.card w_0 ▸ le_trans (le_trans (Finset.card_le_card h_col_sub) Finset.card_biUnion_le)
      (Finset.sum_le_card_nsmul B _ w_0 (fun y _ => h_geom.2 y))
  have h_rad : R ≤ linearExpansionRadius C_rca R_pert := Nat.ceil_mono (mul_le_mul_of_nonneg_left (Nat.cast_le.mpr hr_R) hC_rca)
  have h_base : R ≤ 2 * (R_pert + 2 * linearExpansionRadius C_rca R_pert + r_0) + 1 := by omega
  unfold kpCollarMaxCheckCard
  exact le_trans h_card_col (le_trans (Nat.mul_le_mul (le_trans hB_card (Nat.pow_le_pow_left h_base 3)) (Nat.le_succ w_0)) (Nat.le_succ _))

def kpRCADiagNat (R_pert r_0 w_0 : ℕ) (C_rca : ℝ) : ℕ :=
  R_pert * ((2 * (R_pert + 2 * linearExpansionRadius C_rca R_pert + r_0) + 1) ^ 3 * (w_0 + 1))

lemma kpRCADiagNat_cast_eq (R_pert r_0 w_0 : ℕ) (C_rca : ℝ) :
    (kpRCADiagNat R_pert r_0 w_0 C_rca : ℝ) = rcaDiagonalCoercivityConstant 3 R_pert r_0 w_0 C_rca := by
  unfold kpRCADiagNat rcaDiagonalCoercivityConstant; push_cast; ring

lemma card_filter_kpSpacetimeCellAdj_le
    {L q_code r_0 m_max w_0 R_pert M : ℕ} [NeZero L] (D_field : Box3D L → LocalCSSDescriptor q_code r_0 m_max)
    (sys : IndexedCommutingProjectorHamiltonian 3 L (UniformSite3D L (CodeSlotConfig q_code)) (StaticCSSCheckIdx L q_code m_max))
    (h_sys_checks : ∀ idx, sys.checkProj idx = staticCSSCheckProj D_field idx ∧
      sys.support idx = staticCSSCheckSupport D_field idx ∧ sys.weight idx = 1)
    (h_geom : sys.IsGeometricallyLocal r_0 w_0) {C_rca : ℝ} (hC_rca : 0 ≤ C_rca)
    (p₁ : KPSpacetimeGridCell L q_code m_max M) :
    (Finset.univ.filter (KPSpacetimeCellAdj sys C_rca R_pert M p₁)).card ≤
      4 * (kpRCADiagNat R_pert r_0 w_0 C_rca + 1) * (kpCollarMaxCheckCard R_pert r_0 w_0 C_rca + 1) := by
  let K_geom := (2 * (R_pert + 2 * linearExpansionRadius C_rca R_pert + r_0) + 1) ^ 3 * (w_0 + 1)
  let Δ_nat := kpRCADiagNat R_pert r_0 w_0 C_rca; let Δ_V := kpCollarMaxCheckCard R_pert r_0 w_0 C_rca
  let S_check : Finset (StaticCSSCheckIdx L q_code m_max) :=
    insert p₁.1 ((Finset.Icc 1 (min R_pert L)).biUnion (fun r =>
      ((boxCubes 3 L r).filter (fun A => p₁.1 ∈ kpRCACollarChecks sys C_rca r A)).biUnion
        (fun A => kpRCACollarChecks sys C_rca r A)))
  let S_time : Finset (Fin M) := Finset.univ.filter (KPFinTimeSliceAdj M p₁.2)
  have h_sub : Finset.univ.filter (KPSpacetimeCellAdj sys C_rca R_pert M p₁) ⊆ S_check ×ˢ S_time := by
    intro p₂ hp₂; rcases (Finset.mem_filter.mp hp₂).2 with ⟨ht, hc⟩
    refine Finset.mem_product.mpr ⟨?_, Finset.mem_filter.mpr ⟨Finset.mem_univ p₂.2, ht⟩⟩
    rcases hc with h_eq | ⟨r, hr, A, hA, h₁, h₂⟩
    · exact Finset.mem_insert.mpr (Or.inl h_eq.symm)
    · exact Finset.mem_insert.mpr (Or.inr (Finset.mem_biUnion.mpr ⟨r, hr,
        Finset.mem_biUnion.mpr ⟨A, Finset.mem_filter.mpr ⟨hA, h₁⟩, h₂⟩⟩))
  have h_r_card : ∀ r ∈ Finset.Icc 1 (min R_pert L),
      (((boxCubes 3 L r).filter (fun A => p₁.1 ∈ kpRCACollarChecks sys C_rca r A)).biUnion
        (fun A => kpRCACollarChecks sys C_rca r A)).card ≤ K_geom * Δ_V := fun r hr => by
    refine le_trans Finset.card_biUnion_le (le_trans (Finset.sum_le_card_nsmul _ _ Δ_V fun A _ =>
      card_kpRCACollarChecks_le D_field sys h_sys_checks h_geom hC_rca hr A) ?_)
    simpa using Nat.mul_le_mul_right Δ_V (card_filter_mem_kpRCACollarChecks_le D_field sys h_sys_checks hC_rca hr p₁.1)
  have h_biUnion_r :
      ((Finset.Icc 1 (min R_pert L)).biUnion (fun r =>
        ((boxCubes 3 L r).filter (fun A => p₁.1 ∈ kpRCACollarChecks sys C_rca r A)).biUnion
          (fun A => kpRCACollarChecks sys C_rca r A))).card ≤ Δ_nat * Δ_V := by
    have h_Icc : (Finset.Icc 1 (min R_pert L)).card ≤ R_pert := by rw [Nat.card_Icc]; have := Nat.min_le_left R_pert L; omega
    refine le_trans Finset.card_biUnion_le (le_trans (Finset.sum_le_card_nsmul _ _ (K_geom * Δ_V) h_r_card) ?_)
    have h2 : (Finset.Icc 1 (min R_pert L)).card • (K_geom * Δ_V) ≤ R_pert * (K_geom * Δ_V) := by
      simpa using Nat.mul_le_mul_right (K_geom * Δ_V) h_Icc
    exact (show R_pert * (K_geom * Δ_V) = Δ_nat * Δ_V by dsimp [Δ_nat, kpRCADiagNat, K_geom]; ring) ▸ h2
  have h_check_card : S_check.card ≤ (Δ_nat + 1) * (Δ_V + 1) := by
    have : S_check.card ≤ Δ_nat * Δ_V + 1 :=
      le_trans (Finset.card_insert_le p₁.1 _) (Nat.add_le_add_right h_biUnion_r 1)
    nlinarith
  have h_time_card : S_time.card ≤ 4 := le_trans (card_filter_kpFinTimeSliceAdj_le M p₁.2) (by omega)
  calc (Finset.univ.filter (KPSpacetimeCellAdj sys C_rca R_pert M p₁)).card
    _ ≤ ((Δ_nat + 1) * (Δ_V + 1)) * 4 := le_trans (Finset.card_product S_check S_time ▸ Finset.card_le_card h_sub)
        (Nat.mul_le_mul h_check_card h_time_card)
    _ = 4 * (Δ_nat + 1) * (Δ_V + 1) := by ring

lemma sum_Icc_pow_le_two_mul {r : ℝ} (hr_nn : 0 ≤ r) (hr_half : r ≤ 1 / 2) (N : ℕ) :
    (∑ m ∈ Finset.Icc 1 N, r ^ m) ≤ 2 * r := by
  suffices h : (∑ m ∈ Finset.Icc 1 N, r ^ m) + 2 * r ^ (N + 1) ≤ 2 * r by
    have : 0 ≤ 2 * r ^ (N + 1) := by positivity
    linarith
  induction N with
  | zero => simp [pow_one]
  | succ N ih =>
      have h_ins : Finset.Icc 1 (N + 1) = insert (N + 1) (Finset.Icc 1 N) := by
        ext x; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
      rw [h_ins, Finset.sum_insert (by simp)]
      have h_pow : r ^ (N + 2) = r * r ^ (N + 1) := by ring
      have h_nn : 0 ≤ r ^ (N + 1) := pow_nonneg hr_nn (N + 1)
      nlinarith

/-! ## 2. Kotecký–Preiss Arborescence Resummation -/

lemma piFinset_split_sum {p : ℕ} {α : Type*} [DecidableEq α]
    (A B : Finset (Fin p)) (h_disj : Disjoint A B)
    (T_A T_B : Fin p → Finset α) (K_0 : Fin p → α) (F : (Fin p → α) → ℝ) :
    let PiAB := Fintype.piFinset (fun v => if v ∈ A then T_A v else if v ∈ B then T_B v else {K_0 v})
    let PiA := Fintype.piFinset (fun v => if v ∈ A then T_A v else {K_0 v})
    let PiB (K_A : Fin p → α) := Fintype.piFinset (fun v => if v ∈ B then T_B v else {K_A v})
    (∑ K ∈ PiAB, F K) = ∑ K_A ∈ PiA, ∑ K ∈ PiB K_A, F K := by
  intro PiAB PiA PiB
  have h_eq : PiAB = PiA.biUnion PiB := by
    ext K; simp only [PiAB, PiA, PiB, Finset.mem_biUnion, Fintype.mem_piFinset]
    constructor
    · intro hK
      refine ⟨fun v => if v ∈ A then K v else K_0 v, fun v => ?_, fun v => ?_⟩
      · by_cases hvA : v ∈ A
        · simp only [hvA, if_true]; have h := hK v; rwa [if_pos hvA] at h
        · simp [hvA]
      · by_cases hvB : v ∈ B
        · have hvA : v ∉ A := Finset.disjoint_right.mp h_disj hvB
          have h := hK v; rw [if_neg hvA, if_pos hvB] at h; simpa [hvB] using h
        · simp only [hvB, if_false, Finset.mem_singleton]
          by_cases hvA : v ∈ A
          · simp [hvA]
          · have h := hK v; rw [if_neg hvA, if_neg hvB, Finset.mem_singleton] at h; simp [hvA, h]
    · rintro ⟨K_A, hK_A, hK_B⟩ v
      by_cases hvA : v ∈ A
      · have hvB : v ∉ B := Finset.disjoint_left.mp h_disj hvA
        have hB := hK_B v; rw [if_neg hvB, Finset.mem_singleton] at hB
        have hA := hK_A v; rw [if_pos hvA] at hA; simpa [hvA, hB] using hA
      · by_cases hvB : v ∈ B
        · have hB := hK_B v; rw [if_pos hvB] at hB; simpa [hvA, hvB] using hB
        · have hB := hK_B v; rw [if_neg hvB, Finset.mem_singleton] at hB
          have hA := hK_A v; rw [if_neg hvA] at hA; simpa [hvA, hvB, hB] using hA
  rw [h_eq, Finset.sum_biUnion]
  intro K₁ hK₁ K₂ hK₂ h_ne
  change Disjoint (PiB K₁) (PiB K₂)
  rw [Finset.disjoint_left]
  intro K h₁ h₂
  apply h_ne; funext v
  rw [Finset.mem_coe, Fintype.mem_piFinset] at hK₁ hK₂
  rw [Fintype.mem_piFinset] at h₁ h₂
  by_cases hvA : v ∈ A
  · have hvB : v ∉ B := Finset.disjoint_left.mp h_disj hvA
    have h₁v := h₁ v; rw [if_neg hvB, Finset.mem_singleton] at h₁v
    have h₂v := h₂ v; rw [if_neg hvB, Finset.mem_singleton] at h₂v
    exact h₁v.symm.trans h₂v
  · have h₁v := hK₁ v; rw [if_neg hvA, Finset.mem_singleton] at h₁v
    have h₂v := hK₂ v; rw [if_neg hvA, Finset.mem_singleton] at h₂v
    exact h₁v.trans h₂v.symm

private lemma piFinset_sum_prod_eq_pow {p : ℕ} {α : Type*} [DecidableEq α]
    (C : Finset (Fin p)) (T : Finset α) (K_0 : Fin p → α) (φ : α → ℝ) :
    (∑ K ∈ Fintype.piFinset (fun v => if v ∈ C then T else {K_0 v}), ∏ v ∈ C, φ (K v)) =
      (∑ γ ∈ T, φ γ) ^ C.card := by
  induction C using Finset.induction_on generalizing K_0 with
  | empty =>
      have h_eq : Fintype.piFinset (fun v : Fin p => if v ∈ (∅ : Finset (Fin p)) then T else {K_0 v}) = {K_0} := by
        ext K; simp [funext_iff]
      rw [h_eq]; simp
  | @insert a C' ha ih =>
      have h_disj : Disjoint ({a} : Finset (Fin p)) C' := Finset.disjoint_singleton_left.mpr ha
      have h_ite : (fun v => if v ∈ insert a C' then T else {K_0 v}) =
          (fun v => if v ∈ ({a} : Finset (Fin p)) then T else if v ∈ C' then T else {K_0 v}) := by
        funext v; by_cases hva : v = a <;> [subst hva; skip] <;> simp [*]
      rw [h_ite, piFinset_split_sum {a} C' h_disj (fun _ => T) (fun _ => T) K_0]
      have h_prod : ∀ K_A ∈ Fintype.piFinset (fun v => if v ∈ ({a} : Finset (Fin p)) then T else {K_0 v}),
          (∑ K ∈ Fintype.piFinset (fun v => if v ∈ C' then T else {K_A v}), ∏ v ∈ insert a C', φ (K v)) =
            φ (K_A a) * (∑ γ ∈ T, φ γ) ^ C'.card := by
        intro K_A _
        have h_congr : ∀ K ∈ Fintype.piFinset (fun v => if v ∈ C' then T else {K_A v}),
            (∏ v ∈ insert a C', φ (K v)) = φ (K_A a) * ∏ v ∈ C', φ (K v) := by
          intro K hK; rw [Finset.prod_insert ha]
          have hKa := (Fintype.mem_piFinset.mp hK) a
          rw [if_neg ha, Finset.mem_singleton] at hKa; rw [hKa]
        rw [Finset.sum_congr rfl h_congr, ← Finset.mul_sum, ih K_A]
      rw [Finset.sum_congr rfl h_prod, ← Finset.sum_mul]
      have h_bij : (∑ K_A ∈ Fintype.piFinset (fun v => if v ∈ ({a} : Finset (Fin p)) then T else {K_0 v}), φ (K_A a)) =
          ∑ γ ∈ T, φ γ := by
        refine Finset.sum_bij (fun K_A _ => K_A a) (fun K_A hK_A => by simpa using (Fintype.mem_piFinset.mp hK_A) a) ?_ ?_ (fun _ _ => rfl)
        · intro K₁ hK₁ K₂ hK₂ h_eq; funext v
          rcases eq_or_ne v a with rfl | hva
          · exact h_eq
          · have h₁ := (Fintype.mem_piFinset.mp hK₁) v
            have h₂ := (Fintype.mem_piFinset.mp hK₂) v
            simp only [Finset.mem_singleton, hva, if_false] at h₁ h₂
            exact h₁.trans h₂.symm
        · intro γ hγ
          refine ⟨Function.update K_0 a γ, Fintype.mem_piFinset.mpr fun v => ?_, Function.update_self a γ K_0⟩
          rcases eq_or_ne v a with rfl | hva <;> simp [hγ, *]
      rw [h_bij, Finset.card_insert_of_notMem ha, pow_succ']

private def restrictForest {p : ℕ} (C : Finset (Fin p)) (f : Fin p → Fin p) : Fin p → Fin p :=
  fun v => if v ∈ C then v else f v

private lemma iterate_eq_self_of_fix {α : Type*} {f : α → α} {x : α} (hx : f x = x) :
    ∀ n : ℕ, f^[n] x = x
  | 0 => rfl
  | n + 1 => by rw [Function.iterate_succ_apply, hx, iterate_eq_self_of_fix hx n]

private lemma restrictForest_mem_arborescenceForests {p : ℕ}
    {S R C : Finset (Fin p)} {r₀ : Fin p}
    (hR : R ⊆ S) (hr₀ : r₀ ∈ R) (hC : C ⊆ S \ R)
    {f : Fin p → Fin p} (hf : f ∈ arborescenceForests S R)
    (hC_eq : (S \ R).filter (fun u => f u = r₀) = C) :
    restrictForest C f ∈ arborescenceForests (S.erase r₀) (R.erase r₀ ∪ C) := by
  rcases Finset.mem_filter.mp hf with ⟨_, hf_fix, hf_in⟩
  let S' := S.erase r₀
  let R' := R.erase r₀ ∪ C
  have h_sdiff : S' \ R' = (S \ R) \ C := by
    ext v; simp only [S', R', Finset.mem_sdiff, Finset.mem_erase, Finset.mem_union]
    constructor
    · rintro ⟨⟨hv_ne, hv_S⟩, h_not⟩
      exact ⟨⟨hv_S, fun hv_R => h_not (Or.inl ⟨hv_ne, hv_R⟩)⟩, fun hv_C => h_not (Or.inr hv_C)⟩
    · rintro ⟨⟨hv_S, hv_not_R⟩, hv_not_C⟩
      exact ⟨⟨fun h_eq => hv_not_R (h_eq ▸ hr₀), hv_S⟩, fun h_or => h_or.elim (fun h => hv_not_R h.2) hv_not_C⟩
  have h_fix' : ∀ v, v ∉ S' \ R' → restrictForest C f v = v := by
    intro v hv; rw [h_sdiff, Finset.mem_sdiff] at hv
    by_cases hvC : v ∈ C
    · simp [restrictForest, hvC]
    · simp [restrictForest, hvC, hf_fix v (fun hSR => hv ⟨hSR, hvC⟩)]
  have h_step' : ∀ v ∈ S' \ R', restrictForest C f v ∈ S' := by
    intro v hv; rw [h_sdiff, Finset.mem_sdiff] at hv
    rcases hv with ⟨hv_SR, hv_not_C⟩
    have hf_ne : f v ≠ r₀ := fun h_eq => hv_not_C (hC_eq ▸ Finset.mem_filter.mpr ⟨hv_SR, h_eq⟩)
    simp [restrictForest, hv_not_C, S', Finset.mem_erase, hf_ne, (hf_in v hv_SR).1]
  have h_iter : ∀ (n : ℕ), ∀ w ∈ S', f^[n] w ∈ R ∪ C → (restrictForest C f)^[n] w ∈ R' := by
    intro n; induction n with
    | zero =>
        intro w hwS' hwRC
        rcases Finset.mem_union.mp hwRC with hwR | hwC
        · exact Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨(Finset.mem_erase.mp hwS').1, hwR⟩)
        · exact Finset.mem_union_right _ hwC
    | succ n ih =>
        intro w hwS' hwRC
        by_cases hwR' : w ∈ R'
        · rw [iterate_eq_self_of_fix (h_fix' w (fun h => (Finset.mem_sdiff.mp h).2 hwR')) (n + 1)]
          exact hwR'
        · have hw_sdiff : w ∈ S' \ R' := Finset.mem_sdiff.mpr ⟨hwS', hwR'⟩
          have hw_not_C : w ∉ C := fun hC_w => hwR' (Finset.mem_union_right _ hC_w)
          have h_rf_eq : restrictForest C f w = f w := if_neg hw_not_C
          have hfw_S' : f w ∈ S' := h_rf_eq ▸ h_step' w hw_sdiff
          rw [Function.iterate_succ_apply, h_rf_eq]
          rw [Function.iterate_succ_apply] at hwRC
          exact ih (f w) hfw_S' hwRC
  refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, h_fix', fun v hv => ⟨h_step' v hv, ?_⟩⟩
  have hv_SR : v ∈ S \ R := (Finset.mem_sdiff.mp (h_sdiff ▸ hv)).1
  exact h_iter p v (Finset.mem_sdiff.mp hv).1 (Finset.mem_union_left _ (hf_in v hv_SR).2)

private lemma restrictForest_injOn {p : ℕ} {S R C : Finset (Fin p)} {r₀ : Fin p} :
    Set.InjOn (restrictForest C)
      ((arborescenceForests S R).filter (fun f => (S \ R).filter (fun u => f u = r₀) = C)) := by
  intro f₁ hf₁ f₂ hf₂ h_eq
  have hC₁ := (Finset.mem_filter.mp hf₁).2
  have hC₂ := (Finset.mem_filter.mp hf₂).2
  funext v
  by_cases hvC : v ∈ C
  · have hv₁ : v ∈ (S \ R).filter (fun u => f₁ u = r₀) := hC₁.symm ▸ hvC
    have hv₂ : v ∈ (S \ R).filter (fun u => f₂ u = r₀) := hC₂.symm ▸ hvC
    exact (Finset.mem_filter.mp hv₁).2.trans (Finset.mem_filter.mp hv₂).2.symm
  · simpa [restrictForest, hvC] using congrFun h_eq v

def forestPolymerSum {p : ℕ} {α : Type*} [DecidableEq α]
    (P₀ : Finset α) (incompat : α → α → Prop) [DecidableRel incompat] (w : α → ℝ)
    (S R : Finset (Fin p)) (K_R : Fin p → α) : ℝ :=
  ∑ f ∈ arborescenceForests S R,
    ∑ K ∈ (Fintype.piFinset (fun v : Fin p => if v ∈ S \ R then P₀ else {K_R v})).filter
        (fun K => ∀ v ∈ S \ R, incompat (K (f v)) (K v)),
      ∏ v ∈ S \ R, w (K v)

private lemma list_map_ofFn_prod {m : ℕ} {α : Type*} (t : Fin m → α) (f : α → ℝ) :
    ((List.ofFn t).map f).prod = ∏ i : Fin m, f (t i) := by
  have h_eq : (List.ofFn t).map f = List.ofFn (fun i => f (t i)) :=
    List.ext_get (by simp) (by simp)
  rw [h_eq, List.prod_ofFn]

private lemma exists_piFinset_of_nodup {p : ℕ} {α : Type*} [DecidableEq α]
    (L : List (Fin p)) (hL : L.Nodup) (T : Finset α) (K_0 : Fin p → α)
    (t : Fin L.length → α) (ht : ∀ i, t i ∈ T) :
    ∃ K ∈ Fintype.piFinset (fun v => if v ∈ L.toFinset then T else {K_0 v}),
      (fun i : Fin L.length => K (L.get i)) = t := by
  induction L with
  | nil =>
      refine ⟨K_0, Fintype.mem_piFinset.mpr (by simp), ?_⟩
      funext i; exact Fin.elim0 i
  | cons a L' ih =>
      rcases List.nodup_cons.mp hL with ⟨ha_not, hL'_nodup⟩
      rcases ih hL'_nodup (fun i => t i.succ) (fun i => ht i.succ) with ⟨K', hK', hK'_eq⟩
      let i₀ : Fin (a :: L').length := ⟨0, Nat.succ_pos _⟩
      refine ⟨Function.update K' a (t i₀), Fintype.mem_piFinset.mpr fun v => ?_, ?_⟩
      · rcases eq_or_ne v a with rfl | hva
        · simp only [Function.update_self, List.toFinset_cons, Finset.mem_insert, true_or, if_true]
          exact ht i₀
        · have h' := Fintype.mem_piFinset.mp hK' v
          simpa [Function.update_of_ne hva, List.mem_toFinset, hva] using h'
      · funext ⟨i, hi⟩; cases i with
        | zero =>
            change Function.update K' a (t i₀) a = t i₀
            exact Function.update_self a (t i₀) K'
        | succ j =>
            let idx' : Fin L'.length := ⟨j, Nat.lt_of_succ_lt_succ hi⟩
            have hj_ne : L'.get idx' ≠ a :=
              fun h_eq => ha_not (h_eq ▸ List.get_mem L' idx')
            change Function.update K' a (t i₀) (L'.get idx') = t idx'.succ
            rw [Function.update_of_ne hj_ne]
            exact congrFun hK'_eq idx'

private lemma piFinset_toList_sum_eq {p : ℕ} {α : Type*} [DecidableEq α]
    (L : List (Fin p)) (hL : L.Nodup) (T : Finset α) (K_0 : Fin p → α)
    (G : List α → ℝ) :
    (∑ K ∈ Fintype.piFinset (fun v => if v ∈ L.toFinset then T else {K_0 v}),
      G (L.map K)) =
    ∑ t ∈ Fintype.piFinset (fun _ : Fin L.length => T),
      G (List.ofFn t) := by
  refine Finset.sum_bij (fun K _ => fun i : Fin L.length => K (L.get i)) ?_ ?_ ?_ ?_
  · intro K hK; rw [Fintype.mem_piFinset] at hK ⊢
    intro i; have h := hK (L.get i)
    rwa [if_pos (List.mem_toFinset.mpr (List.get_mem L i))] at h
  · intro K₁ hK₁ K₂ hK₂ h_eq; funext v
    rw [Fintype.mem_piFinset] at hK₁ hK₂
    by_cases hv : v ∈ L.toFinset
    · rcases List.mem_iff_get.mp (List.mem_toFinset.mp hv) with ⟨i, rfl⟩
      exact congrFun h_eq i
    · have h₁ := hK₁ v; rw [if_neg hv, Finset.mem_singleton] at h₁
      have h₂ := hK₂ v; rw [if_neg hv, Finset.mem_singleton] at h₂
      exact h₁.trans h₂.symm
  · intro t ht
    rcases exists_piFinset_of_nodup L hL T K_0 t (Fintype.mem_piFinset.mp ht) with ⟨K, hK, h_eq⟩
    exact ⟨K, hK, h_eq⟩
  · intro K _
    have h_map : List.ofFn (fun i : Fin L.length => K (L.get i)) = L.map K :=
      List.ext_get (by simp) (by simp)
    rw [h_map]

def kpForestWeight {α : Type*} [DecidableEq α]
    (P₀ : Finset α) (incompat : α → α → Prop) [DecidableRel incompat] (w : α → ℝ) :
    ℕ → List α → ℝ
  | 0, _ => 1
  | _ + 1, [] => 0
  | s + 1, γ₀ :: Γ =>
      let n := s - Γ.length
      ∑ m ∈ Finset.range (n + 1), ((m.factorial : ℝ)⁻¹) *
        ∑ t ∈ Fintype.piFinset (fun _ : Fin m => P₀.filter (incompat γ₀)),
          (∏ i : Fin m, w (t i)) * kpForestWeight P₀ incompat w s (List.ofFn t ++ Γ)

lemma kpForestWeight_nonneg {α : Type*} [DecidableEq α]
    (P₀ : Finset α) (incompat : α → α → Prop) [DecidableRel incompat]
    {w : α → ℝ} (hw : ∀ γ ∈ P₀, 0 ≤ w γ) :
    ∀ (s : ℕ) (Γ : List α), 0 ≤ kpForestWeight P₀ incompat w s Γ
  | 0, _ => zero_le_one
  | _ + 1, [] => le_refl 0
  | s + 1, γ₀ :: Γ => by
      dsimp [kpForestWeight]
      refine Finset.sum_nonneg fun m _ => mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg _)) ?_
      refine Finset.sum_nonneg fun t ht => mul_nonneg (Finset.prod_nonneg fun i _ => ?_)
        (kpForestWeight_nonneg P₀ incompat hw s _)
      exact hw (t i) (Finset.mem_filter.mp (Fintype.mem_piFinset.mp ht i)).1

lemma forestPolymerSum_le_kpForestWeight {p : ℕ} {α : Type*} [DecidableEq α]
    (P₀ : Finset α) (incompat : α → α → Prop) [DecidableRel incompat]
    {w : α → ℝ} (hw : ∀ γ ∈ P₀, 0 ≤ w γ) :
    ∀ (s : ℕ) (S : Finset (Fin p)) (roots : List (Fin p)),
      S.card = s → roots.Nodup → roots.toFinset ⊆ S →
      ∀ K_R : Fin p → α,
        forestPolymerSum P₀ incompat w S roots.toFinset K_R ≤
          (((S \ roots.toFinset).card.factorial : ℝ)) *
            kpForestWeight P₀ incompat w s (roots.map K_R) := by
  intro s; induction s with
  | zero =>
      intro S roots hS _ hR_sub K_R
      have hS_emp : S = ∅ := Finset.card_eq_zero.mp hS
      have hR_emp : roots.toFinset = ∅ := Finset.subset_empty.mp (hS_emp ▸ hR_sub)
      rw [hS_emp, hR_emp]
      simp only [Finset.sdiff_self, Finset.card_empty, Nat.factorial_zero, Nat.cast_one,
        kpForestWeight, mul_one, forestPolymerSum]
      have h_arb_sub : arborescenceForests (∅ : Finset (Fin p)) ∅ ⊆ {id} := by
        intro f hf; rw [Finset.mem_singleton]; funext v
        exact (Finset.mem_filter.mp hf).2.1 v (by simp)
      have h_pi_sub : ∀ f : Fin p → Fin p,
          (Fintype.piFinset (fun v : Fin p => if v ∈ (∅ \ ∅ : Finset (Fin p)) then P₀ else {K_R v})).filter
            (fun K => ∀ v ∈ (∅ \ ∅ : Finset (Fin p)), incompat (K (f v)) (K v)) ⊆ {K_R} := by
        intro f K hK; rw [Finset.mem_singleton]; funext v
        have hv := (Fintype.mem_piFinset.mp (Finset.mem_filter.mp hK).1) v
        simpa using hv
      calc ∑ f ∈ arborescenceForests (∅ : Finset (Fin p)) ∅,
            ∑ K ∈ (Fintype.piFinset (fun v : Fin p => if v ∈ (∅ \ ∅ : Finset (Fin p)) then P₀ else {K_R v})).filter
              (fun K => ∀ v ∈ (∅ \ ∅ : Finset (Fin p)), incompat (K (f v)) (K v)),
              ∏ v ∈ (∅ \ ∅ : Finset (Fin p)), w (K v)
        _ ≤ ∑ f ∈ ({id} : Finset (Fin p → Fin p)),
            ∑ K ∈ (Fintype.piFinset (fun v : Fin p => if v ∈ (∅ \ ∅ : Finset (Fin p)) then P₀ else {K_R v})).filter
              (fun K => ∀ v ∈ (∅ \ ∅ : Finset (Fin p)), incompat (K (f v)) (K v)), (1 : ℝ) := by
            simp only [Finset.sdiff_self, Finset.prod_empty]
            exact Finset.sum_le_sum_of_subset_of_nonneg h_arb_sub
              (fun _ _ _ => Finset.sum_nonneg (fun _ _ => zero_le_one))
        _ ≤ ∑ _f ∈ ({id} : Finset (Fin p → Fin p)), ∑ _K ∈ ({K_R} : Finset (Fin p → α)), (1 : ℝ) := by
            refine Finset.sum_le_sum fun f _ => ?_
            exact Finset.sum_le_sum_of_subset_of_nonneg (h_pi_sub f) (fun _ _ _ => zero_le_one)
        _ = 1 := by simp
  | succ s ih =>
      intro S roots hS h_nodup hR_sub K_R
      cases roots with
      | nil =>
          simp only [List.toFinset_nil, List.map_nil, kpForestWeight, mul_zero, forestPolymerSum]
          have hS_ne : S.Nonempty := Finset.card_pos.mp (by omega)
          rcases hS_ne with ⟨v₀, hv₀⟩
          have h_arb_emp : arborescenceForests S ∅ = ∅ := by
            rw [Finset.eq_empty_iff_forall_notMem]
            intro f hf
            have hv₀_SR : v₀ ∈ S \ ∅ := Finset.mem_sdiff.mpr ⟨hv₀, Finset.notMem_empty v₀⟩
            exact Finset.notMem_empty _ ((Finset.mem_filter.mp hf).2.2 v₀ hv₀_SR).2
          rw [h_arb_emp, Finset.sum_empty]
      | cons r₀ roots' =>
          let R := (r₀ :: roots').toFinset
          rcases List.nodup_cons.mp h_nodup with ⟨hr₀_not_mem, hroots'_nodup⟩
          have hr₀_R : r₀ ∈ R := List.mem_toFinset.mpr List.mem_cons_self
          have hr₀_S : r₀ ∈ S := hR_sub hr₀_R
          have hR_erase : R.erase r₀ = roots'.toFinset := by
            ext v; simp only [R, List.toFinset_cons, Finset.mem_erase, Finset.mem_insert, List.mem_toFinset]
            exact ⟨fun ⟨hne, h_or⟩ => h_or.resolve_left hne,
              fun hv => ⟨fun h_eq => hr₀_not_mem (h_eq ▸ hv), Or.inr hv⟩⟩
          let S' := S.erase r₀
          have hS'_card : S'.card = s := by
            have h1 : S'.card = S.card - 1 := Finset.card_erase_of_mem hr₀_S
            omega
          have hR_card : R.card = roots'.length + 1 := by
            change (r₀ :: roots').toFinset.card = roots'.length + 1
            rw [List.toFinset_card_of_nodup h_nodup, List.length_cons]
          have h_SR_card : (S \ R).card = s - roots'.length := by
            have h1 : (S \ R).card + R.card = S.card := Finset.card_sdiff_add_card_eq_card hR_sub
            omega
          have h_part : arborescenceForests S R =
              (S \ R).powerset.biUnion (fun C =>
                (arborescenceForests S R).filter (fun f => (S \ R).filter (fun u => f u = r₀) = C)) := by
            ext f; simp only [Finset.mem_biUnion, Finset.mem_powerset, Finset.mem_filter]
            exact ⟨fun hf => ⟨_, Finset.filter_subset _ _, hf, rfl⟩, fun ⟨_, _, hf, _⟩ => hf⟩
          have h_part_disj : Set.PairwiseDisjoint ↑(S \ R).powerset
              (fun C => (arborescenceForests S R).filter (fun f => (S \ R).filter (fun u => f u = r₀) = C)) := by
            intro C₁ _ C₂ _ h_ne
            change Disjoint _ _
            rw [Finset.disjoint_left]
            intro f hf₁ hf₂
            exact h_ne ((Finset.mem_filter.mp hf₁).2.symm.trans (Finset.mem_filter.mp hf₂).2)
          have h_C_bound : ∀ C ∈ (S \ R).powerset,
              (∑ f ∈ (arborescenceForests S R).filter (fun f => (S \ R).filter (fun u => f u = r₀) = C),
                ∑ K ∈ (Fintype.piFinset (fun v : Fin p => if v ∈ S \ R then P₀ else {K_R v})).filter
                    (fun K => ∀ v ∈ S \ R, incompat (K (f v)) (K v)),
                  ∏ v ∈ S \ R, w (K v)) ≤
              (((S \ R).card - C.card).factorial : ℝ) *
                ∑ t ∈ Fintype.piFinset (fun _ : Fin C.card => P₀.filter (incompat (K_R r₀))),
                  (∏ i : Fin C.card, w (t i)) *
                    kpForestWeight P₀ incompat w s (List.ofFn t ++ roots'.map K_R) := by
            intro C hC_pow
            have hC : C ⊆ S \ R := Finset.mem_powerset.mp hC_pow
            let R' := R.erase r₀ ∪ C
            have h_sdiff : S' \ R' = (S \ R) \ C := by
              ext v; simp only [S', R', Finset.mem_sdiff, Finset.mem_erase, Finset.mem_union]
              constructor
              · rintro ⟨⟨hv_ne, hv_S⟩, h_not⟩
                exact ⟨⟨hv_S, fun hv_R => h_not (Or.inl ⟨hv_ne, hv_R⟩)⟩, fun hv_C => h_not (Or.inr hv_C)⟩
              · rintro ⟨⟨hv_S, hv_not_R⟩, hv_not_C⟩
                exact ⟨⟨fun h_eq => hv_not_R (h_eq ▸ hr₀_R), hv_S⟩,
                  fun h_or => h_or.elim (fun h => hv_not_R h.2) hv_not_C⟩
            have h_disj_C : Disjoint C (S' \ R') := by
              rw [h_sdiff]; exact disjoint_sdiff_self_right
            have h_union_C : C ∪ (S' \ R') = S \ R := by
              rw [h_sdiff, Finset.union_sdiff_of_subset hC]
            let T₀ := P₀.filter (incompat (K_R r₀))
            let PiC := Fintype.piFinset (fun v : Fin p => if v ∈ C then T₀ else {K_R v})
            let innerTerm (K_C : Fin p → α) (f' : Fin p → Fin p) : ℝ :=
              ∑ K ∈ (Fintype.piFinset (fun v : Fin p => if v ∈ S' \ R' then P₀ else {K_C v})).filter
                  (fun K => ∀ v ∈ S' \ R', incompat (K (f' v)) (K v)),
                ∏ v ∈ S' \ R', w (K v)
            have h_f_eq : ∀ f ∈ (arborescenceForests S R).filter (fun f => (S \ R).filter (fun u => f u = r₀) = C),
                (∑ K ∈ (Fintype.piFinset (fun v : Fin p => if v ∈ S \ R then P₀ else {K_R v})).filter
                    (fun K => ∀ v ∈ S \ R, incompat (K (f v)) (K v)),
                  ∏ v ∈ S \ R, w (K v)) =
                ∑ K_C ∈ PiC, (∏ u ∈ C, w (K_C u)) * innerTerm K_C (restrictForest C f) := by
              intro f hf
              have hC_eq : (S \ R).filter (fun u => f u = r₀) = C := (Finset.mem_filter.mp hf).2
              let Pi_C_SR := Fintype.piFinset (fun v : Fin p =>
                if v ∈ C then T₀ else if v ∈ S' \ R' then P₀ else {K_R v})
              have h_dom_eq : (Fintype.piFinset (fun v : Fin p => if v ∈ S \ R then P₀ else {K_R v})).filter
                  (fun K => ∀ v ∈ S \ R, incompat (K (f v)) (K v)) =
                  Pi_C_SR.filter (fun K => ∀ v ∈ S' \ R', incompat (K (restrictForest C f v)) (K v)) := by
                ext K
                simp only [Pi_C_SR, T₀, Finset.mem_filter, Fintype.mem_piFinset]
                have hr₀_not_SR : r₀ ∉ S \ R := fun h => (Finset.mem_sdiff.mp h).2 hr₀_R
                have hr₀_not_C : r₀ ∉ C := fun h => hr₀_not_SR (hC h)
                have hr₀_not_S'R' : r₀ ∉ S' \ R' := by
                  rw [h_sdiff]; exact fun h => hr₀_not_SR (Finset.mem_sdiff.mp h).1
                constructor
                · rintro ⟨hK_pi, hK_inc⟩
                  have hKr₀ : K r₀ = K_R r₀ := by
                    have h := hK_pi r₀; rwa [if_neg hr₀_not_SR, Finset.mem_singleton] at h
                  refine ⟨fun v => ?_, fun v hv => ?_⟩
                  · by_cases hvC : v ∈ C
                    · have hv_SR : v ∈ S \ R := hC hvC
                      have hv_filt : v ∈ (S \ R).filter (fun u => f u = r₀) := hC_eq.symm ▸ hvC
                      have hfv : f v = r₀ := (Finset.mem_filter.mp hv_filt).2
                      have h_p₀ := hK_pi v; rw [if_pos hv_SR] at h_p₀
                      have h_inc := hK_inc v hv_SR; rw [hfv, hKr₀] at h_inc
                      simp [hvC, h_p₀, h_inc]
                    · by_cases hv_sdiff : v ∈ S' \ R'
                      · have hv_SR : v ∈ S \ R := (Finset.mem_sdiff.mp (h_sdiff ▸ hv_sdiff)).1
                        have h_p₀ := hK_pi v; rw [if_pos hv_SR] at h_p₀
                        simp [hvC, hv_sdiff, h_p₀]
                      · have hv_not_SR : v ∉ S \ R := fun h_in => by
                          rw [← h_union_C, Finset.mem_union] at h_in
                          exact h_in.elim hvC hv_sdiff
                        have h_eq := hK_pi v; rw [if_neg hv_not_SR] at h_eq
                        simp [hvC, hv_sdiff, h_eq]
                  · have hv_SR : v ∈ S \ R := (Finset.mem_sdiff.mp (h_sdiff ▸ hv)).1
                    have hv_not_C : v ∉ C := (Finset.mem_sdiff.mp (h_sdiff ▸ hv)).2
                    simpa [restrictForest, hv_not_C] using hK_inc v hv_SR
                · rintro ⟨hK_pi, hK_inc⟩
                  have hKr₀ : K r₀ = K_R r₀ := by
                    have h := hK_pi r₀
                    rwa [if_neg hr₀_not_C, if_neg hr₀_not_S'R', Finset.mem_singleton] at h
                  refine ⟨fun v => ?_, fun v hv_SR => ?_⟩
                  · by_cases hv_SR : v ∈ S \ R
                    · rw [← h_union_C, Finset.mem_union] at hv_SR
                      rcases hv_SR with hvC | hv_sdiff
                      · have h := hK_pi v; rw [if_pos hvC, Finset.mem_filter] at h
                        rw [if_pos (hC hvC)]; exact h.1
                      · have hv_not_C : v ∉ C := (Finset.mem_sdiff.mp (h_sdiff ▸ hv_sdiff)).2
                        have h := hK_pi v; rw [if_neg hv_not_C, if_pos hv_sdiff] at h
                        rw [if_pos ((Finset.mem_sdiff.mp (h_sdiff ▸ hv_sdiff)).1)]; exact h
                    · have hv_not_C : v ∉ C := fun h => hv_SR (hC h)
                      have hv_not_sdiff : v ∉ S' \ R' := fun h =>
                        hv_SR ((Finset.mem_sdiff.mp (h_sdiff ▸ h)).1)
                      have h := hK_pi v; rw [if_neg hv_not_C, if_neg hv_not_sdiff] at h
                      rw [if_neg hv_SR]; exact h
                  · rw [← h_union_C, Finset.mem_union] at hv_SR
                    rcases hv_SR with hvC | hv_sdiff
                    · have hv_filt : v ∈ (S \ R).filter (fun u => f u = r₀) := hC_eq.symm ▸ hvC
                      have hfv : f v = r₀ := (Finset.mem_filter.mp hv_filt).2
                      have h := hK_pi v; rw [if_pos hvC, Finset.mem_filter] at h
                      rw [hfv, hKr₀]; exact h.2
                    · have hv_not_C : v ∉ C := (Finset.mem_sdiff.mp (h_sdiff ▸ hv_sdiff)).2
                      have h := hK_inc v hv_sdiff
                      simpa [restrictForest, hv_not_C] using h
              rw [h_dom_eq, Finset.sum_filter]
              rw [piFinset_split_sum C (S' \ R') h_disj_C (fun _ => T₀) (fun _ => P₀) K_R]
              refine Finset.sum_congr rfl fun K_C _ => ?_
              dsimp [innerTerm]
              rw [Finset.sum_filter, Finset.mul_sum]
              refine Finset.sum_congr rfl fun K hK => ?_
              split_ifs with h_inc
              · rw [← h_union_C, Finset.prod_union h_disj_C]
                congr 1
                refine Finset.prod_congr rfl fun u hu => ?_
                have hu_not : u ∉ S' \ R' := Finset.disjoint_left.mp h_disj_C hu
                have hKu := Fintype.mem_piFinset.mp hK u
                rw [if_neg hu_not, Finset.mem_singleton] at hKu
                rw [hKu]
              · ring
            rw [Finset.sum_congr rfl h_f_eq, Finset.sum_comm]
            have h_inner_le : ∀ K_C ∈ PiC,
                (∑ f ∈ (arborescenceForests S R).filter (fun f => (S \ R).filter (fun u => f u = r₀) = C),
                  (∏ u ∈ C, w (K_C u)) * innerTerm K_C (restrictForest C f)) ≤
                (∏ u ∈ C, w (K_C u)) * forestPolymerSum P₀ incompat w S' R' K_C := by
              intro K_C hK_C
              rw [← Finset.mul_sum]
              have h_prod_nn : 0 ≤ ∏ u ∈ C, w (K_C u) := by
                refine Finset.prod_nonneg fun u hu => ?_
                have h := Fintype.mem_piFinset.mp hK_C u
                rw [if_pos hu] at h
                exact hw (K_C u) (Finset.mem_filter.mp h).1
              refine mul_le_mul_of_nonneg_left ?_ h_prod_nn
              rw [← Finset.sum_image restrictForest_injOn]
              refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun f' _ _ => ?_)
              · rw [Finset.image_subset_iff]
                intro f hf
                exact restrictForest_mem_arborescenceForests hR_sub hr₀_R hC
                  (Finset.mem_filter.mp hf).1 (Finset.mem_filter.mp hf).2
              · refine Finset.sum_nonneg fun K hK => Finset.prod_nonneg fun v hv => ?_
                have hv_P₀ := (Fintype.mem_piFinset.mp (Finset.mem_filter.mp hK).1) v
                rw [if_pos hv] at hv_P₀; exact hw (K v) hv_P₀
            let L := C.toList
            have hL_nodup : L.Nodup := Finset.nodup_toList C
            have hL_toFinset : L.toFinset = C := by ext x; simp [L]
            have hL_len : L.length = C.card := Finset.length_toList C
            let roots'' := L ++ roots'
            have h_roots''_nodup : roots''.Nodup := by
              refine List.nodup_append.mpr ⟨hL_nodup, hroots'_nodup, fun x hxL y hyR' h_eq => ?_⟩
              subst h_eq
              have hxC : x ∈ C := hL_toFinset ▸ List.mem_toFinset.mpr hxL
              have hxR : x ∈ R := by
                have : x ∈ R.erase r₀ := hR_erase.symm ▸ List.mem_toFinset.mpr hyR'
                exact Finset.mem_of_mem_erase this
              exact (Finset.mem_sdiff.mp (hC hxC)).2 hxR
            have h_roots''_toFinset : roots''.toFinset = R' := by
              dsimp [roots'', R']
              rw [List.toFinset_append, hL_toFinset, ← hR_erase, Finset.union_comm]
            have h_roots''_sub : roots''.toFinset ⊆ S' := by
              rw [h_roots''_toFinset]
              refine Finset.union_subset (Finset.erase_subset_erase r₀ hR_sub) ?_
              intro x hxC
              have hx_SR := hC hxC
              exact Finset.mem_erase.mpr ⟨fun h_eq => (Finset.mem_sdiff.mp hx_SR).2 (h_eq ▸ hr₀_R),
                (Finset.mem_sdiff.mp hx_SR).1⟩
            have h_sdiff_card : (S' \ roots''.toFinset).card = (S \ R).card - C.card := by
              rw [h_roots''_toFinset, h_sdiff]
              have := Finset.card_sdiff_add_card_eq_card hC; omega
            have h_K_C_bound : ∀ K_C ∈ PiC,
                (∏ u ∈ C, w (K_C u)) * forestPolymerSum P₀ incompat w S' R' K_C ≤
                  (((S \ R).card - C.card).factorial : ℝ) *
                    (((L.map K_C).map w).prod *
                      kpForestWeight P₀ incompat w s (L.map K_C ++ roots'.map K_R)) := by
              intro K_C hK_C
              have h_prod_nn : 0 ≤ ∏ u ∈ C, w (K_C u) := by
                refine Finset.prod_nonneg fun u hu => ?_
                have h := Fintype.mem_piFinset.mp hK_C u
                rw [if_pos hu] at h
                exact hw (K_C u) (Finset.mem_filter.mp h).1
              have h_ih := ih S' roots'' hS'_card h_roots''_nodup h_roots''_sub K_C
              rw [h_roots''_toFinset] at h_ih
              have h_sdiff_card' : (S' \ R').card = (S \ R).card - C.card := by
                rw [h_sdiff]; have := Finset.card_sdiff_add_card_eq_card hC; omega
              rw [h_sdiff_card'] at h_ih
              have h_map_roots' : roots'.map K_C = roots'.map K_R := by
                refine List.map_congr_left fun v hv => ?_
                have hv_R : v ∈ R.erase r₀ := hR_erase.symm ▸ List.mem_toFinset.mpr hv
                have hv_not_C : v ∉ C := fun hvC =>
                  (Finset.mem_sdiff.mp (hC hvC)).2 (Finset.mem_of_mem_erase hv_R)
                have h := Fintype.mem_piFinset.mp hK_C v
                rw [if_neg hv_not_C, Finset.mem_singleton] at h
                exact h
              have h_map_roots'' : roots''.map K_C = L.map K_C ++ roots'.map K_R := by
                dsimp [roots'']; rw [List.map_append, h_map_roots']
              rw [h_map_roots''] at h_ih
              have h_prod_L : (∏ u ∈ C, w (K_C u)) = ((L.map K_C).map w).prod := by
                rw [← hL_toFinset, List.prod_toFinset _ hL_nodup, List.map_map]; rfl
              calc (∏ u ∈ C, w (K_C u)) * forestPolymerSum P₀ incompat w S' R' K_C
                _ ≤ (∏ u ∈ C, w (K_C u)) *
                    ((((S \ R).card - C.card).factorial : ℝ) *
                      kpForestWeight P₀ incompat w s (L.map K_C ++ roots'.map K_R)) :=
                    mul_le_mul_of_nonneg_left h_ih h_prod_nn
                _ = (((S \ R).card - C.card).factorial : ℝ) *
                    (((L.map K_C).map w).prod *
                      kpForestWeight P₀ incompat w s (L.map K_C ++ roots'.map K_R)) := by
                    rw [h_prod_L]; ring
            calc (∑ K_C ∈ PiC, ∑ f ∈ (arborescenceForests S R).filter (fun f => (S \ R).filter (fun u => f u = r₀) = C),
                  (∏ u ∈ C, w (K_C u)) * innerTerm K_C (restrictForest C f))
              _ ≤ ∑ K_C ∈ PiC, (∏ u ∈ C, w (K_C u)) * forestPolymerSum P₀ incompat w S' R' K_C :=
                  Finset.sum_le_sum h_inner_le
              _ ≤ ∑ K_C ∈ PiC, (((S \ R).card - C.card).factorial : ℝ) *
                  (((L.map K_C).map w).prod *
                    kpForestWeight P₀ incompat w s (L.map K_C ++ roots'.map K_R)) :=
                  Finset.sum_le_sum h_K_C_bound
              _ = (((S \ R).card - C.card).factorial : ℝ) *
                  ∑ K_C ∈ Fintype.piFinset (fun v : Fin p => if v ∈ L.toFinset then T₀ else {K_R v}),
                    (((L.map K_C).map w).prod *
                      kpForestWeight P₀ incompat w s (L.map K_C ++ roots'.map K_R)) := by
                  rw [← Finset.mul_sum]; dsimp [PiC]; rw [hL_toFinset]
              _ = (((S \ R).card - C.card).factorial : ℝ) *
                  ∑ t ∈ Fintype.piFinset (fun _ : Fin L.length => T₀),
                    (((List.ofFn t).map w).prod *
                      kpForestWeight P₀ incompat w s (List.ofFn t ++ roots'.map K_R)) := by
                  rw [piFinset_toList_sum_eq L hL_nodup T₀ K_R
                    (fun M => (M.map w).prod * kpForestWeight P₀ incompat w s (M ++ roots'.map K_R))]
              _ = (((S \ R).card - C.card).factorial : ℝ) *
                  ∑ t ∈ Fintype.piFinset (fun _ : Fin C.card => T₀),
                    (∏ i : Fin C.card, w (t i)) *
                      kpForestWeight P₀ incompat w s (List.ofFn t ++ roots'.map K_R) := by
                  congr 1
                  rw [hL_len]
                  refine Finset.sum_congr rfl fun t _ => ?_
                  rw [list_map_ofFn_prod]
          unfold forestPolymerSum
          change (∑ f ∈ arborescenceForests S R, _) ≤ _
          rw [h_part, Finset.sum_biUnion h_part_disj]
          calc (∑ C ∈ (S \ R).powerset,
                ∑ f ∈ (arborescenceForests S R).filter (fun f => (S \ R).filter (fun u => f u = r₀) = C),
                  ∑ K ∈ (Fintype.piFinset (fun v : Fin p => if v ∈ S \ R then P₀ else {K_R v})).filter
                      (fun K => ∀ v ∈ S \ R, incompat (K (f v)) (K v)),
                    ∏ v ∈ S \ R, w (K v))
            _ ≤ ∑ C ∈ (S \ R).powerset,
                (((S \ R).card - C.card).factorial : ℝ) *
                  ∑ t ∈ Fintype.piFinset (fun _ : Fin C.card => P₀.filter (incompat (K_R r₀))),
                    (∏ i : Fin C.card, w (t i)) *
                      kpForestWeight P₀ incompat w s (List.ofFn t ++ roots'.map K_R) :=
                Finset.sum_le_sum h_C_bound
            _ = (((S \ R).card.factorial : ℝ)) *
                kpForestWeight P₀ incompat w (s + 1) ((r₀ :: roots').map K_R) := by
                rw [Finset.sum_powerset, List.map_cons]
                dsimp [kpForestWeight]
                simp only [List.length_map]
                rw [← h_SR_card, Finset.mul_sum]
                refine Finset.sum_congr rfl fun m hm => ?_
                have hm_le : m ≤ (S \ R).card := Nat.lt_succ_iff.mp (Finset.mem_range.mp hm)
                have h_card_congr : ∀ C ∈ (S \ R).powersetCard m,
                    (((S \ R).card - C.card).factorial : ℝ) *
                      (∑ t ∈ Fintype.piFinset (fun _ : Fin C.card => P₀.filter (incompat (K_R r₀))),
                        (∏ i : Fin C.card, w (t i)) *
                          kpForestWeight P₀ incompat w s (List.ofFn t ++ roots'.map K_R)) =
                    (((S \ R).card - m).factorial : ℝ) *
                      (∑ t ∈ Fintype.piFinset (fun _ : Fin m => P₀.filter (incompat (K_R r₀))),
                        (∏ i : Fin m, w (t i)) *
                          kpForestWeight P₀ incompat w s (List.ofFn t ++ roots'.map K_R)) := by
                  intro C hC_m
                  have hC_card : C.card = m := (Finset.mem_powersetCard.mp hC_m).2
                  subst hC_card; rfl
                rw [Finset.sum_congr rfl h_card_congr, Finset.sum_const, Finset.card_powersetCard,
                  nsmul_eq_mul, ← mul_assoc, ← mul_assoc ((S \ R).card.factorial : ℝ)]
                congr 1
                have h_fac : ((S \ R).card.choose m : ℝ) * (((S \ R).card - m).factorial : ℝ) * (m.factorial : ℝ) =
                    ((S \ R).card.factorial : ℝ) := by
                  have h_nat := Nat.choose_mul_factorial_mul_factorial hm_le
                  have h_cast : (((S \ R).card.choose m * m.factorial * ((S \ R).card - m).factorial : ℕ) : ℝ) =
                      ((S \ R).card.factorial : ℝ) := by exact_mod_cast h_nat
                  push_cast at h_cast
                  linarith [h_cast]
                have hm_ne : (m.factorial : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero m)
                calc ((S \ R).card.choose m : ℝ) * (((S \ R).card - m).factorial : ℝ)
                  _ = ((S \ R).card.choose m : ℝ) * (((S \ R).card - m).factorial : ℝ) * (m.factorial : ℝ) * (m.factorial : ℝ)⁻¹ :=
                      (mul_inv_cancel_right₀ hm_ne _).symm
                  _ = ((S \ R).card.factorial : ℝ) * (m.factorial : ℝ)⁻¹ := by rw [h_fac]

private lemma sum_range_le_swap (N : ℕ) (f : ℕ → ℕ → ℝ) :
    (∑ n ∈ Finset.range (N + 1), ∑ m ∈ Finset.range (n + 1), f m (n - m)) =
      ∑ m ∈ Finset.range (N + 1), ∑ j ∈ Finset.range (N - m + 1), f m j := by
  induction N with
  | zero => simp
  | succ N ih =>
      have h_lhs : (∑ n ∈ Finset.range (N + 1 + 1), ∑ m ∈ Finset.range (n + 1), f m (n - m)) =
          (∑ m ∈ Finset.range (N + 1), ∑ j ∈ Finset.range (N - m + 1), f m j) +
            ((∑ m ∈ Finset.range (N + 1), f m (N + 1 - m)) + f (N + 1) 0) := by
        rw [Finset.sum_range_succ (fun n => ∑ m ∈ Finset.range (n + 1), f m (n - m)) (N + 1), ih]
        rw [Finset.sum_range_succ (fun m => f m (N + 1 - m)) (N + 1), Nat.sub_self]
      have h_rhs : (∑ m ∈ Finset.range (N + 1 + 1), ∑ j ∈ Finset.range (N + 1 - m + 1), f m j) =
          (∑ m ∈ Finset.range (N + 1), ((∑ j ∈ Finset.range (N - m + 1), f m j) + f m (N + 1 - m))) +
            f (N + 1) 0 := by
        rw [Finset.sum_range_succ (fun m => ∑ j ∈ Finset.range (N + 1 - m + 1), f m j) (N + 1)]
        rw [Nat.sub_self, Finset.range_one, Finset.sum_singleton]
        congr 1
        refine Finset.sum_congr rfl fun m hm => ?_
        have hm_le : m ≤ N := Nat.lt_succ_iff.mp (Finset.mem_range.mp hm)
        have h_sub : N + 1 - m = (N - m) + 1 := Nat.succ_sub hm_le
        rw [h_sub, Finset.sum_range_succ (fun j => f m j) (N - m + 1), ← h_sub]
      rw [h_lhs, h_rhs, Finset.sum_add_distrib, add_assoc]

lemma sum_kpDegWeight_le_exp {α : Type*} [DecidableEq α]
    (P₀ : Finset α) (incompat : α → α → Prop) [DecidableRel incompat]
    {w a : α → ℝ} (hw : ∀ γ ∈ P₀, 0 ≤ w γ) (ha : ∀ γ ∈ P₀, 0 ≤ a γ)
    (h_kp_a : ∀ γ₀ ∈ P₀, (∑ γ ∈ P₀.filter (incompat γ₀), w γ * Real.exp (a γ)) ≤ a γ₀) :
    ∀ (N : ℕ) (Γ : List α), (∀ γ ∈ Γ, γ ∈ P₀) →
      (∑ n ∈ Finset.range (N + 1), kpForestWeight P₀ incompat w (n + Γ.length) Γ) ≤
        (Γ.map (fun γ => Real.exp (a γ))).prod := by
  intro N; induction N using Nat.strong_induction_on with
  | h N ih_N =>
      intro Γ; induction Γ with
      | nil =>
          intro _
          rw [Finset.sum_range_eq_add_Ico _ (Nat.succ_pos N)]
          have h_zero : ∀ x ∈ Finset.Ico 1 (N + 1),
              kpForestWeight P₀ incompat w (x + ([] : List α).length) ([] : List α) = 0 := by
            intro x hx
            rcases Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt (Finset.mem_Ico.mp hx).1) with ⟨k, rfl⟩
            rfl
          rw [Finset.sum_eq_zero h_zero, add_zero]
          simp [kpForestWeight]
      | cons γ₀ Γ' ih_Γ =>
          intro hΓ
          have hγ₀ : γ₀ ∈ P₀ := hΓ γ₀ List.mem_cons_self
          have hΓ' : ∀ γ ∈ Γ', γ ∈ P₀ := fun γ h => hΓ γ (List.mem_cons_of_mem γ₀ h)
          have h_expand : ∀ n ∈ Finset.range (N + 1),
              kpForestWeight P₀ incompat w (n + (γ₀ :: Γ').length) (γ₀ :: Γ') =
                ∑ m ∈ Finset.range (n + 1), ((m.factorial : ℝ)⁻¹) *
                  ∑ t ∈ Fintype.piFinset (fun _ : Fin m => P₀.filter (incompat γ₀)),
                    (∏ i : Fin m, w (t i)) *
                      kpForestWeight P₀ incompat w ((n - m) + (List.ofFn t ++ Γ').length) (List.ofFn t ++ Γ') := by
            intro n _
            have h_len : n + (γ₀ :: Γ').length = (n + Γ'.length) + 1 := by simp [List.length_cons, add_assoc]
            rw [h_len]
            dsimp [kpForestWeight]
            rw [Nat.add_sub_cancel]
            refine Finset.sum_congr rfl fun m hm => ?_
            congr 1
            refine Finset.sum_congr rfl fun t _ => ?_
            have hm_le : m ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hm)
            have h_idx : n + Γ'.length = (n - m) + (List.ofFn t ++ Γ').length := by
              simp only [List.length_append, List.length_ofFn]; omega
            rw [h_idx]
          rw [Finset.sum_congr rfl h_expand]
          rw [sum_range_le_swap N (fun m j => ((m.factorial : ℝ)⁻¹) *
            ∑ t ∈ Fintype.piFinset (fun _ : Fin m => P₀.filter (incompat γ₀)),
              (∏ i : Fin m, w (t i)) *
                kpForestWeight P₀ incompat w (j + (List.ofFn t ++ Γ').length) (List.ofFn t ++ Γ'))]
          have h_m_bound : ∀ m ∈ Finset.range (N + 1),
              (∑ j ∈ Finset.range (N - m + 1), ((m.factorial : ℝ)⁻¹) *
                ∑ t ∈ Fintype.piFinset (fun _ : Fin m => P₀.filter (incompat γ₀)),
                  (∏ i : Fin m, w (t i)) *
                    kpForestWeight P₀ incompat w (j + (List.ofFn t ++ Γ').length) (List.ofFn t ++ Γ')) ≤
              ((a γ₀) ^ m / (m.factorial : ℝ)) * (Γ'.map (fun γ => Real.exp (a γ))).prod := by
            intro m hm
            rw [← Finset.mul_sum, Finset.sum_comm]
            have h_t_bound : ∀ t ∈ Fintype.piFinset (fun _ : Fin m => P₀.filter (incompat γ₀)),
                (∑ j ∈ Finset.range (N - m + 1), (∏ i : Fin m, w (t i)) *
                  kpForestWeight P₀ incompat w (j + (List.ofFn t ++ Γ').length) (List.ofFn t ++ Γ')) ≤
                (∏ i : Fin m, (w (t i) * Real.exp (a (t i)))) * (Γ'.map (fun γ => Real.exp (a γ))).prod := by
              intro t ht
              rw [← Finset.mul_sum]
              have h_prod_nn : 0 ≤ ∏ i : Fin m, w (t i) := Finset.prod_nonneg fun i _ =>
                hw (t i) (Finset.mem_filter.mp (Fintype.mem_piFinset.mp ht i)).1
              have h_rec_le : (∑ j ∈ Finset.range (N - m + 1),
                  kpForestWeight P₀ incompat w (j + (List.ofFn t ++ Γ').length) (List.ofFn t ++ Γ')) ≤
                  (∏ i : Fin m, Real.exp (a (t i))) * (Γ'.map (fun γ => Real.exp (a γ))).prod := by
                cases m with
                | zero =>
                    simpa [List.ofFn_zero] using ih_Γ hΓ'
                | succ m' =>
                    have hm_le : m' + 1 ≤ N := Nat.lt_succ_iff.mp (Finset.mem_range.mp hm)
                    have h_lt : N - (m' + 1) < N := by omega
                    have h_mem_all : ∀ γ ∈ List.ofFn t ++ Γ', γ ∈ P₀ := by
                      intro γ hγ
                      rcases List.mem_append.mp hγ with h_ofFn | h_Γ'
                      · rcases List.mem_ofFn.mp h_ofFn with ⟨i, rfl⟩
                        exact (Finset.mem_filter.mp (Fintype.mem_piFinset.mp ht i)).1
                      · exact hΓ' γ h_Γ'
                    have h_ih := ih_N (N - (m' + 1)) h_lt (List.ofFn t ++ Γ') h_mem_all
                    have h_prod_map : ((List.ofFn t ++ Γ').map (fun γ => Real.exp (a γ))).prod =
                        (∏ i : Fin (m' + 1), Real.exp (a (t i))) * (Γ'.map (fun γ => Real.exp (a γ))).prod := by
                      rw [List.map_append, List.prod_append, list_map_ofFn_prod]
                    rwa [h_prod_map] at h_ih
              calc (∏ i : Fin m, w (t i)) * ∑ j ∈ Finset.range (N - m + 1),
                    kpForestWeight P₀ incompat w (j + (List.ofFn t ++ Γ').length) (List.ofFn t ++ Γ')
                _ ≤ (∏ i : Fin m, w (t i)) *
                    ((∏ i : Fin m, Real.exp (a (t i))) * (Γ'.map (fun γ => Real.exp (a γ))).prod) :=
                    mul_le_mul_of_nonneg_left h_rec_le h_prod_nn
                _ = (∏ i : Fin m, (w (t i) * Real.exp (a (t i)))) * (Γ'.map (fun γ => Real.exp (a γ))).prod := by
                    rw [← mul_assoc, ← Finset.prod_mul_distrib]
            have h_sum_t : (∑ t ∈ Fintype.piFinset (fun _ : Fin m => P₀.filter (incompat γ₀)),
                ∏ i : Fin m, (w (t i) * Real.exp (a (t i)))) =
                (∑ γ ∈ P₀.filter (incompat γ₀), w γ * Real.exp (a γ)) ^ m := by
              simpa using piFinset_sum_prod_eq_pow (Finset.univ : Finset (Fin m))
                (P₀.filter (incompat γ₀)) (fun _ => γ₀) (fun γ => w γ * Real.exp (a γ))
            have h_pow_le : (∑ γ ∈ P₀.filter (incompat γ₀), w γ * Real.exp (a γ)) ^ m ≤ (a γ₀) ^ m := by
              refine pow_le_pow_left₀ (Finset.sum_nonneg fun γ hγ => ?_) (h_kp_a γ₀ hγ₀) m
              exact mul_nonneg (hw γ (Finset.mem_filter.mp hγ).1) (Real.exp_nonneg _)
            have h_G_nn : 0 ≤ (Γ'.map (fun γ => Real.exp (a γ))).prod :=
              List.prod_nonneg (by intro x hx; rcases List.mem_map.mp hx with ⟨γ, _, rfl⟩; exact Real.exp_nonneg _)
            calc ((m.factorial : ℝ)⁻¹) * ∑ t ∈ Fintype.piFinset (fun _ : Fin m => P₀.filter (incompat γ₀)),
                  ∑ j ∈ Finset.range (N - m + 1), (∏ i : Fin m, w (t i)) *
                    kpForestWeight P₀ incompat w (j + (List.ofFn t ++ Γ').length) (List.ofFn t ++ Γ')
              _ ≤ ((m.factorial : ℝ)⁻¹) * ∑ t ∈ Fintype.piFinset (fun _ : Fin m => P₀.filter (incompat γ₀)),
                  (∏ i : Fin m, (w (t i) * Real.exp (a (t i)))) * (Γ'.map (fun γ => Real.exp (a γ))).prod :=
                  mul_le_mul_of_nonneg_left (Finset.sum_le_sum h_t_bound) (inv_nonneg.mpr (Nat.cast_nonneg _))
              _ = ((m.factorial : ℝ)⁻¹) * ((∑ γ ∈ P₀.filter (incompat γ₀), w γ * Real.exp (a γ)) ^ m *
                  (Γ'.map (fun γ => Real.exp (a γ))).prod) := by rw [← Finset.sum_mul, h_sum_t]
              _ ≤ ((m.factorial : ℝ)⁻¹) * ((a γ₀) ^ m * (Γ'.map (fun γ => Real.exp (a γ))).prod) :=
                  mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right h_pow_le h_G_nn)
                    (inv_nonneg.mpr (Nat.cast_nonneg _))
              _ = ((a γ₀) ^ m / (m.factorial : ℝ)) * (Γ'.map (fun γ => Real.exp (a γ))).prod := by
                  ring
          calc ∑ m ∈ Finset.range (N + 1), ∑ j ∈ Finset.range (N - m + 1), ((m.factorial : ℝ)⁻¹) *
                ∑ t ∈ Fintype.piFinset (fun _ : Fin m => P₀.filter (incompat γ₀)),
                  (∏ i : Fin m, w (t i)) *
                    kpForestWeight P₀ incompat w (j + (List.ofFn t ++ Γ').length) (List.ofFn t ++ Γ')
            _ ≤ ∑ m ∈ Finset.range (N + 1),
                ((a γ₀) ^ m / (m.factorial : ℝ)) * (Γ'.map (fun γ => Real.exp (a γ))).prod :=
                Finset.sum_le_sum h_m_bound
            _ = (∑ m ∈ Finset.range (N + 1), (a γ₀) ^ m / (m.factorial : ℝ)) *
                (Γ'.map (fun γ => Real.exp (a γ))).prod := (Finset.sum_mul _ _ _).symm
            _ ≤ Real.exp (a γ₀) * (Γ'.map (fun γ => Real.exp (a γ))).prod := by
                refine mul_le_mul_of_nonneg_right (Real.sum_le_exp_of_nonneg (ha γ₀ hγ₀) (N + 1)) ?_
                exact List.prod_nonneg (by intro x hx; rcases List.mem_map.mp hx with ⟨γ, _, rfl⟩; exact Real.exp_nonneg _)
            _ = ((γ₀ :: Γ').map (fun γ => Real.exp (a γ))).prod := by simp

lemma sum_biUnion_le_of_nonneg {α β : Type*} [DecidableEq α] [DecidableEq β]
    (S : Finset α) (t : α → Finset β) {g : β → ℝ} (hg : ∀ x, 0 ≤ g x) :
    (∑ x ∈ S.biUnion t, g x) ≤ ∑ u ∈ S, ∑ x ∈ t u, g x := by
  induction S using Finset.induction_on with
  | empty => simp
  | @insert a S' ha ih =>
      rw [Finset.biUnion_insert, Finset.sum_insert ha]
      have h_u : (∑ x ∈ t a ∪ S'.biUnion t, g x) ≤ (∑ x ∈ t a, g x) + (∑ x ∈ S'.biUnion t, g x) := by
        rw [← Finset.sum_union_inter]
        linarith [Finset.sum_nonneg (fun x (_ : x ∈ t a ∩ S'.biUnion t) => hg x)]
      linarith

def kpNatDist (a b : ℕ) : ℕ := (a - b) + (b - a)

lemma kpNatDist_self (a : ℕ) : kpNatDist a a = 0 := by unfold kpNatDist; omega

lemma kpNatDist_comm (a b : ℕ) : kpNatDist a b = kpNatDist b a := by unfold kpNatDist; omega

lemma kpNatDist_triangle (a b c : ℕ) : kpNatDist a c ≤ kpNatDist a b + kpNatDist b c := by
  unfold kpNatDist; omega

lemma kpNatDist_le_of_mem_boxCube {L r : ℕ} {x0 y : Box3D L}
    (hy : y ∈ boxCube x0 r) (i : Fin 3) :
    kpNatDist (y i).val (x0 i).val ≤ r := by
  rw [mem_boxCube] at hy
  have := (hy i).1; have := (hy i).2
  unfold kpNatDist; omega

lemma kpNatDist_le_of_mem_enclosingBoxCube {L r R : ℕ} {x0 y : Box3D L}
    (hy : y ∈ enclosingBoxCube x0 r R) (i : Fin 3) :
    kpNatDist (y i).val (x0 i).val ≤ R := by
  rw [enclosingBoxCube, mem_boxCube] at hy
  have h1 := (hy i).1; have h2 := (hy i).2
  (try dsimp at h1 h2)
  unfold kpNatDist; omega

lemma kpNatDist_anchor_kpStaticCSSCheckAnchor_le
    {L q_code r_0 m_max : ℕ} [NeZero L]
    (D_field : Box3D L → LocalCSSDescriptor q_code r_0 m_max)
    (sys : IndexedCommutingProjectorHamiltonian 3 L (UniformSite3D L (CodeSlotConfig q_code)) (StaticCSSCheckIdx L q_code m_max))
    (h_sys_supp : ∀ idx, sys.support idx = staticCSSCheckSupport D_field idx)
    {C_rca : ℝ} {r : ℕ} {A : Finset (Box3D L)} {c : StaticCSSCheckIdx L q_code m_max}
    (hc : c ∈ kpRCACollarChecks sys C_rca r A) (i : Fin 3) :
    kpNatDist (kpStaticCSSCheckAnchor c i).val (anchorOfCube r A i).val ≤
      linearExpansionRadius C_rca r := by
  have h_in : kpStaticCSSCheckAnchor c ∈ kpRCACollarCube C_rca r A :=
    (Finset.mem_filter.mp hc).2 (h_sys_supp c ▸ kpStaticCSSCheckAnchor_mem_support D_field c)
  exact kpNatDist_le_of_mem_enclosingBoxCube h_in i

lemma linearExpansionRadius_le_ceil_mul (C_rca : ℝ) (r : ℕ) :
    linearExpansionRadius C_rca r ≤ Nat.ceil C_rca * r := by
  unfold linearExpansionRadius
  refine Nat.ceil_le.mpr ?_
  push_cast
  exact mul_le_mul_of_nonneg_right (Nat.le_ceil C_rca) (Nat.cast_nonneg r)

lemma ceil_add_one_mul_scaleCal_le_kpCollarMaxCheckCard
    {R_cut r_0 w_0 : ℕ} (hR_cut : 1 ≤ R_cut) {C_rca : ℝ} (hC_rca : 0 ≤ C_rca) :
    (Nat.ceil C_rca + 1) * (4 * (Nat.ceil C_rca + 1) * (r_0 + 1) * R_cut) ≤
      kpCollarMaxCheckCard R_cut r_0 w_0 C_rca := by
  let E := linearExpansionRadius C_rca R_cut
  let B := 2 * (R_cut + 2 * E + r_0) + 1
  have h_ceil_le_E : Nat.ceil C_rca ≤ E := by
    unfold E linearExpansionRadius
    refine Nat.ceil_mono ?_
    have hR1 : (1 : ℝ) ≤ (R_cut : ℝ) := by exact_mod_cast hR_cut
    nlinarith
  have h_mul_le : Nat.ceil C_rca * R_cut ≤ E + R_cut := by
    have h_lt : (Nat.ceil C_rca : ℝ) < C_rca + 1 := Nat.ceil_lt_add_one hC_rca
    have hR_pos : (0 : ℝ) < (R_cut : ℝ) := by exact_mod_cast (Nat.lt_of_lt_of_le zero_lt_one hR_cut)
    have h_mul_lt : (Nat.ceil C_rca : ℝ) * (R_cut : ℝ) < (C_rca + 1) * (R_cut : ℝ) :=
      mul_lt_mul_of_pos_right h_lt hR_pos
    have hE_ge : C_rca * (R_cut : ℝ) ≤ (E : ℝ) := Nat.le_ceil (C_rca * (R_cut : ℝ))
    have h_real : ((Nat.ceil C_rca * R_cut : ℕ) : ℝ) < ((E + R_cut : ℕ) : ℝ) + 1 := by
      push_cast; nlinarith
    have h_nat : Nat.ceil C_rca * R_cut < E + R_cut + 1 := by exact_mod_cast h_real
    omega
  have hf1 : 2 * (Nat.ceil C_rca + 1) ≤ B := by dsimp [B]; omega
  have hf2 : (Nat.ceil C_rca + 1) * R_cut ≤ B := by
    have : (Nat.ceil C_rca + 1) * R_cut = Nat.ceil C_rca * R_cut + R_cut := by ring
    dsimp [B]; omega
  have hf3 : 2 * (r_0 + 1) ≤ B := by dsimp [B]; omega
  have h_prod : (2 * (Nat.ceil C_rca + 1)) * ((Nat.ceil C_rca + 1) * R_cut) * (2 * (r_0 + 1)) ≤ B ^ 3 := by
    calc (2 * (Nat.ceil C_rca + 1)) * ((Nat.ceil C_rca + 1) * R_cut) * (2 * (r_0 + 1))
      _ ≤ B * B * B := Nat.mul_le_mul (Nat.mul_le_mul hf1 hf2) hf3
      _ = B ^ 3 := by ring
  have h_eq : (Nat.ceil C_rca + 1) * (4 * (Nat.ceil C_rca + 1) * (r_0 + 1) * R_cut) =
      (2 * (Nat.ceil C_rca + 1)) * ((Nat.ceil C_rca + 1) * R_cut) * (2 * (r_0 + 1)) := by ring
  unfold kpCollarMaxCheckCard
  rw [h_eq]
  exact le_trans h_prod (le_trans (Nat.le_mul_of_pos_right (B ^ 3) (Nat.succ_pos w_0)) (Nat.le_succ _))

lemma card_boxCube_le_pow {L : ℕ} [NeZero L] (x0 : Box3D L) (R : ℕ) :
    (boxCube x0 R).card ≤ R ^ 3 := by
  have hL_pos : 0 < L := NeZero.pos L
  let g : (Fin 3 → Fin R) → Box3D L := fun k i =>
    ⟨min (L - 1) ((x0 i).val + (k i).val),
      Nat.lt_of_le_of_lt (Nat.min_le_left _ _) (Nat.sub_lt hL_pos zero_lt_one)⟩
  have h_sub : boxCube x0 R ⊆ Finset.univ.image g := fun y hy => by
    rw [mem_boxCube] at hy
    have hk_lt : ∀ i : Fin 3, (y i).val - (x0 i).val < R := fun i => by
      have := (hy i).1; have := (hy i).2; omega
    let k : Fin 3 → Fin R := fun i => ⟨(y i).val - (x0 i).val, hk_lt i⟩
    have hy_eq : g k = y := by
      funext i; apply Fin.ext; have := (hy i).1; have := (y i).isLt; dsimp [g, k]; omega
    exact Finset.mem_image.mpr ⟨k, Finset.mem_univ k, hy_eq⟩
  calc (boxCube x0 R).card
    _ ≤ (Finset.univ : Finset (Fin 3 → Fin R)).card :=
        le_trans (Finset.card_le_card h_sub) Finset.card_image_le
    _ = R ^ 3 := by rw [Finset.card_univ, Fintype.card_fun, Fintype.card_fin, Fintype.card_fin]

lemma card_filter_boxCubes_anchor_kpNatDist_le {L : ℕ} [NeZero L]
    (r R : ℕ) (z : Box3D L) :
    ((boxCubes 3 L r).filter (fun A =>
      ∀ i : Fin 3, kpNatDist (anchorOfCube r A i).val (z i).val ≤ R)).card ≤
      (2 * R + 1) ^ 3 := by
  let x_min : Box3D L := fun i => ⟨(z i).val - R, Nat.sub_lt_of_lt (z i).isLt⟩
  have h_maps : ∀ A ∈ (boxCubes 3 L r).filter (fun A =>
      ∀ i : Fin 3, kpNatDist (anchorOfCube r A i).val (z i).val ≤ R),
      anchorOfCube r A ∈ boxCube x_min (2 * R + 1) := by
    intro A hA
    have h_dist := (Finset.mem_filter.mp hA).2
    rw [mem_boxCube]
    intro i
    have hi := h_dist i
    dsimp [x_min]
    unfold kpNatDist at hi
    omega
  have h_inj : Set.InjOn (anchorOfCube r) (((boxCubes 3 L r).filter (fun A =>
      ∀ i : Fin 3, kpNatDist (anchorOfCube r A i).val (z i).val ≤ R)) : Set (Finset (Box3D L))) := by
    intro A₁ hA₁ A₂ hA₂ h_eq
    have h₁ := boxCube_anchorOfCube (Finset.mem_filter.mp hA₁).1
    have h₂ := boxCube_anchorOfCube (Finset.mem_filter.mp hA₂).1
    rw [← h₁, ← h₂, h_eq]
  exact le_trans (Finset.card_le_card_of_injOn (anchorOfCube r) h_maps h_inj)
    (card_boxCube_le_pow x_min (2 * R + 1))

lemma twenty_seven_mul_succ_le_kpCollarMaxCheckCard
    {R_cut r_0 w_0 : ℕ} (hR_cut : 1 ≤ R_cut) (C_RCA : ℝ) :
    27 * (w_0 + 1) + 1 ≤ kpCollarMaxCheckCard R_cut r_0 w_0 C_RCA := by
  unfold kpCollarMaxCheckCard
  have h_base : 3 ≤ 2 * (R_cut + 2 * linearExpansionRadius C_RCA R_cut + r_0) + 1 := by omega
  have h_pow : 27 ≤ (2 * (R_cut + 2 * linearExpansionRadius C_RCA R_cut + r_0) + 1) ^ 3 :=
    Nat.pow_le_pow_left h_base 3
  exact Nat.add_le_add_right (Nat.mul_le_mul_right (w_0 + 1) h_pow) 1

lemma card_cubeIntersectingChecks_le_pow_mul_w0
    {L q_code r_0 m_max w_0 R_cut : ℕ} [NeZero L]
    (sys : IndexedCommutingProjectorHamiltonian 3 L (UniformSite3D L (CodeSlotConfig q_code)) (StaticCSSCheckIdx L q_code m_max))
    (h_geom : sys.IsGeometricallyLocal r_0 w_0)
    {r : ℕ} (_hr : r ∈ Finset.Icc 1 (min R_cut L))
    {A : Finset (Box3D L)} (hA : A ∈ boxCubes 3 L r) :
    (cubeIntersectingChecks sys A).card ≤ r ^ 3 * w_0 := by
  have hA_card : A.card ≤ r ^ 3 := by
    rw [← boxCube_anchorOfCube hA]
    exact card_boxCube_le_pow (anchorOfCube r A) r
  have h_col_sub : cubeIntersectingChecks sys A ⊆
      A.biUnion (fun y => Finset.univ.filter (fun c => y ∈ sys.support c)) := fun c hc => by
    rcases Finset.not_disjoint_iff.mp (Finset.mem_filter.mp hc).2 with ⟨y, hy_supp, hyA⟩
    exact Finset.mem_biUnion.mpr ⟨y, hyA, Finset.mem_filter.mpr ⟨Finset.mem_univ c, hy_supp⟩⟩
  have h_card_col : (cubeIntersectingChecks sys A).card ≤ A.card * w_0 :=
    smul_eq_mul A.card w_0 ▸ le_trans (le_trans (Finset.card_le_card h_col_sub) Finset.card_biUnion_le)
      (Finset.sum_le_card_nsmul A _ w_0 (fun y _ => h_geom.2 y))
  exact le_trans h_card_col (Nat.mul_le_mul_right w_0 hA_card)

lemma card_cubeIntersectingChecks_cast_le_div_twenty_seven
    {L q_code r_0 m_max w_0 R_cut : ℕ} [NeZero L]
    {C_RCA c_wl : ℝ} (hR_cut : 1 ≤ R_cut)
    (sys : IndexedCommutingProjectorHamiltonian 3 L (UniformSite3D L (CodeSlotConfig q_code)) (StaticCSSCheckIdx L q_code m_max))
    (h_geom : sys.IsGeometricallyLocal r_0 w_0)
    (hc_wl_cal : (kpCollarMaxCheckCard R_cut r_0 w_0 C_RCA : ℝ) ≤ c_wl)
    {r : ℕ} (hr : r ∈ Finset.Icc 1 (min R_cut L))
    {A : Finset (Box3D L)} (hA : A ∈ boxCubes 3 L r) :
    ((cubeIntersectingChecks sys A).card : ℝ) ≤ (1 / 27 : ℝ) * c_wl * ((r : ℝ) ^ 3) := by
  have h1 := card_cubeIntersectingChecks_le_pow_mul_w0 sys h_geom hr hA
  have h2 := twenty_seven_mul_succ_le_kpCollarMaxCheckCard (r_0 := r_0) (w_0 := w_0) hR_cut C_RCA
  have h_w0 : (w_0 : ℝ) ≤ (1 / 27 : ℝ) * c_wl := by
    have h2_real : (27 : ℝ) * ((w_0 : ℝ) + 1) + 1 ≤ (kpCollarMaxCheckCard R_cut r_0 w_0 C_RCA : ℝ) := by
      exact_mod_cast h2
    linarith
  calc ((cubeIntersectingChecks sys A).card : ℝ)
    _ ≤ ((r ^ 3 * w_0 : ℕ) : ℝ) := by exact_mod_cast h1
    _ = (w_0 : ℝ) * ((r : ℝ) ^ 3) := by push_cast; ring
    _ ≤ ((1 / 27 : ℝ) * c_wl) * ((r : ℝ) ^ 3) :=
        mul_le_mul_of_nonneg_right h_w0 (by positivity)
    _ = (1 / 27 : ℝ) * c_wl * ((r : ℝ) ^ 3) := by ring

abbrev kpScaleCubeFinset (L R_cut : ℕ) : Finset (ℕ × Finset (Box3D L)) :=
  (Finset.Icc 1 (min R_cut L)).biUnion (fun r => (boxCubes 3 L r).image (fun A => (r, A)))

abbrev KPScaleCubeOverlap {L q_code m_max : ℕ} [NeZero L]
    (sys : IndexedCommutingProjectorHamiltonian 3 L (UniformSite3D L (CodeSlotConfig q_code)) (StaticCSSCheckIdx L q_code m_max))
    (C_rca : ℝ) (p q : ℕ × Finset (Box3D L)) : Prop :=
  p ≠ q ∧ ¬Disjoint (kpRCACollarChecks sys C_rca p.1 p.2) (kpRCACollarChecks sys C_rca q.1 q.2)

lemma mem_kpScaleCubeFinset_iff {L R_cut : ℕ} {p : ℕ × Finset (Box3D L)} :
    p ∈ kpScaleCubeFinset L R_cut ↔
      p.1 ∈ Finset.Icc 1 (min R_cut L) ∧ p.2 ∈ boxCubes 3 L p.1 := by
  unfold kpScaleCubeFinset
  rw [Finset.mem_biUnion]
  constructor
  · rintro ⟨r, hr, hA⟩
    rcases Finset.mem_image.mp hA with ⟨A, hA_mem, h_eq⟩
    have hr_eq : r = p.1 := congrArg Prod.fst h_eq
    have hA_eq : A = p.2 := congrArg Prod.snd h_eq
    subst hr_eq hA_eq
    exact ⟨hr, hA_mem⟩
  · rintro ⟨hr, hA⟩
    exact ⟨p.1, hr, Finset.mem_image.mpr ⟨p.2, hA, Prod.eta p⟩⟩

lemma card_filter_kpScaleCubeOverlap_le
    {L q_code r_0 m_max w_0 R_cut : ℕ} [NeZero L]
    (_hR_cut : 1 ≤ R_cut)
    (D_field : Box3D L → LocalCSSDescriptor q_code r_0 m_max)
    (sys : IndexedCommutingProjectorHamiltonian 3 L (UniformSite3D L (CodeSlotConfig q_code)) (StaticCSSCheckIdx L q_code m_max))
    (h_sys_checks : ∀ idx, sys.checkProj idx = staticCSSCheckProj D_field idx ∧
      sys.support idx = staticCSSCheckSupport D_field idx ∧ sys.weight idx = 1)
    (h_geom : sys.IsGeometricallyLocal r_0 w_0)
    {C_rca : ℝ} (hC_rca : 0 ≤ C_rca)
    {p : ℕ × Finset (Box3D L)} (hp : p ∈ kpScaleCubeFinset L R_cut) :
    ((kpScaleCubeFinset L R_cut).filter (KPScaleCubeOverlap sys C_rca p)).card ≤
      kpCollarMaxCheckCard R_cut r_0 w_0 C_rca ^ 3 := by
  let U := kpScaleCubeFinset L R_cut
  let K_geom := (2 * (R_cut + 2 * linearExpansionRadius C_rca R_cut + r_0) + 1) ^ 3 * (w_0 + 1)
  let Δ_V := kpCollarMaxCheckCard R_cut r_0 w_0 C_rca
  rcases mem_kpScaleCubeFinset_iff.mp hp with ⟨hp_r, _⟩
  have h_sub : U.filter (KPScaleCubeOverlap sys C_rca p) ⊆
      (kpRCACollarChecks sys C_rca p.1 p.2).biUnion (fun c =>
        (Finset.Icc 1 (min R_cut L)).biUnion (fun r =>
          ((boxCubes 3 L r).filter (fun A => c ∈ kpRCACollarChecks sys C_rca r A)).image (fun A => (r, A)))) := by
    intro q hq
    rcases Finset.mem_filter.mp hq with ⟨hq_U, _, h_nd⟩
    rcases mem_kpScaleCubeFinset_iff.mp hq_U with ⟨hq_r, hq_A⟩
    rcases Finset.not_disjoint_iff.mp h_nd with ⟨c, hc_p, hc_q⟩
    exact Finset.mem_biUnion.mpr ⟨c, hc_p, Finset.mem_biUnion.mpr ⟨q.1, hq_r,
      Finset.mem_image.mpr ⟨q.2, Finset.mem_filter.mpr ⟨hq_A, hc_q⟩, Prod.eta q⟩⟩⟩
  have h_c_card : ∀ c : StaticCSSCheckIdx L q_code m_max,
      ((Finset.Icc 1 (min R_cut L)).biUnion (fun r =>
        ((boxCubes 3 L r).filter (fun A => c ∈ kpRCACollarChecks sys C_rca r A)).image (fun A => (r, A)))).card ≤
      R_cut * K_geom := fun c => by
    have h_Icc : (Finset.Icc 1 (min R_cut L)).card ≤ R_cut := by
      rw [Nat.card_Icc]; have := Nat.min_le_left R_cut L; omega
    refine le_trans Finset.card_biUnion_le ?_
    refine le_trans (Finset.sum_le_card_nsmul _ _ K_geom fun r hr => ?_) ?_
    · exact le_trans Finset.card_image_le
        (card_filter_mem_kpRCACollarChecks_le D_field sys h_sys_checks hC_rca hr c)
    · rw [smul_eq_mul]
      exact Nat.mul_le_mul_right K_geom h_Icc
  have h_deg_le : (U.filter (KPScaleCubeOverlap sys C_rca p)).card ≤ Δ_V * (R_cut * K_geom) := by
    refine le_trans (Finset.card_le_card h_sub) (le_trans Finset.card_biUnion_le ?_)
    refine le_trans (Finset.sum_le_card_nsmul _ _ (R_cut * K_geom) fun c _ => h_c_card c) ?_
    rw [smul_eq_mul]
    exact Nat.mul_le_mul_right (R_cut * K_geom)
      (card_kpRCACollarChecks_le D_field sys h_sys_checks h_geom hC_rca hp_r p.2)
  have hR_le_K : R_cut ≤ K_geom := by
    have h_b : R_cut ≤ 2 * (R_cut + 2 * linearExpansionRadius C_rca R_cut + r_0) + 1 := by omega
    have h_p : R_cut ≤ (2 * (R_cut + 2 * linearExpansionRadius C_rca R_cut + r_0) + 1) ^ 3 := by
      calc R_cut
        _ ≤ R_cut ^ 3 := Nat.le_self_pow (by decide) R_cut
        _ ≤ (2 * (R_cut + 2 * linearExpansionRadius C_rca R_cut + r_0) + 1) ^ 3 := Nat.pow_le_pow_left h_b 3
    exact le_trans h_p (Nat.le_mul_of_pos_right _ (Nat.succ_pos w_0))
  have hK_le_Δ : K_geom ≤ Δ_V := Nat.le_succ K_geom
  have hR_le_Δ : R_cut ≤ Δ_V := le_trans hR_le_K hK_le_Δ
  calc (U.filter (KPScaleCubeOverlap sys C_rca p)).card
    _ ≤ Δ_V * (R_cut * K_geom) := h_deg_le
    _ ≤ Δ_V * (Δ_V * Δ_V) := Nat.mul_le_mul_left Δ_V (Nat.mul_le_mul hR_le_Δ hK_le_Δ)
    _ = Δ_V ^ 3 := by ring

lemma card_connected_kpScaleCubeFinset_of_root_le
    {L q_code r_0 m_max w_0 R_cut : ℕ} [NeZero L]
    (hR_cut : 1 ≤ R_cut)
    (D_field : Box3D L → LocalCSSDescriptor q_code r_0 m_max)
    (sys : IndexedCommutingProjectorHamiltonian 3 L (UniformSite3D L (CodeSlotConfig q_code)) (StaticCSSCheckIdx L q_code m_max))
    (h_sys_checks : ∀ idx, sys.checkProj idx = staticCSSCheckProj D_field idx ∧
      sys.support idx = staticCSSCheckSupport D_field idx ∧ sys.weight idx = 1)
    (h_geom : sys.IsGeometricallyLocal r_0 w_0)
    {C_rca : ℝ} (hC_rca : 0 ≤ C_rca)
    {p₀ : ℕ × Finset (Box3D L)} (hp₀ : p₀ ∈ kpScaleCubeFinset L R_cut)
    {n : ℕ} (hn : 1 ≤ n) :
    (((kpScaleCubeFinset L R_cut).powerset.filter (fun M =>
      p₀ ∈ M ∧ M.card = n ∧ KPIsConnectedSubgraph (KPScaleCubeOverlap sys C_rca) M)).card : ℝ) ≤
      (Real.exp (6 * (kpCollarMaxCheckCard R_cut r_0 w_0 C_rca : ℝ))) ^ n := by
  let Δ_V := kpCollarMaxCheckCard R_cut r_0 w_0 C_rca
  have hΔ_pos : 1 ≤ Δ_V ^ 3 := Nat.one_le_pow 3 Δ_V (Nat.succ_pos _)
  have h_klarner := kp_klarner_connected_subgraph_on_count_le
    (kpScaleCubeFinset L R_cut)
    (KPScaleCubeOverlap sys C_rca)
    (fun u v h => ⟨h.1.symm, fun hd => h.2 hd.symm⟩)
    hΔ_pos
    (fun p hp => card_filter_kpScaleCubeOverlap_le hR_cut D_field sys h_sys_checks h_geom hC_rca hp)
    hp₀ hn
  have h_cast : (((Δ_V ^ 3) ^ 2 : ℕ) : ℝ) ^ n ≤ (Real.exp (6 * (Δ_V : ℝ))) ^ n := by
    refine pow_le_pow_left₀ (Nat.cast_nonneg _) ?_ n
    have h_exp : (Δ_V : ℝ) ≤ Real.exp (Δ_V : ℝ) :=
      le_trans (by linarith) (Real.add_one_le_exp (Δ_V : ℝ))
    calc (((Δ_V ^ 3) ^ 2 : ℕ) : ℝ)
      _ = (Δ_V : ℝ) ^ 6 := by push_cast; ring
      _ ≤ (Real.exp (Δ_V : ℝ)) ^ 6 := pow_le_pow_left₀ (Nat.cast_nonneg _) h_exp 6
      _ = Real.exp (6 * (Δ_V : ℝ)) := by rw [← Real.exp_nat_mul]; norm_num
  exact le_trans (by exact_mod_cast h_klarner) h_cast

lemma exists_enclosing_boxCube_of_connected_kpScaleCubeFinset
    {L q_code r_0 m_max R_cut : ℕ} [NeZero L]
    (D_field : Box3D L → LocalCSSDescriptor q_code r_0 m_max)
    (sys : IndexedCommutingProjectorHamiltonian 3 L (UniformSite3D L (CodeSlotConfig q_code)) (StaticCSSCheckIdx L q_code m_max))
    (h_sys_supp : ∀ idx, sys.support idx = staticCSSCheckSupport D_field idx)
    {C_rca : ℝ} (_hC_rca : 0 ≤ C_rca)
    {M : Finset (ℕ × Finset (Box3D L))}
    (hM_sub : M ⊆ kpScaleCubeFinset L R_cut)
    (hM_ne : M.Nonempty)
    (h_conn : KPIsConnectedSubgraph (KPScaleCubeOverlap sys C_rca) M) :
    ∃ x0 : Box3D L,
      M.biUnion Prod.snd ⊆ boxCube x0 (M.card * (4 * (Nat.ceil C_rca + 1) * (r_0 + 1) * R_cut)) := by
  let D_step := 2 * (Nat.ceil C_rca + 1) * R_cut
  let S_cal := 4 * (Nat.ceil C_rca + 1) * (r_0 + 1) * R_cut
  have h_min : ∀ i : Fin 3, ∃ p ∈ M, ∀ q ∈ M,
      (anchorOfCube p.1 p.2 i).val ≤ (anchorOfCube q.1 q.2 i).val :=
    fun i => Finset.exists_min_image M (fun p => (anchorOfCube p.1 p.2 i).val) hM_ne
  let p_min (i : Fin 3) : ℕ × Finset (Box3D L) := Classical.choose (h_min i)
  let x0 : Box3D L := fun i => anchorOfCube (p_min i).1 (p_min i).2 i
  have h_adj_dist : ∀ (i : Fin 3) (p q : ℕ × Finset (Box3D L)),
      p ∈ M → q ∈ M → KPScaleCubeOverlap sys C_rca p q →
      kpNatDist (anchorOfCube p.1 p.2 i).val (anchorOfCube q.1 q.2 i).val ≤ D_step := by
    intro i p q hp hq h_ov
    rcases mem_kpScaleCubeFinset_iff.mp (hM_sub hp) with ⟨hp_r, _⟩
    rcases mem_kpScaleCubeFinset_iff.mp (hM_sub hq) with ⟨hq_r, _⟩
    have hp_R : p.1 ≤ R_cut := le_trans (Finset.mem_Icc.mp hp_r).2 (Nat.min_le_left R_cut L)
    have hq_R : q.1 ≤ R_cut := le_trans (Finset.mem_Icc.mp hq_r).2 (Nat.min_le_left R_cut L)
    rcases Finset.not_disjoint_iff.mp h_ov.2 with ⟨c, hc_p, hc_q⟩
    have h1 := le_trans (kpNatDist_anchor_kpStaticCSSCheckAnchor_le D_field sys h_sys_supp hc_p i)
      (le_trans (linearExpansionRadius_le_ceil_mul C_rca p.1) (Nat.mul_le_mul_left _ hp_R))
    have h2 := le_trans (kpNatDist_anchor_kpStaticCSSCheckAnchor_le D_field sys h_sys_supp hc_q i)
      (le_trans (linearExpansionRadius_le_ceil_mul C_rca q.1) (Nat.mul_le_mul_left _ hq_R))
    rw [kpNatDist_comm] at h1
    have h_tri := kpNatDist_triangle (anchorOfCube p.1 p.2 i).val (kpStaticCSSCheckAnchor c i).val
      (anchorOfCube q.1 q.2 i).val
    have h_sum : Nat.ceil C_rca * R_cut + Nat.ceil C_rca * R_cut ≤ D_step := by
      dsimp [D_step]; nlinarith
    exact le_trans h_tri (le_trans (Nat.add_le_add h1 h2) h_sum)
  refine ⟨x0, fun v hv => ?_⟩
  rcases Finset.mem_biUnion.mp hv with ⟨q, hq_M, hv_q⟩
  rcases mem_kpScaleCubeFinset_iff.mp (hM_sub hq_M) with ⟨hq_r, hq_A⟩
  have hq_R : q.1 ≤ R_cut := le_trans (Finset.mem_Icc.mp hq_r).2 (Nat.min_le_left R_cut L)
  rw [← boxCube_anchorOfCube hq_A, mem_boxCube] at hv_q
  rw [mem_boxCube]
  intro i
  rcases Classical.choose_spec (h_min i) with ⟨hp_min_M, hp_min_le⟩
  have h_le_anc : (x0 i).val ≤ (anchorOfCube q.1 q.2 i).val := hp_min_le q hq_M
  have h_dist := connectedSubgraph_bound_of_step_le h_conn hp_min_M
    (fun a => kpNatDist (x0 i).val (anchorOfCube a.1 a.2 i).val) D_step
    (kpNatDist_self (x0 i).val)
    (fun u hu w hw huw => le_trans
      (kpNatDist_triangle (x0 i).val (anchorOfCube u.1 u.2 i).val (anchorOfCube w.1 w.2 i).val)
      (Nat.add_le_add_left (h_adj_dist i u w hu hw huw) _))
    q hq_M
  have hv_i := hv_q i
  have hM_pos : 1 ≤ M.card := Finset.card_pos.mpr hM_ne
  have hD_le_S : D_step ≤ S_cal := by
    calc D_step = 1 * D_step := (one_mul D_step).symm
      _ ≤ (2 * (r_0 + 1)) * D_step := Nat.mul_le_mul_right D_step (by omega)
      _ = S_cal := by dsimp [D_step, S_cal]; ring
  have hR_le_D : R_cut ≤ D_step :=
    Nat.le_mul_of_pos_left R_cut (by omega)
  have h_step_mul : (M.card - 1) * D_step + R_cut ≤ M.card * S_cal := by
    have h1 : (M.card - 1) * D_step + R_cut ≤ (M.card - 1) * D_step + D_step :=
      Nat.add_le_add_left hR_le_D _
    have h2 : (M.card - 1) * D_step + D_step = M.card * D_step := by
      cases h_c : M.card with
      | zero => omega
      | succ k => simp [Nat.succ_mul]
    exact le_trans h1 (h2.symm ▸ Nat.mul_le_mul_left M.card hD_le_S)
  change (x0 i).val ≤ (v i).val ∧ (v i).val < (x0 i).val + M.card * S_cal
  dsimp only [kpNatDist] at h_dist
  omega

lemma kpNatDist_anchor_le_of_enclosing_and_collar
    {L q_code r_0 m_max w_0 R_cut : ℕ} [NeZero L]
    (hR_cut : 1 ≤ R_cut)
    (D_field : Box3D L → LocalCSSDescriptor q_code r_0 m_max)
    (sys : IndexedCommutingProjectorHamiltonian 3 L (UniformSite3D L (CodeSlotConfig q_code)) (StaticCSSCheckIdx L q_code m_max))
    (h_sys_supp : ∀ idx, sys.support idx = staticCSSCheckSupport D_field idx)
    {C_rca : ℝ} (hC_rca : 0 ≤ C_rca)
    {n r r_enc : ℕ} {x_enc : Box3D L} {B : Finset (Box3D L)}
    {p₀ : ℕ × Finset (Box3D L)} (hp₀ : p₀ ∈ kpScaleCubeFinset L R_cut)
    {c : StaticCSSCheckIdx L q_code m_max}
    (hr_pos : 1 ≤ r)
    (hr_le : r ≤ n * (4 * (Nat.ceil C_rca + 1) * (r_0 + 1) * R_cut))
    (hrenc_le : r_enc ≤ n * (4 * (Nat.ceil C_rca + 1) * (r_0 + 1) * R_cut))
    (hp₀_sub : p₀.2 ⊆ boxCube x_enc r_enc)
    (hB_cube : B ∈ boxCubes 3 L r)
    (hB_sub : B ⊆ boxCube x_enc r_enc)
    (hc : c ∈ kpRCACollarChecks sys C_rca r B)
    (i : Fin 3) :
    kpNatDist (anchorOfCube p₀.1 p₀.2 i).val (kpStaticCSSCheckAnchor c i).val ≤
      n * kpCollarMaxCheckCard R_cut r_0 w_0 C_rca := by
  let S_cal := 4 * (Nat.ceil C_rca + 1) * (r_0 + 1) * R_cut
  rcases mem_kpScaleCubeFinset_iff.mp hp₀ with ⟨hp₀_r, hp₀_A⟩
  have hp₀_pos : 1 ≤ p₀.1 := (Finset.mem_Icc.mp hp₀_r).1
  have h_anc_p₀ : anchorOfCube p₀.1 p₀.2 ∈ boxCube x_enc r_enc := by
    apply hp₀_sub
    have h_self : anchorOfCube p₀.1 p₀.2 ∈ boxCube (anchorOfCube p₀.1 p₀.2) p₀.1 := by
      rw [mem_boxCube]; intro j; exact ⟨le_refl _, by omega⟩
    rwa [boxCube_anchorOfCube hp₀_A] at h_self
  have h_anc_B : anchorOfCube r B ∈ boxCube x_enc r_enc := by
    apply hB_sub
    have h_self : anchorOfCube r B ∈ boxCube (anchorOfCube r B) r := by
      rw [mem_boxCube]; intro j; exact ⟨le_refl _, by omega⟩
    rwa [boxCube_anchorOfCube hB_cube] at h_self
  rw [mem_boxCube] at h_anc_p₀ h_anc_B
  have h_dist_B : kpNatDist (anchorOfCube p₀.1 p₀.2 i).val (anchorOfCube r B i).val ≤ n * S_cal := by
    have := (h_anc_p₀ i).1; have := (h_anc_p₀ i).2
    have := (h_anc_B i).1; have := (h_anc_B i).2
    change r_enc ≤ n * S_cal at hrenc_le
    unfold kpNatDist; omega
  have h_dist_c : kpNatDist (anchorOfCube r B i).val (kpStaticCSSCheckAnchor c i).val ≤
      Nat.ceil C_rca * (n * S_cal) := by
    rw [kpNatDist_comm]
    exact le_trans (kpNatDist_anchor_kpStaticCSSCheckAnchor_le D_field sys h_sys_supp hc i)
      (le_trans (linearExpansionRadius_le_ceil_mul C_rca r) (Nat.mul_le_mul_left _ hr_le))
  have h_tri := kpNatDist_triangle (anchorOfCube p₀.1 p₀.2 i).val (anchorOfCube r B i).val
    (kpStaticCSSCheckAnchor c i).val
  have h_cal := ceil_add_one_mul_scaleCal_le_kpCollarMaxCheckCard (r_0 := r_0) (w_0 := w_0) hR_cut hC_rca
  calc kpNatDist (anchorOfCube p₀.1 p₀.2 i).val (kpStaticCSSCheckAnchor c i).val
    _ ≤ n * S_cal + Nat.ceil C_rca * (n * S_cal) := le_trans h_tri (Nat.add_le_add h_dist_B h_dist_c)
    _ = n * ((Nat.ceil C_rca + 1) * S_cal) := by ring
    _ ≤ n * kpCollarMaxCheckCard R_cut r_0 w_0 C_rca := Nat.mul_le_mul_left n h_cal

lemma card_kpScaleCubeFinset_anchor_kpNatDist_le
    {L r_0 w_0 R_cut : ℕ} [NeZero L]
    (hR_cut : 1 ≤ R_cut) (C_rca : ℝ) (z : Box3D L)
    {n : ℕ} (hn : 1 ≤ n) :
    (((kpScaleCubeFinset L R_cut).filter (fun p₀ =>
      ∀ i : Fin 3, kpNatDist (anchorOfCube p₀.1 p₀.2 i).val (z i).val ≤
        n * kpCollarMaxCheckCard R_cut r_0 w_0 C_rca)).card : ℝ) ≤
      (Real.exp (6 * (kpCollarMaxCheckCard R_cut r_0 w_0 C_rca : ℝ))) ^ n := by
  let Δ_V := kpCollarMaxCheckCard R_cut r_0 w_0 C_rca
  let R := n * Δ_V
  have h_sub : (kpScaleCubeFinset L R_cut).filter (fun p₀ =>
      ∀ i : Fin 3, kpNatDist (anchorOfCube p₀.1 p₀.2 i).val (z i).val ≤ R) ⊆
      (Finset.Icc 1 (min R_cut L)).biUnion (fun r =>
        ((boxCubes 3 L r).filter (fun A =>
          ∀ i : Fin 3, kpNatDist (anchorOfCube r A i).val (z i).val ≤ R)).image (fun A => (r, A))) := by
    intro p₀ hp₀
    rcases Finset.mem_filter.mp hp₀ with ⟨hp₀_U, hp₀_dist⟩
    rcases mem_kpScaleCubeFinset_iff.mp hp₀_U with ⟨hp₀_r, hp₀_A⟩
    exact Finset.mem_biUnion.mpr ⟨p₀.1, hp₀_r,
      Finset.mem_image.mpr ⟨p₀.2, Finset.mem_filter.mpr ⟨hp₀_A, hp₀_dist⟩, Prod.eta p₀⟩⟩
  have h_Icc : (Finset.Icc 1 (min R_cut L)).card ≤ R_cut := by
    rw [Nat.card_Icc]; have := Nat.min_le_left R_cut L; omega
  have h_nat : ((kpScaleCubeFinset L R_cut).filter (fun p₀ =>
      ∀ i : Fin 3, kpNatDist (anchorOfCube p₀.1 p₀.2 i).val (z i).val ≤ R)).card ≤
      R_cut * (2 * R + 1) ^ 3 := by
    refine le_trans (Finset.card_le_card h_sub) (le_trans Finset.card_biUnion_le ?_)
    refine le_trans (Finset.sum_le_card_nsmul _ _ ((2 * R + 1) ^ 3) fun r _ => ?_) ?_
    · exact le_trans Finset.card_image_le (card_filter_boxCubes_anchor_kpNatDist_le r R z)
    · rw [smul_eq_mul]
      exact Nat.mul_le_mul_right _ h_Icc
  let X : ℝ := (n : ℝ) * (Δ_V : ℝ)
  have hΔ_ge : 27 ≤ Δ_V := by
    have := twenty_seven_mul_succ_le_kpCollarMaxCheckCard (r_0 := r_0) (w_0 := w_0) hR_cut C_rca
    omega
  have hX_ge : 27 ≤ X := by
    dsimp [X]
    have hn_r : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    have hΔ_r : (27 : ℝ) ≤ (Δ_V : ℝ) := by exact_mod_cast hΔ_ge
    nlinarith
  have hR_cut_le_X : (R_cut : ℝ) ≤ X := by
    have hR_le_Δ : R_cut ≤ Δ_V := by
      unfold Δ_V kpCollarMaxCheckCard
      have h_b : R_cut ≤ 2 * (R_cut + 2 * linearExpansionRadius C_rca R_cut + r_0) + 1 := by omega
      have h_p : R_cut ≤ (2 * (R_cut + 2 * linearExpansionRadius C_rca R_cut + r_0) + 1) ^ 3 :=
        le_trans (Nat.le_self_pow (by decide) R_cut) (Nat.pow_le_pow_left h_b 3)
      exact le_trans h_p (le_trans (Nat.le_mul_of_pos_right _ (Nat.succ_pos w_0)) (Nat.le_succ _))
    have hn_r : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    have hR_r : (R_cut : ℝ) ≤ (Δ_V : ℝ) := by exact_mod_cast hR_le_Δ
    dsimp [X]; nlinarith
  have h_R_exp : (R_cut : ℝ) ≤ Real.exp X :=
    le_trans (by linarith) (Real.add_one_le_exp X)
  have h_2X_exp : 2 * X + 1 ≤ Real.exp X := by
    have h_sq : 2 * X + 1 ≤ (X / 2 + 1) ^ 2 := by nlinarith
    have h_half := Real.add_one_le_exp (X / 2)
    have h_pow : (X / 2 + 1) ^ 2 ≤ (Real.exp (X / 2)) ^ 2 :=
      pow_le_pow_left₀ (by linarith) h_half 2
    have h_exp_sq : (Real.exp (X / 2)) ^ 2 = Real.exp X := by
      rw [← Real.exp_nat_mul]; congr 1; ring
    linarith
  have h_pow3 : (2 * X + 1) ^ 3 ≤ Real.exp (3 * X) := by
    calc (2 * X + 1) ^ 3
      _ ≤ (Real.exp X) ^ 3 := pow_le_pow_left₀ (by linarith) h_2X_exp 3
      _ = Real.exp (3 * X) := by rw [← Real.exp_nat_mul]; norm_num
  calc (((kpScaleCubeFinset L R_cut).filter (fun p₀ =>
        ∀ i : Fin 3, kpNatDist (anchorOfCube p₀.1 p₀.2 i).val (z i).val ≤ R)).card : ℝ)
    _ ≤ ((R_cut * (2 * R + 1) ^ 3 : ℕ) : ℝ) := by exact_mod_cast h_nat
    _ = (R_cut : ℝ) * (2 * X + 1) ^ 3 := by dsimp [R, X]; push_cast; ring
    _ ≤ Real.exp X * Real.exp (3 * X) :=
        mul_le_mul h_R_exp h_pow3 (by positivity) (Real.exp_nonneg X)
    _ = Real.exp (4 * X) := by rw [← Real.exp_add]; congr 1; ring
    _ ≤ Real.exp (6 * X) := Real.exp_le_exp.mpr (by linarith)
    _ = (Real.exp (6 * (Δ_V : ℝ))) ^ n := by
        rw [← Real.exp_nat_mul]; congr 1; dsimp [X]; ring

lemma card_kpScaleCubeFinset_le_of_gt_L_star
    {L r_0 w_0 L_star R_cut : ℕ} [NeZero L]
    (hR_cut : 1 ≤ R_cut) {C_rca : ℝ} (hC_rca : 0 ≤ C_rca)
    (hL_star_card : (Fintype.card (Box3D L) : ℝ) ≤ Real.exp (L_star : ℝ))
    {n : ℕ} (hn : 1 ≤ n)
    (h_gt : L_star < n * (4 * (Nat.ceil C_rca + 1) * (r_0 + 1) * R_cut)) :
    ((kpScaleCubeFinset L R_cut).card : ℝ) ≤
      (Real.exp (6 * (kpCollarMaxCheckCard R_cut r_0 w_0 C_rca : ℝ))) ^ n := by
  let Δ_V := kpCollarMaxCheckCard R_cut r_0 w_0 C_rca
  let S_cal := 4 * (Nat.ceil C_rca + 1) * (r_0 + 1) * R_cut
  let X : ℝ := (n : ℝ) * (Δ_V : ℝ)
  have h_cal_le_Δ : S_cal ≤ Δ_V := by
    have h1 : (Nat.ceil C_rca + 1) * S_cal ≤ Δ_V :=
      ceil_add_one_mul_scaleCal_le_kpCollarMaxCheckCard (r_0 := r_0) (w_0 := w_0) hR_cut hC_rca
    exact le_trans (Nat.le_mul_of_pos_left S_cal (Nat.succ_pos _)) h1
  have hL_star_le_X : (L_star : ℝ) ≤ X := by
    have h_nat : L_star ≤ n * Δ_V := le_trans (Nat.le_of_lt h_gt) (Nat.mul_le_mul_left n h_cal_le_Δ)
    dsimp [X]; exact_mod_cast h_nat
  have h_Icc : (Finset.Icc 1 (min R_cut L)).card ≤ R_cut := by
    rw [Nat.card_Icc]; have := Nat.min_le_left R_cut L; omega
  have h_nat : (kpScaleCubeFinset L R_cut).card ≤ R_cut * Fintype.card (Box3D L) := by
    unfold kpScaleCubeFinset
    refine le_trans Finset.card_biUnion_le ?_
    refine le_trans (Finset.sum_le_card_nsmul _ _ (Fintype.card (Box3D L)) fun r _ => ?_) ?_
    · refine le_trans Finset.card_image_le ?_
      unfold boxCubes
      exact le_trans Finset.card_image_le (by simp)
    · rw [smul_eq_mul]
      exact Nat.mul_le_mul_right _ h_Icc
  have hR_le_Δ : R_cut ≤ Δ_V := by
    unfold Δ_V kpCollarMaxCheckCard
    have h_b : R_cut ≤ 2 * (R_cut + 2 * linearExpansionRadius C_rca R_cut + r_0) + 1 := by omega
    have h_p : R_cut ≤ (2 * (R_cut + 2 * linearExpansionRadius C_rca R_cut + r_0) + 1) ^ 3 :=
      le_trans (Nat.le_self_pow (by decide) R_cut) (Nat.pow_le_pow_left h_b 3)
    exact le_trans h_p (le_trans (Nat.le_mul_of_pos_right _ (Nat.succ_pos w_0)) (Nat.le_succ _))
  have hR_le_X : (R_cut : ℝ) ≤ X := by
    have hn_r : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    have hR_r : (R_cut : ℝ) ≤ (Δ_V : ℝ) := by exact_mod_cast hR_le_Δ
    dsimp [X]; nlinarith
  have h_R_exp : (R_cut : ℝ) ≤ Real.exp X :=
    le_trans (by linarith) (Real.add_one_le_exp X)
  have h_L_exp : (Fintype.card (Box3D L) : ℝ) ≤ Real.exp X :=
    le_trans hL_star_card (Real.exp_le_exp.mpr hL_star_le_X)
  have hX_nn : 0 ≤ X := by dsimp [X]; positivity
  calc ((kpScaleCubeFinset L R_cut).card : ℝ)
    _ ≤ ((R_cut * Fintype.card (Box3D L) : ℕ) : ℝ) := by exact_mod_cast h_nat
    _ = (R_cut : ℝ) * (Fintype.card (Box3D L) : ℝ) := by push_cast; ring
    _ ≤ Real.exp X * Real.exp X := mul_le_mul h_R_exp h_L_exp (Nat.cast_nonneg _) (Real.exp_nonneg X)
    _ = Real.exp (2 * X) := by rw [← Real.exp_add]; congr 1; ring
    _ ≤ Real.exp (6 * X) := Real.exp_le_exp.mpr (by linarith)
    _ = (Real.exp (6 * (Δ_V : ℝ))) ^ n := by
        rw [← Real.exp_nat_mul]; congr 1; dsimp [X]; ring

lemma card_activeMonomerSets_of_card_le
    {L q_code r_0 m_max w_0 L_star R_cut : ℕ} [NeZero L]
    (hR_cut : 1 ≤ R_cut)
    (D_field : Box3D L → LocalCSSDescriptor q_code r_0 m_max)
    (sys : IndexedCommutingProjectorHamiltonian 3 L (UniformSite3D L (CodeSlotConfig q_code)) (StaticCSSCheckIdx L q_code m_max))
    (h_sys_checks : ∀ idx, sys.checkProj idx = staticCSSCheckProj D_field idx ∧
      sys.support idx = staticCSSCheckSupport D_field idx ∧ sys.weight idx = 1)
    (h_geom : sys.IsGeometricallyLocal r_0 w_0)
    {C_rca : ℝ} (hC_rca : 0 ≤ C_rca)
    (hL_star_card : (Fintype.card (Box3D L) : ℝ) ≤ Real.exp (L_star : ℝ))
    (z : Box3D L)
    (P_act : Finset (ℕ × Finset (Box3D L)) → Prop) [DecidablePred P_act]
    (hP_act : ∀ M ⊆ kpScaleCubeFinset L R_cut, P_act M →
      KPIsConnectedSubgraph (KPScaleCubeOverlap sys C_rca) M ∧
      (M.card * (4 * (Nat.ceil C_rca + 1) * (r_0 + 1) * R_cut) ≤ L_star →
        ∃ p₀ ∈ M, ∀ i : Fin 3,
          kpNatDist (anchorOfCube p₀.1 p₀.2 i).val (z i).val ≤
            M.card * kpCollarMaxCheckCard R_cut r_0 w_0 C_rca))
    {n : ℕ} (hn : 1 ≤ n) :
    (((kpScaleCubeFinset L R_cut).powerset.filter (fun M => M.card = n ∧ P_act M)).card : ℝ) ≤
      (Real.exp (12 * (kpCollarMaxCheckCard R_cut r_0 w_0 C_rca : ℝ))) ^ n := by
  let U := kpScaleCubeFinset L R_cut
  let Δ_V := kpCollarMaxCheckCard R_cut r_0 w_0 C_rca
  let S_cal := 4 * (Nat.ceil C_rca + 1) * (r_0 + 1) * R_cut
  let E6 := (Real.exp (6 * (Δ_V : ℝ))) ^ n
  have hE6_eq : E6 * E6 = (Real.exp (12 * (Δ_V : ℝ))) ^ n := by
    dsimp [E6]
    rw [← mul_pow, ← Real.exp_add]
    congr 2; ring
  by_cases h_le : n * S_cal ≤ L_star
  · let R_roots := U.filter (fun p₀ =>
      ∀ i : Fin 3, kpNatDist (anchorOfCube p₀.1 p₀.2 i).val (z i).val ≤ n * Δ_V)
    have h_sub : U.powerset.filter (fun M => M.card = n ∧ P_act M) ⊆
        R_roots.biUnion (fun p₀ =>
          U.powerset.filter (fun M => p₀ ∈ M ∧ M.card = n ∧
            KPIsConnectedSubgraph (KPScaleCubeOverlap sys C_rca) M)) := by
      intro M hM
      rcases Finset.mem_filter.mp hM with ⟨hM_pow, hM_card, hM_P⟩
      have hM_sub : M ⊆ U := Finset.mem_powerset.mp hM_pow
      rcases hP_act M hM_sub hM_P with ⟨h_conn, h_root_ex⟩
      rcases h_root_ex (hM_card.symm ▸ h_le) with ⟨p₀, hp₀_M, hp₀_dist⟩
      rw [hM_card] at hp₀_dist
      exact Finset.mem_biUnion.mpr ⟨p₀, Finset.mem_filter.mpr ⟨hM_sub hp₀_M, hp₀_dist⟩,
        Finset.mem_filter.mpr ⟨hM_pow, hp₀_M, hM_card, h_conn⟩⟩
    have h_bi : ((U.powerset.filter (fun M => M.card = n ∧ P_act M)).card : ℝ) ≤
        (R_roots.card : ℝ) * E6 := by
      have h_nat : (U.powerset.filter (fun M => M.card = n ∧ P_act M)).card ≤
          ∑ p₀ ∈ R_roots, (U.powerset.filter (fun M => p₀ ∈ M ∧ M.card = n ∧
            KPIsConnectedSubgraph (KPScaleCubeOverlap sys C_rca) M)).card :=
        le_trans (Finset.card_le_card h_sub) Finset.card_biUnion_le
      calc ((U.powerset.filter (fun M => M.card = n ∧ P_act M)).card : ℝ)
        _ ≤ ∑ p₀ ∈ R_roots, ((U.powerset.filter (fun M => p₀ ∈ M ∧ M.card = n ∧
              KPIsConnectedSubgraph (KPScaleCubeOverlap sys C_rca) M)).card : ℝ) := by
            exact_mod_cast h_nat
        _ ≤ ∑ _p₀ ∈ R_roots, E6 := Finset.sum_le_sum fun p₀ hp₀ =>
            card_connected_kpScaleCubeFinset_of_root_le hR_cut D_field sys h_sys_checks h_geom hC_rca
              (Finset.mem_filter.mp hp₀).1 hn
        _ = (R_roots.card : ℝ) * E6 := by rw [Finset.sum_const, nsmul_eq_mul]
    have h_roots_le : (R_roots.card : ℝ) ≤ E6 :=
      card_kpScaleCubeFinset_anchor_kpNatDist_le hR_cut C_rca z hn
    calc ((U.powerset.filter (fun M => M.card = n ∧ P_act M)).card : ℝ)
      _ ≤ (R_roots.card : ℝ) * E6 := h_bi
      _ ≤ E6 * E6 := mul_le_mul_of_nonneg_right h_roots_le (by dsimp [E6]; positivity)
      _ = (Real.exp (12 * (Δ_V : ℝ))) ^ n := hE6_eq
  · have h_gt : L_star < n * S_cal := Nat.lt_of_not_ge h_le
    have h_sub : U.powerset.filter (fun M => M.card = n ∧ P_act M) ⊆
        U.biUnion (fun p₀ =>
          U.powerset.filter (fun M => p₀ ∈ M ∧ M.card = n ∧
            KPIsConnectedSubgraph (KPScaleCubeOverlap sys C_rca) M)) := by
      intro M hM
      rcases Finset.mem_filter.mp hM with ⟨hM_pow, hM_card, hM_P⟩
      have hM_sub : M ⊆ U := Finset.mem_powerset.mp hM_pow
      have hM_ne : M.Nonempty := Finset.card_pos.mp (by omega)
      rcases hM_ne with ⟨p₀, hp₀_M⟩
      exact Finset.mem_biUnion.mpr ⟨p₀, hM_sub hp₀_M,
        Finset.mem_filter.mpr ⟨hM_pow, hp₀_M, hM_card, (hP_act M hM_sub hM_P).1⟩⟩
    have h_bi : ((U.powerset.filter (fun M => M.card = n ∧ P_act M)).card : ℝ) ≤
        (U.card : ℝ) * E6 := by
      have h_nat : (U.powerset.filter (fun M => M.card = n ∧ P_act M)).card ≤
          ∑ p₀ ∈ U, (U.powerset.filter (fun M => p₀ ∈ M ∧ M.card = n ∧
            KPIsConnectedSubgraph (KPScaleCubeOverlap sys C_rca) M)).card :=
        le_trans (Finset.card_le_card h_sub) Finset.card_biUnion_le
      calc ((U.powerset.filter (fun M => M.card = n ∧ P_act M)).card : ℝ)
        _ ≤ ∑ p₀ ∈ U, ((U.powerset.filter (fun M => p₀ ∈ M ∧ M.card = n ∧
              KPIsConnectedSubgraph (KPScaleCubeOverlap sys C_rca) M)).card : ℝ) := by
            exact_mod_cast h_nat
        _ ≤ ∑ _p₀ ∈ U, E6 := Finset.sum_le_sum fun p₀ hp₀ =>
            card_connected_kpScaleCubeFinset_of_root_le hR_cut D_field sys h_sys_checks h_geom hC_rca hp₀ hn
        _ = (U.card : ℝ) * E6 := by rw [Finset.sum_const, nsmul_eq_mul]
    have h_U_le : (U.card : ℝ) ≤ E6 :=
      card_kpScaleCubeFinset_le_of_gt_L_star hR_cut hC_rca hL_star_card hn h_gt
    calc ((U.powerset.filter (fun M => M.card = n ∧ P_act M)).card : ℝ)
      _ ≤ (U.card : ℝ) * E6 := h_bi
      _ ≤ E6 * E6 := mul_le_mul_of_nonneg_right h_U_le (by dsimp [E6]; positivity)
      _ = (Real.exp (12 * (Δ_V : ℝ))) ^ n := hE6_eq

def kpMonomerWeight {L : ℕ} (c_wl β J : ℝ) (f : ℕ → ℝ) (p : ℕ × Finset (Box3D L)) : ℝ :=
  4 * β * J * f p.1 * Real.exp ((1 / 27 : ℝ) * c_wl * (1 + β) * ((p.1 : ℝ) ^ 3))

lemma kpMonomerWeight_bounds
    {L r_0 w_0 R_cut : ℕ}
    {C_rca C_wl c_wl β J : ℝ} {f : ℕ → ℝ}
    (hR_cut : 1 ≤ R_cut)
    (hf_nn : ∀ r, 0 ≤ f r)
    (hC_wl_cal : (kpCollarMaxCheckCard R_cut r_0 w_0 C_rca : ℝ) ≤ C_wl)
    (hc_wl_cal : (kpCollarMaxCheckCard R_cut r_0 w_0 C_rca : ℝ) ≤ c_wl)
    (hβ : 16 < β) (hJ : 0 ≤ J)
    {p : ℕ × Finset (Box3D L)} (hp : p ∈ kpScaleCubeFinset L R_cut)
    (h_ss : 64 * Real.exp 1 * C_wl * ((p.1 : ℝ) ^ 6) * (β * J * f p.1) *
      Real.exp (c_wl * (1 + β) * ((p.1 : ℝ) ^ 3)) ≤ 1) :
    let Δ_V := (kpCollarMaxCheckCard R_cut r_0 w_0 C_rca : ℝ)
    0 ≤ kpMonomerWeight c_wl β J f p ∧
    4 * Real.exp 1 * Real.exp ((1 / 8 : ℝ) * Δ_V) * kpMonomerWeight c_wl β J f p ≤
      (1 / 64 : ℝ) * Real.exp (-12 * Δ_V) ∧
    kpMonomerWeight c_wl β J f p ≤ 1 ∧
    4 * β * J * f p.1 * Real.exp (4 * β * J * f p.1) ≤ kpMonomerWeight c_wl β J f p := by
  intro Δ_V
  rcases mem_kpScaleCubeFinset_iff.mp hp with ⟨hp_r, _⟩
  have hr_Icc : p.1 ∈ Finset.Icc 1 R_cut :=
    Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp hp_r).1,
      le_trans (Finset.mem_Icc.mp hp_r).2 (Nat.min_le_left R_cut L)⟩
  have hr_ge_one : (1 : ℝ) ≤ (p.1 : ℝ) := by exact_mod_cast (Finset.mem_Icc.mp hr_Icc).1
  have hr3_ge_one : (1 : ℝ) ≤ (p.1 : ℝ) ^ 3 := one_le_pow₀ hr_ge_one
  have hr6_ge_one : (1 : ℝ) ≤ (p.1 : ℝ) ^ 6 := one_le_pow₀ hr_ge_one
  have hΔ_ge : (27 : ℝ) ≤ Δ_V := by
    have h_nat : 27 ≤ kpCollarMaxCheckCard R_cut r_0 w_0 C_rca := by
      have := twenty_seven_mul_succ_le_kpCollarMaxCheckCard (r_0 := r_0) (w_0 := w_0) hR_cut C_rca
      omega
    change (27 : ℝ) ≤ (kpCollarMaxCheckCard R_cut r_0 w_0 C_rca : ℝ)
    exact_mod_cast h_nat
  have hC_wl_ge : 16 ≤ C_wl := by linarith
  have hc_wl_ge : 27 ≤ c_wl := by linarith
  have hw_nn : 0 ≤ kpMonomerWeight c_wl β J f p := by
    unfold kpMonomerWeight
    have := hf_nn p.1
    positivity
  have h_exp_le :
      Real.exp ((12 + 1 / 8 : ℝ) * Δ_V + (1 / 27 : ℝ) * c_wl * (1 + β) * ((p.1 : ℝ) ^ 3)) ≤
        Real.exp (c_wl * (1 + β) * ((p.1 : ℝ) ^ 3)) := by
    apply Real.exp_le_exp.mpr
    have h_Δ_r3 : Δ_V ≤ c_wl * ((p.1 : ℝ) ^ 3) := by nlinarith
    nlinarith
  have h_pref_le :
      1024 * Real.exp 1 * (β * J * f p.1) ≤
        64 * Real.exp 1 * C_wl * ((p.1 : ℝ) ^ 6) * (β * J * f p.1) := by
    have h_jf_nn : 0 ≤ Real.exp 1 * (β * J * f p.1) := by
      have := hf_nn p.1; have := Real.exp_pos 1; positivity
    have h_16 : (1024 : ℝ) ≤ 64 * C_wl * ((p.1 : ℝ) ^ 6) := by nlinarith
    nlinarith
  have h_prod_le_one :
      1024 * Real.exp 1 * (β * J * f p.1) *
        Real.exp ((12 + 1 / 8 : ℝ) * Δ_V + (1 / 27 : ℝ) * c_wl * (1 + β) * ((p.1 : ℝ) ^ 3)) ≤ 1 := by
    refine le_trans (mul_le_mul h_pref_le h_exp_le (le_of_lt (Real.exp_pos _)) ?_) h_ss
    have := hf_nn p.1; have := Real.exp_pos 1; positivity
  have h_main :
      4 * Real.exp 1 * Real.exp ((1 / 8 : ℝ) * Δ_V) * kpMonomerWeight c_wl β J f p ≤
        (1 / 64 : ℝ) * Real.exp (-12 * Δ_V) := by
    have h_mul := mul_le_mul_of_nonneg_right h_prod_le_one
      (by positivity : 0 ≤ (1 / 64 : ℝ) * Real.exp (-12 * Δ_V))
    have h_lhs_eq :
        1024 * Real.exp 1 * (β * J * f p.1) *
          Real.exp ((12 + 1 / 8 : ℝ) * Δ_V + (1 / 27 : ℝ) * c_wl * (1 + β) * ((p.1 : ℝ) ^ 3)) *
          ((1 / 64 : ℝ) * Real.exp (-12 * Δ_V)) =
        4 * Real.exp 1 * Real.exp ((1 / 8 : ℝ) * Δ_V) * kpMonomerWeight c_wl β J f p := by
      unfold kpMonomerWeight
      have h_e :
          Real.exp ((12 + 1 / 8 : ℝ) * Δ_V + (1 / 27 : ℝ) * c_wl * (1 + β) * ((p.1 : ℝ) ^ 3)) *
            Real.exp (-12 * Δ_V) =
          Real.exp ((1 / 8 : ℝ) * Δ_V) *
            Real.exp ((1 / 27 : ℝ) * c_wl * (1 + β) * ((p.1 : ℝ) ^ 3)) := by
        rw [← Real.exp_add, ← Real.exp_add]
        congr 1; ring
      calc 1024 * Real.exp 1 * (β * J * f p.1) *
            Real.exp ((12 + 1 / 8 : ℝ) * Δ_V + (1 / 27 : ℝ) * c_wl * (1 + β) * ((p.1 : ℝ) ^ 3)) *
            ((1 / 64 : ℝ) * Real.exp (-12 * Δ_V))
        _ = (16 * Real.exp 1 * β * J * f p.1) *
              (Real.exp ((12 + 1 / 8 : ℝ) * Δ_V + (1 / 27 : ℝ) * c_wl * (1 + β) * ((p.1 : ℝ) ^ 3)) *
                Real.exp (-12 * Δ_V)) := by ring
        _ = (16 * Real.exp 1 * β * J * f p.1) *
              (Real.exp ((1 / 8 : ℝ) * Δ_V) *
                Real.exp ((1 / 27 : ℝ) * c_wl * (1 + β) * ((p.1 : ℝ) ^ 3))) := by rw [h_e]
        _ = 4 * Real.exp 1 * Real.exp ((1 / 8 : ℝ) * Δ_V) *
              (4 * β * J * f p.1 * Real.exp ((1 / 27 : ℝ) * c_wl * (1 + β) * ((p.1 : ℝ) ^ 3))) := by ring
    rw [h_lhs_eq, one_mul] at h_mul
    exact h_mul
  have hw_le_one : kpMonomerWeight c_wl β J f p ≤ 1 := by
    have h_e1 : 1 ≤ Real.exp 1 := Real.one_le_exp zero_le_one
    have h_e8 : 1 ≤ Real.exp ((1 / 8 : ℝ) * Δ_V) := Real.one_le_exp (by linarith)
    have h_em : Real.exp (-12 * Δ_V) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
    have h_ge4 : 4 * kpMonomerWeight c_wl β J f p ≤
        4 * Real.exp 1 * Real.exp ((1 / 8 : ℝ) * Δ_V) * kpMonomerWeight c_wl β J f p := by
      have : 1 ≤ Real.exp 1 * Real.exp ((1 / 8 : ℝ) * Δ_V) := by nlinarith
      nlinarith
    linarith
  have h_mayer_le : 4 * β * J * f p.1 * Real.exp (4 * β * J * f p.1) ≤ kpMonomerWeight c_wl β J f p := by
    unfold kpMonomerWeight
    have h_exp_ge_one : 1 ≤ Real.exp ((1 / 27 : ℝ) * c_wl * (1 + β) * ((p.1 : ℝ) ^ 3)) :=
      Real.one_le_exp (by positivity)
    have h_4bjf_le_one : 4 * β * J * f p.1 ≤ 1 := by
      unfold kpMonomerWeight at hw_le_one
      have : 0 ≤ 4 * β * J * f p.1 := by have := hf_nn p.1; positivity
      nlinarith
    have h_c_r3 : (27 : ℝ) ≤ c_wl * ((p.1 : ℝ) ^ 3) := by nlinarith
    have h_one_le_arg : 1 ≤ (1 / 27 : ℝ) * c_wl * (1 + β) * ((p.1 : ℝ) ^ 3) := by nlinarith
    refine mul_le_mul_of_nonneg_left
      (Real.exp_le_exp.mpr (le_trans h_4bjf_le_one h_one_le_arg))
      (by have := hf_nn p.1; positivity)
  exact ⟨hw_nn, h_main, hw_le_one, h_mayer_le⟩

lemma two_pow_cubeIntersectingChecks_mul_le_kpMonomerWeight
    {L q_code r_0 m_max w_0 R_cut : ℕ} [NeZero L]
    {C_rca c_wl β J : ℝ} {f : ℕ → ℝ}
    (hR_cut : 1 ≤ R_cut) (hβ : 0 ≤ β) (hJ : 0 ≤ J) (hf_nn : ∀ r, 0 ≤ f r)
    (sys : IndexedCommutingProjectorHamiltonian 3 L (UniformSite3D L (CodeSlotConfig q_code)) (StaticCSSCheckIdx L q_code m_max))
    (h_geom : sys.IsGeometricallyLocal r_0 w_0)
    (hc_wl_cal : (kpCollarMaxCheckCard R_cut r_0 w_0 C_rca : ℝ) ≤ c_wl)
    {p : ℕ × Finset (Box3D L)} (hp : p ∈ kpScaleCubeFinset L R_cut)
    {N : ℕ} (hN : N ≤ 2 ^ (cubeIntersectingChecks sys p.2).card) :
    (N : ℝ) *
      (2 * β * J * f p.1 * Real.exp ((1 / 27 : ℝ) * c_wl * β * ((p.1 : ℝ) ^ 3))) ≤
      kpMonomerWeight c_wl β J f p := by
  rcases mem_kpScaleCubeFinset_iff.mp hp with ⟨hr, hA⟩
  have h_c := card_cubeIntersectingChecks_cast_le_div_twenty_seven hR_cut sys h_geom hc_wl_cal hr hA
  have h2_le_exp1 : (2 : ℝ) ≤ Real.exp 1 := by have := Real.add_one_le_exp (1 : ℝ); linarith
  have h_pow_exp : ((2 ^ (cubeIntersectingChecks sys p.2).card : ℕ) : ℝ) ≤
      Real.exp ((1 / 27 : ℝ) * c_wl * ((p.1 : ℝ) ^ 3)) := by
    push_cast
    calc (2 : ℝ) ^ (cubeIntersectingChecks sys p.2).card
      _ ≤ (Real.exp 1) ^ (cubeIntersectingChecks sys p.2).card := pow_le_pow_left₀ (by positivity) h2_le_exp1 _
      _ = Real.exp ((cubeIntersectingChecks sys p.2).card : ℝ) := by rw [← Real.exp_nat_mul, mul_one]
      _ ≤ Real.exp ((1 / 27 : ℝ) * c_wl * ((p.1 : ℝ) ^ 3)) := Real.exp_le_exp.mpr h_c
  have h_card_exp : (N : ℝ) ≤ Real.exp ((1 / 27 : ℝ) * c_wl * ((p.1 : ℝ) ^ 3)) :=
    le_trans (by exact_mod_cast hN) h_pow_exp
  have hf_p := hf_nn p.1
  calc (N : ℝ) *
        (2 * β * J * f p.1 * Real.exp ((1 / 27 : ℝ) * c_wl * β * ((p.1 : ℝ) ^ 3)))
    _ ≤ Real.exp ((1 / 27 : ℝ) * c_wl * ((p.1 : ℝ) ^ 3)) *
        (2 * β * J * f p.1 * Real.exp ((1 / 27 : ℝ) * c_wl * β * ((p.1 : ℝ) ^ 3))) :=
        mul_le_mul_of_nonneg_right h_card_exp (by positivity)
    _ = 2 * β * J * f p.1 * (Real.exp ((1 / 27 : ℝ) * c_wl * ((p.1 : ℝ) ^ 3)) *
          Real.exp ((1 / 27 : ℝ) * c_wl * β * ((p.1 : ℝ) ^ 3))) := by ring
    _ = 2 * β * J * f p.1 * Real.exp ((1 / 27 : ℝ) * c_wl * (1 + β) * ((p.1 : ℝ) ^ 3)) := by
        rw [← Real.exp_add]; congr 1; ring
    _ ≤ kpMonomerWeight c_wl β J f p := by
        unfold kpMonomerWeight
        have : 0 ≤ β * J * f p.1 * Real.exp ((1 / 27 : ℝ) * c_wl * (1 + β) * ((p.1 : ℝ) ^ 3)) := by positivity
        linarith

end SpacetimeWorldlineKP
end
