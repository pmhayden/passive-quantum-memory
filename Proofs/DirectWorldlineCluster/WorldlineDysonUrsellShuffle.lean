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

import Proofs.DirectWorldlineCluster.WorldlineDysonUrsellDuhamel

/-!
# Ordered Dyson Simplex Shuffle Factorization and Connected Monomer Components

Constructs the multi-polymer jump-list shuffle combinatorics (`multiPolymerShuffleFinset`) and proves Fubini factorization of ordered Dyson simplex integrals over shuffles of compatible polymers (`multiPolymer_shuffle_simplex_integral_factorization_of_compatible`). Also decomposes arbitrary valid jump lists into connected monomer components (`MonomerStepRel`, `monomerComponents`, `componentPolymer_monomers_and_valid`).

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

/-- Finite set of all order-preserving shuffle interleavings of the component jump lists `γ.1` of a multi-polymer tuple `K = (γ_1, ..., γ_p)` (Part II, Section 3.5 (`subsec:worldline-expansion`), Lemma 3.9 (`lem:worldline-factorization-time-reversal`)). -/
def multiPolymerShuffleFinset
    {L q_code r_0 m_max : ℕ}
    (D_field : Box3D L → LocalCSSDescriptor q_code r_0 m_max)
    (R_cut : ℕ) (K : WorldlineUrsellCluster L q_code) :
    Finset (List (WorldlineJumpMonomer L q_code)) :=
  let M := (K.map (fun γ => γ.1.length)).sum
  (worldlineJumpListFinsetOfLength D_field R_cut M).filter (fun ξ_list =>
    ∃ (owner : Fin M → Fin K.length) (idx : ∀ j : Fin M, Fin (K.get (owner j)).1.length),
      (∀ j₁ j₂ : Fin M, j₁ < j₂ → ∀ h_eq : owner j₁ = owner j₂,
        (idx j₁).1 < (idx j₂).1) ∧
      (∀ a : Fin K.length, ∀ i : Fin (K.get a).1.length,
        ∃ j : Fin M, ∃ h_eq : owner j = a, (idx j).1 = i.1) ∧
      (∀ j : Fin M, ξ_list.getD j.1 default = (K.get (owner j)).1.get (idx j)))

private lemma length_eq_of_mem_worldlineJumpListFinsetOfLength
    {L q_code r_0 m_max : ℕ}
    (D_field : Box3D L → LocalCSSDescriptor q_code r_0 m_max)
    (R_cut M : ℕ) {ξ_list : List (WorldlineJumpMonomer L q_code)}
    (h : ξ_list ∈ worldlineJumpListFinsetOfLength D_field R_cut M) :
    ξ_list.length = M := by
  unfold worldlineJumpListFinsetOfLength at h
  rcases Finset.mem_image.mp h with ⟨g, _, rfl⟩
  exact List.length_ofFn

private lemma list_prod_neg_one_pow_length
    {L q_code : ℕ} (K : WorldlineUrsellCluster L q_code) :
    ((-1 : ℝ) ^ (K.map (fun γ => γ.1.length)).sum) =
      (K.map (fun γ => (-1 : ℝ) ^ γ.1.length)).prod := by
  induction K with
  | nil => simp
  | cons hd tl ih =>
    simp only [List.map_cons, List.sum_cons, List.prod_cons, pow_add, ih]

private def rankOfOwner {M : ℕ} {α : Type*} [DecidableEq α]
    (owner : Fin M → α) (j : Fin M) : ℕ :=
  (Finset.univ.filter (fun j' : Fin M => j' < j ∧ owner j' = owner j)).card

private lemma rankOfOwner_strictMono_on_fiber {M : ℕ} {α : Type*} [DecidableEq α]
    (owner : Fin M → α) {j₁ j₂ : Fin M} (h_lt : j₁ < j₂) (h_eq : owner j₁ = owner j₂) :
    rankOfOwner owner j₁ < rankOfOwner owner j₂ := by
  unfold rankOfOwner
  refine Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr ⟨fun j' hj' => ?_, ?_⟩)
  · rcases Finset.mem_filter.mp hj' with ⟨_, hj'_lt, hj'_eq⟩
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, lt_trans hj'_lt h_lt, hj'_eq.trans h_eq⟩
  · intro h_set_eq
    have hj₁_in : j₁ ∈ Finset.univ.filter (fun j' : Fin M => j' < j₂ ∧ owner j' = owner j₂) :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, h_lt, h_eq⟩
    rw [← h_set_eq] at hj₁_in
    exact (lt_irrefl j₁ (Finset.mem_filter.mp hj₁_in).2.1).elim

private lemma rankOfOwner_lt_card_fiber {M : ℕ} {α : Type*} [DecidableEq α]
    (owner : Fin M → α) (j : Fin M) :
    rankOfOwner owner j < (Finset.univ.filter (fun j' : Fin M => owner j' = owner j)).card := by
  unfold rankOfOwner
  refine Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr ⟨fun j' hj' => ?_, ?_⟩)
  · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hj').2.2⟩
  · intro h_set_eq
    have hj_in : j ∈ Finset.univ.filter (fun j' : Fin M => owner j' = owner j) :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, rfl⟩
    rw [← h_set_eq] at hj_in
    exact (lt_irrefl j (Finset.mem_filter.mp hj_in).2.1).elim

private lemma strictMono_fin_eq_id {m : ℕ} (f : Fin m → Fin m) (hf : StrictMono f) :
    ∀ i : Fin m, f i = i := by
  have h_inj : Function.Injective f := hf.injective
  have h_bij : Function.Bijective f := (Fintype.bijective_iff_injective_and_card f).mpr ⟨h_inj, rfl⟩
  have h_ge : ∀ n : ℕ, ∀ hn : n < m, n ≤ (f ⟨n, hn⟩).1 := by
    intro n
    induction n with
    | zero => intro _; exact Nat.zero_le _
    | succ k ih =>
      intro hk
      have hk' : k < m := Nat.lt_of_succ_lt hk
      have h_lt : (f ⟨k, hk'⟩).1 < (f ⟨k + 1, hk⟩).1 := hf (Nat.lt_succ_self k)
      have h_ih := ih hk'
      omega
  have h_le : ∀ i : Fin m, (f i).1 ≤ i.1 := by
    intro i
    by_contra! h_gt
    let S_gt := Finset.univ.filter (fun x : Fin m => i.1 < x.1)
    let T_gt := Finset.univ.filter (fun x : Fin m => i.1 < (f x).1)
    have h_sub : S_gt ⊂ T_gt := by
      refine Finset.ssubset_iff_subset_ne.mpr ⟨fun x hx => ?_, ?_⟩
      · have hx_lt : i < x := (Finset.mem_filter.mp hx).2
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, lt_trans h_gt (hf hx_lt)⟩
      · intro h_eq
        have hi_in : i ∈ T_gt := Finset.mem_filter.mpr ⟨Finset.mem_univ _, h_gt⟩
        rw [← h_eq] at hi_in
        exact lt_irrefl i.1 (Finset.mem_filter.mp hi_in).2
    have h_card_lt : S_gt.card < T_gt.card := Finset.card_lt_card h_sub
    have h_card_eq : T_gt.card = S_gt.card := by
      refine Finset.card_bij (fun x _ => f x)
        (fun x hx => Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hx).2⟩)
        (fun x₁ _ x₂ _ h => h_inj h)
        (fun y hy => by
          rcases h_bij.2 y with ⟨x, rfl⟩
          exact ⟨x, Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hy).2⟩, rfl⟩)
    omega
  intro i
  exact Fin.ext (le_antisymm (h_le i) (h_ge i.1 i.2))

private lemma rankOfOwner_surj_and_unique {M m : ℕ} {α : Type*} [DecidableEq α]
    (owner : Fin M → α) (a : α) :
    (Finset.univ.filter (fun j : Fin M => owner j = a)).card = m →
      ∀ i : Fin m, ∃ j : Fin M, owner j = a ∧ rankOfOwner owner j = i.1 := by
  intro h_card i
  let S := Finset.univ.filter (fun j : Fin M => owner j = a)
  let r_map : S → Fin m := fun j =>
    ⟨rankOfOwner owner j.1, by
      have h_lt := rankOfOwner_lt_card_fiber owner j.1
      have hj_eq : owner j.1 = a := (Finset.mem_filter.mp j.2).2
      rwa [hj_eq, h_card] at h_lt⟩
  have hr_inj : Function.Injective r_map := by
    intro j₁ j₂ h_eq
    by_contra h_ne
    have h_val_ne : j₁.1 ≠ j₂.1 := fun h => h_ne (Subtype.ext h)
    have h_own : owner j₁.1 = owner j₂.1 :=
      (Finset.mem_filter.mp j₁.2).2.trans (Finset.mem_filter.mp j₂.2).2.symm
    rcases lt_or_gt_of_ne h_val_ne with h_lt | h_gt
    · exact ne_of_lt (rankOfOwner_strictMono_on_fiber owner h_lt h_own) (congrArg Fin.val h_eq)
    · exact ne_of_gt (rankOfOwner_strictMono_on_fiber owner h_gt h_own.symm) (congrArg Fin.val h_eq)
  have hS_card : Fintype.card S = Fintype.card (Fin m) := by
    rw [Fintype.card_coe, h_card, Fintype.card_fin]
  have hr_bij : Function.Bijective r_map :=
    (Fintype.bijective_iff_injective_and_card r_map).mpr ⟨hr_inj, hS_card⟩
  rcases hr_bij.2 i with ⟨⟨j, hj⟩, hj_eq⟩
  exact ⟨j, (Finset.mem_filter.mp hj).2, congrArg Fin.val hj_eq⟩

private lemma idx_eq_rankOfOwner_and_card_fiber
    {L q_code : ℕ} (K : WorldlineUrsellCluster L q_code)
    (owner : Fin (K.map (fun γ => γ.1.length)).sum → Fin K.length)
    (idx : ∀ j : Fin (K.map (fun γ => γ.1.length)).sum, Fin (K.get (owner j)).1.length)
    (h_mono : ∀ j₁ j₂ : Fin (K.map (fun γ => γ.1.length)).sum, j₁ < j₂ →
      ∀ h_eq : owner j₁ = owner j₂, (idx j₁).1 < (idx j₂).1)
    (h_surj : ∀ a : Fin K.length, ∀ i : Fin (K.get a).1.length,
      ∃ j : Fin (K.map (fun γ => γ.1.length)).sum, ∃ h_eq : owner j = a, (idx j).1 = i.1) :
    (∀ a : Fin K.length,
      (Finset.univ.filter (fun j => owner j = a)).card = (K.get a).1.length) ∧
    (∀ j : Fin (K.map (fun γ => γ.1.length)).sum, (idx j).1 = rankOfOwner owner j) := by
  have h_card : ∀ a : Fin K.length,
      (Finset.univ.filter (fun j => owner j = a)).card = (K.get a).1.length := by
    intro a
    let S := Finset.univ.filter (fun j => owner j = a)
    let f : S → Fin (K.get a).1.length := fun j =>
      ⟨(idx j.1).1, by
        have hj_eq : owner j.1 = a := (Finset.mem_filter.mp j.2).2
        rw [← hj_eq]
        exact (idx j.1).2⟩
    have hf_inj : Function.Injective f := by
      intro j₁ j₂ h_eq
      by_contra h_ne
      have h_val_ne : j₁.1 ≠ j₂.1 := fun h => h_ne (Subtype.ext h)
      have h_own : owner j₁.1 = owner j₂.1 :=
        (Finset.mem_filter.mp j₁.2).2.trans (Finset.mem_filter.mp j₂.2).2.symm
      rcases lt_or_gt_of_ne h_val_ne with h_lt | h_gt
      · exact ne_of_lt (h_mono j₁.1 j₂.1 h_lt h_own) (congrArg Fin.val h_eq)
      · exact ne_of_gt (h_mono j₂.1 j₁.1 h_gt h_own.symm) (congrArg Fin.val h_eq)
    have hf_surj : Function.Surjective f := by
      intro i
      rcases h_surj a i with ⟨j, hj_own, hj_idx⟩
      exact ⟨⟨j, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hj_own⟩⟩, Fin.ext hj_idx⟩
    have h_bij : Function.Bijective f := ⟨hf_inj, hf_surj⟩
    have h_fintype := Fintype.card_of_bijective h_bij
    rwa [Fintype.card_coe, Fintype.card_fin] at h_fintype
  refine ⟨h_card, fun j => ?_⟩
  let a := owner j
  have h_ca := h_card a
  let g : Fin (K.get a).1.length → Fin (K.get a).1.length := fun i =>
    let h_ex := rankOfOwner_surj_and_unique owner a h_ca i
    let j_i := Classical.choose h_ex
    have hj_i : owner j_i = a ∧ rankOfOwner owner j_i = i.1 := Classical.choose_spec h_ex
    ⟨(idx j_i).1, by rw [← hj_i.1]; exact (idx j_i).2⟩
  have hg_mono : StrictMono g := by
    intro i₁ i₂ h_lt
    dsimp [g]
    let j₁ := Classical.choose (rankOfOwner_surj_and_unique owner a h_ca i₁)
    let j₂ := Classical.choose (rankOfOwner_surj_and_unique owner a h_ca i₂)
    have hj₁ : owner j₁ = a ∧ rankOfOwner owner j₁ = i₁.1 :=
      Classical.choose_spec (rankOfOwner_surj_and_unique owner a h_ca i₁)
    have hj₂ : owner j₂ = a ∧ rankOfOwner owner j₂ = i₂.1 :=
      Classical.choose_spec (rankOfOwner_surj_and_unique owner a h_ca i₂)
    have hj_lt : j₁ < j₂ := by
      by_contra! h_ge
      rcases eq_or_lt_of_le h_ge with h_eq | h_gt
      · have : i₁.1 = i₂.1 := hj₁.2.symm.trans (by rw [← h_eq]; exact hj₂.2)
        exact ne_of_lt h_lt (Fin.ext this)
      · have h_r := rankOfOwner_strictMono_on_fiber owner h_gt (hj₂.1.trans hj₁.1.symm)
        rw [hj₂.2, hj₁.2] at h_r
        exact not_lt_of_gt h_lt h_r
    exact h_mono j₁ j₂ hj_lt (hj₁.1.trans hj₂.1.symm)
  let i_j : Fin (K.get a).1.length :=
    ⟨rankOfOwner owner j, by
      have h_lt := rankOfOwner_lt_card_fiber owner j
      rwa [h_ca] at h_lt⟩
  have hg_id := strictMono_fin_eq_id g hg_mono i_j
  let j' := Classical.choose (rankOfOwner_surj_and_unique owner a h_ca i_j)
  have hj' : owner j' = a ∧ rankOfOwner owner j' = rankOfOwner owner j :=
    Classical.choose_spec (rankOfOwner_surj_and_unique owner a h_ca i_j)
  have hj'_eq : j' = j := by
    by_contra h_ne
    rcases lt_or_gt_of_ne h_ne with h_lt | h_gt
    · exact ne_of_lt (rankOfOwner_strictMono_on_fiber owner h_lt hj'.1) hj'.2
    · exact ne_of_gt (rankOfOwner_strictMono_on_fiber owner h_gt hj'.1.symm) hj'.2
  have h_val : (idx j').1 = rankOfOwner owner j := congrArg Fin.val hg_id
  rwa [hj'_eq] at h_val

private abbrev clusterTotalJumpLength {L q_code : ℕ} (K : WorldlineUrsellCluster L q_code) : ℕ :=
  (K.map (fun γ => γ.1.length)).sum

private def validShuffleOwnerFinset {L q_code : ℕ} (K : WorldlineUrsellCluster L q_code) :
    Finset (Fin (clusterTotalJumpLength K) → Fin K.length) :=
  Finset.univ.filter (fun owner =>
    ∀ a : Fin K.length,
      (Finset.univ.filter (fun j => owner j = a)).card = (K.get a).1.length)

private def shuffleListOfOwner {L q_code : ℕ} (K : WorldlineUrsellCluster L q_code)
    (owner : Fin (clusterTotalJumpLength K) → Fin K.length) :
    List (WorldlineJumpMonomer L q_code) :=
  List.ofFn (fun j => (K.get (owner j)).1.getD (rankOfOwner owner j) default)

private lemma length_shuffleListOfOwner {L q_code : ℕ} (K : WorldlineUrsellCluster L q_code)
    (owner : Fin (clusterTotalJumpLength K) → Fin K.length) :
    (shuffleListOfOwner K owner).length = clusterTotalJumpLength K :=
  List.length_ofFn

private def shufflePosOfOwner {L q_code : ℕ} {K : WorldlineUrsellCluster L q_code}
    {owner : Fin (clusterTotalJumpLength K) → Fin K.length}
    (h_own : owner ∈ validShuffleOwnerFinset K)
    (a : Fin K.length) (i : Fin (K.get a).1.length) :
    Fin (clusterTotalJumpLength K) :=
  Classical.choose (rankOfOwner_surj_and_unique owner a ((Finset.mem_filter.mp h_own).2 a) i)

private lemma shufflePosOfOwner_spec {L q_code : ℕ} {K : WorldlineUrsellCluster L q_code}
    {owner : Fin (clusterTotalJumpLength K) → Fin K.length}
    (h_own : owner ∈ validShuffleOwnerFinset K) :
    (∀ a : Fin K.length, ∀ i : Fin (K.get a).1.length,
      owner (shufflePosOfOwner h_own a i) = a ∧
      rankOfOwner owner (shufflePosOfOwner h_own a i) = i.1) ∧
    (∀ a : Fin K.length, StrictMono (shufflePosOfOwner h_own a)) ∧
    Function.Bijective (fun p : Σ a : Fin K.length, Fin (K.get a).1.length =>
      shufflePosOfOwner h_own p.1 p.2) := by
  have h_spec : ∀ a : Fin K.length, ∀ i : Fin (K.get a).1.length,
      owner (shufflePosOfOwner h_own a i) = a ∧
      rankOfOwner owner (shufflePosOfOwner h_own a i) = i.1 :=
    fun a i => Classical.choose_spec
      (rankOfOwner_surj_and_unique owner a ((Finset.mem_filter.mp h_own).2 a) i)
  have h_mono : ∀ a : Fin K.length, StrictMono (shufflePosOfOwner h_own a) := by
    intro a i₁ i₂ h_lt
    by_contra! h_ge
    rcases eq_or_lt_of_le h_ge with h_eq | h_gt
    · have : i₁.1 = i₂.1 := (h_spec a i₁).2.symm.trans (by rw [← h_eq]; exact (h_spec a i₂).2)
      exact ne_of_lt h_lt (Fin.ext this)
    · have h_r := rankOfOwner_strictMono_on_fiber owner h_gt
        ((h_spec a i₂).1.trans (h_spec a i₁).1.symm)
      rw [(h_spec a i₂).2, (h_spec a i₁).2] at h_r
      exact not_lt_of_gt h_lt h_r
  refine ⟨h_spec, h_mono, ⟨?_, ?_⟩⟩
  · rintro ⟨a₁, i₁⟩ ⟨a₂, i₂⟩ h_eq
    (try dsimp only at h_eq)
    have ha : a₁ = a₂ := (h_spec a₁ i₁).1.symm.trans (by rw [h_eq]; exact (h_spec a₂ i₂).1)
    subst ha
    exact Sigma.ext rfl (heq_of_eq ((h_mono a₁).injective h_eq))
  · intro j
    let a := owner j
    have h_lt : rankOfOwner owner j < (K.get a).1.length := by
      have h1 := rankOfOwner_lt_card_fiber owner j
      rwa [(Finset.mem_filter.mp h_own).2 a] at h1
    let i : Fin (K.get a).1.length := ⟨rankOfOwner owner j, h_lt⟩
    refine ⟨⟨a, i⟩, ?_⟩
    (try dsimp only)
    let j' := shufflePosOfOwner h_own a i
    have hj' := h_spec a i
    by_contra h_ne
    rcases lt_or_gt_of_ne h_ne with h_lt' | h_gt'
    · exact ne_of_lt (rankOfOwner_strictMono_on_fiber owner h_lt' hj'.1) hj'.2
    · exact ne_of_gt (rankOfOwner_strictMono_on_fiber owner h_gt' hj'.1.symm) hj'.2

private lemma boolToZMod2_foldr_syndromeXor {α : Type*} {L q_code m_max : ℕ}
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

private lemma list_sum_map_finRange_filter {n : ℕ} {M : Type*} [AddCommMonoid M]
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

private lemma worldlineTrajectorySyndrome_shuffleListOfOwner_eq
    {L q_code r_0 m_max : ℕ}
    (D_field : Box3D L → LocalCSSDescriptor q_code r_0 m_max)
    (K : WorldlineUrsellCluster L q_code)
    {owner : Fin (clusterTotalJumpLength K) → Fin K.length}
    (h_own : owner ∈ validShuffleOwnerFinset K)
    (σ : IdxCSS[L, q_code, m_max] → Bool)
    (τ : Fin (clusterTotalJumpLength K) → ℝ) (t : ℝ) :
    worldlineTrajectorySyndrome D_field (shuffleListOfOwner K owner) σ
        (fun j => τ (Fin.cast (length_shuffleListOfOwner K owner) j)) t =
      (List.finRange K.length).foldr
        (fun a acc =>
          syndromeXor
            (worldlineTrajectorySyndrome D_field (K.get a).1 (fun _ => false)
              (fun i => τ (shufflePosOfOwner h_own a i)) t)
            acc)
        σ := by
  have h_inj : Function.Injective boolToZMod2 := by
    intro b₁ b₂; cases b₁ <;> cases b₂ <;> decide
  rcases shufflePosOfOwner_spec h_own with ⟨h_spec, _, h_bij⟩
  ext c
  apply h_inj
  unfold worldlineTrajectorySyndrome
  rw [boolToZMod2_foldr_syndromeXor, list_sum_map_finRange_filter,
    boolToZMod2_foldr_syndromeXor]
  congr 1
  have h_rhs :
      (((List.finRange K.length).map (fun a =>
        boolToZMod2
          ((((List.finRange (K.get a).1.length).filter
            (fun i => decide (τ (shufflePosOfOwner h_own a i) ≤ t))).foldr
            (fun i acc =>
              syndromeXor (staticCSSPauliFlip D_field ((K.get a).1.get i).2.1 ((K.get a).1.get i).2.2) acc)
            (fun _ => false)) c))).sum) =
      ∑ p : Σ a : Fin K.length, Fin (K.get a).1.length,
        if decide (τ (shufflePosOfOwner h_own p.1 p.2) ≤ t) then
          boolToZMod2
            (staticCSSPauliFlip D_field ((K.get p.1).1.get p.2).2.1 ((K.get p.1).1.get p.2).2.2 c)
        else 0 := by
    rw [← Fin.sum_univ_def, Fintype.sum_sigma]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [boolToZMod2_foldr_syndromeXor, list_sum_map_finRange_filter]
    change _ + (0 : ZMod 2) = _
    rw [add_zero]
  rw [h_rhs]
  let e_len : Fin (shuffleListOfOwner K owner).length ≃ Fin (clusterTotalJumpLength K) :=
    finCongr (length_shuffleListOfOwner K owner)
  rw [← Equiv.sum_comp e_len.symm]
  symm
  refine Fintype.sum_bijective (fun p => shufflePosOfOwner h_own p.1 p.2) h_bij _ _ (fun p => ?_)
  rcases p with ⟨a, i⟩
  dsimp only [e_len, shuffleListOfOwner, finCongr_symm, finCongr_apply, Fin.cast_cast,
    Fin.cast_eq_self]
  let j := shufflePosOfOwner h_own a i
  have hj_own : owner j = a := (h_spec a i).1
  have hj_rank : rankOfOwner owner j = i.1 := (h_spec a i).2
  have h_elem :
      (List.ofFn (fun j' => (K.get (owner j')).1.getD (rankOfOwner owner j') default))[j.1]'(by
        rw [List.length_ofFn]; exact j.2) = (K.get a).1.get i := by
    rw [List.getElem_ofFn, hj_rank]
    revert hj_rank
    rw [hj_own]
    intro _
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem i.2, Option.getD_some]
    rfl
  change (if decide (τ j ≤ t) = true then
      boolToZMod2 (staticCSSPauliFlip D_field ((K.get a).1.get i).2.1 ((K.get a).1.get i).2.2 c)
    else 0) =
    if decide (τ j ≤ t) = true then
      boolToZMod2 (staticCSSPauliFlip D_field
        ((List.ofFn (fun j' => (K.get (owner j')).1.getD (rankOfOwner owner j') default))[j.1]'(by
          rw [List.length_ofFn]; exact j.2)).2.1
        ((List.ofFn (fun j' => (K.get (owner j')).1.getD (rankOfOwner owner j') default))[j.1]'(by
          rw [List.length_ofFn]; exact j.2)).2.2 c)
    else 0
  rw [h_elem]

private lemma measurable_and_integrableOn_worldlineTrajectorySyndrome
    {L q_code r_0 m_max : ℕ}
    (D_field : Box3D L → LocalCSSDescriptor q_code r_0 m_max)
    (jumps : List (WorldlineJumpMonomer L q_code))
    (σ₀ : IdxCSS[L, q_code, m_max] → Bool)
    (g : (IdxCSS[L, q_code, m_max] → Bool) → ℝ) :
    Measurable (fun p : ℝ × (Fin jumps.length → ℝ) =>
      g (worldlineTrajectorySyndrome D_field jumps σ₀ p.2 p.1)) ∧
    ∀ (τ : Fin jumps.length → ℝ) (β : ℝ),
      MeasureTheory.IntegrableOn
        (fun t : ℝ => g (worldlineTrajectorySyndrome D_field jumps σ₀ τ t))
        (Set.Icc 0 β) := by
  have h_list : ∀ (l : List (Fin jumps.length)) (h : (IdxCSS[L, q_code, m_max] → Bool) → ℝ),
      Measurable (fun p : ℝ × (Fin jumps.length → ℝ) =>
        h (((l.filter (fun j => decide (p.2 j ≤ p.1))).foldr
          (fun j acc =>
            syndromeXor (staticCSSPauliFlip D_field (jumps.get j).2.1 (jumps.get j).2.2) acc)
          σ₀))) := by
    intro l
    induction l with
    | nil =>
      intro h
      simp only [List.filter_nil, List.foldr_nil]
      exact measurable_const
    | cons hd tl ih =>
      intro h
      have h_eq : (fun p : ℝ × (Fin jumps.length → ℝ) =>
          h ((((hd :: tl).filter (fun j => decide (p.2 j ≤ p.1))).foldr
            (fun j acc =>
              syndromeXor (staticCSSPauliFlip D_field (jumps.get j).2.1 (jumps.get j).2.2) acc)
            σ₀))) =
          Set.piecewise {p : ℝ × (Fin jumps.length → ℝ) | p.2 hd ≤ p.1}
            (fun p => h (syndromeXor
              (staticCSSPauliFlip D_field (jumps.get hd).2.1 (jumps.get hd).2.2)
              ((tl.filter (fun j => decide (p.2 j ≤ p.1))).foldr
                (fun j acc =>
                  syndromeXor (staticCSSPauliFlip D_field (jumps.get j).2.1 (jumps.get j).2.2) acc)
                σ₀)))
            (fun p => h ((tl.filter (fun j => decide (p.2 j ≤ p.1))).foldr
              (fun j acc =>
                syndromeXor (staticCSSPauliFlip D_field (jumps.get j).2.1 (jumps.get j).2.2) acc)
              σ₀)) := by
        ext p
        by_cases hp : p.2 hd ≤ p.1
        · simp [Set.piecewise, hp]
        · simp [Set.piecewise, hp]
      rw [h_eq]
      refine Measurable.piecewise
        (measurableSet_le ((measurable_pi_apply hd).comp measurable_snd) measurable_fst)
        (ih (fun η => h (syndromeXor
          (staticCSSPauliFlip D_field (jumps.get hd).2.1 (jumps.get hd).2.2) η)))
        (ih h)
  have h_joint : Measurable (fun p : ℝ × (Fin jumps.length → ℝ) =>
      g (worldlineTrajectorySyndrome D_field jumps σ₀ p.2 p.1)) :=
    h_list (List.finRange jumps.length) g
  refine ⟨h_joint, fun τ β => ?_⟩
  have h_meas_t : Measurable (fun t : ℝ => g (worldlineTrajectorySyndrome D_field jumps σ₀ τ t)) :=
    h_joint.comp (Measurable.prodMk measurable_id measurable_const)
  let C_max : ℝ := ∑ η : IdxCSS[L, q_code, m_max] → Bool, ‖g η‖
  have h_vol : MeasureTheory.volume (Set.Icc 0 β) < ⊤ := by
    rw [Real.volume_Icc]
    exact ENNReal.ofReal_lt_top
  refine (MeasureTheory.integrableOn_const (C := C_max) h_vol.ne).mono'
    h_meas_t.aestronglyMeasurable (Filter.Eventually.of_forall fun t => ?_)
  exact Finset.single_le_sum (fun η _ => norm_nonneg (g η))
    (Finset.mem_univ (worldlineTrajectorySyndrome D_field jumps σ₀ τ t))

private lemma worldlineTrajectorySyndrome_xor_false_and_supp
    {L q_code r_0 m_max w_0 R_cut : ℕ} [NeZero L] {C_RCA : ℝ}
    (D_field : Box3D L → LocalCSSDescriptor q_code r_0 m_max)
    (sys : SysCSS[L, q_code, m_max])
    (h_sys_supp : ∀ idx, sys.support idx = staticCSSCheckSupport D_field idx)
    (h_geom : sys.IsGeometricallyLocal r_0 w_0)
    (hr0_le : 1 + 4 * (r_0 : ℝ) ≤ C_RCA)
    {γ : WorldlineDysonPolymer L q_code}
    (hγ : IsValidWorldlinePolymer D_field sys C_RCA R_cut γ)
    (σ₀ : IdxCSS[L, q_code, m_max] → Bool)
    (τ : Fin γ.1.length → ℝ) (t : ℝ) :
    worldlineTrajectorySyndrome D_field γ.1 σ₀ τ t =
      syndromeXor (worldlineTrajectorySyndrome D_field γ.1 (fun _ => false) τ t) σ₀ ∧
    (∀ c : IdxCSS[L, q_code, m_max],
      worldlineTrajectorySyndrome D_field γ.1 (fun _ => false) τ t c = true →
      c ∈ worldlinePolymerNativeCollar sys C_RCA γ) := by
  have h_fold : ∀ l : List (Fin γ.1.length),
      l.foldr (fun j acc =>
        syndromeXor (staticCSSPauliFlip D_field (γ.1.get j).2.1 (γ.1.get j).2.2) acc) σ₀ =
      syndromeXor (l.foldr (fun j acc =>
        syndromeXor (staticCSSPauliFlip D_field (γ.1.get j).2.1 (γ.1.get j).2.2) acc)
        (fun _ => false)) σ₀ := by
    intro l
    induction l with
    | nil => ext c; change σ₀ c = bne false (σ₀ c); cases σ₀ c <;> rfl
    | cons hd tl ih =>
      rw [List.foldr_cons, List.foldr_cons, ih]
      ext c
      let d_hd := staticCSSPauliFlip D_field (γ.1.get hd).2.1 (γ.1.get hd).2.2 c
      let d_tl := (tl.foldr (fun j acc =>
        syndromeXor (staticCSSPauliFlip D_field (γ.1.get j).2.1 (γ.1.get j).2.2) acc)
        (fun _ => false)) c
      change bne d_hd (bne d_tl (σ₀ c)) = bne (bne d_hd d_tl) (σ₀ c)
      cases d_hd <;> cases d_tl <;> cases σ₀ c <;> rfl
  refine ⟨h_fold ((List.finRange γ.1.length).filter (fun j => decide (τ j ≤ t))), ?_⟩
  intro c hc_true
  by_contra hc_not
  have h_false : worldlineTrajectorySyndrome D_field γ.1 (fun _ => false) τ t c = false := by
    unfold worldlineTrajectorySyndrome
    refine foldr_syndromeXor_eq_of_all_false
      (fun j => staticCSSPauliFlip D_field (γ.1.get j).2.1 (γ.1.get j).2.2)
      ((List.finRange γ.1.length).filter (fun j => decide (τ j ≤ t))) c (fun j _ => ?_) (fun _ => false)
    (try dsimp only)
    cases h_flip : staticCSSPauliFlip D_field (γ.1.get j).2.1 (γ.1.get j).2.2 c
    · rfl
    · exact False.elim (hc_not (staticCSSPauliFlip_mem_worldlinePolymerNativeCollar
        D_field sys h_sys_supp h_geom hr0_le hγ (List.get_mem γ.1 j) h_flip))
  rw [h_false] at hc_true
  cases hc_true

private lemma disjoint_monomers_and_mayer_of_compatible_hd_collar
    {L q_code r_0 m_max w_0 R_cut : ℕ} [NeZero L] {C_RCA : ℝ}
    (D_field : Box3D L → LocalCSSDescriptor q_code r_0 m_max)
    (sys : SysCSS[L, q_code, m_max])
    (h_sys_supp : ∀ idx, sys.support idx = staticCSSCheckSupport D_field idx)
    (h_geom : sys.IsGeometricallyLocal r_0 w_0)
    (hr0_le : 1 + 4 * (r_0 : ℝ) ≤ C_RCA)
    (K : WorldlineUrsellCluster L q_code)
    (hK_valid : ∀ γ ∈ K, IsValidWorldlinePolymer D_field sys C_RCA R_cut γ)
    (hK_pw : K.Pairwise (fun γ₁ γ₂ => ¬ArePolymersIncompatible sys C_RCA γ₁ γ₂)) :
    (∀ i j : Fin K.length, i ≠ j →
      Disjoint (worldlinePolymerMonomers (K.get i)) (worldlinePolymerMonomers (K.get j)) ∧
      Disjoint (K.get i).2 (K.get j).2) ∧
    K.foldr (fun γ acc => γ.2 ∪ acc) ∅ =
      (Finset.univ : Finset (Fin K.length)).biUnion (fun i => (K.get i).2) := by
  have h_mon_col_ne : ∀ γ ∈ K, ∀ p ∈ worldlinePolymerMonomers γ,
      (rcaCollarChecks sys C_RCA p.1 p.2).Nonempty := by
    intro γ hγ p hp
    have hγ_val := hK_valid γ hγ
    have h_ne : γ.1 ≠ [] := by
      intro h_nil; have h_len := hγ_val.2.2.1.1; rw [h_nil, List.length_nil] at h_len; omega
    rcases List.exists_mem_of_ne_nil γ.1 h_ne with ⟨ξ₀, hξ₀⟩
    have hp₀ : ξ₀.1 ∈ worldlinePolymerMonomers γ :=
      Finset.mem_union_left _ (List.mem_toFinset.mpr (List.mem_map_of_mem hξ₀))
    have h_path := hγ_val.2.2.2.2 ξ₀.1 hp₀ p hp
    cases h_path with
    | refl =>
      have h_flip_ne := (hγ_val.2.1 ξ₀ hξ₀).2.1
      have h_ex_c : ∃ c : IdxCSS[L, q_code, m_max],
          staticCSSPauliFlip D_field ξ₀.2.1 ξ₀.2.2 c = true := by
        by_contra! h_all; apply h_flip_ne; funext c
        cases h_val : staticCSSPauliFlip D_field ξ₀.2.1 ξ₀.2.2 c
        · rfl
        · exact False.elim (h_all c h_val)
      rcases h_ex_c with ⟨c, hc⟩
      rcases mem_scaleCubeFinset_iff.mp (hγ_val.1 ξ₀.1 hp₀) with ⟨hr, hA⟩
      have hc_int := staticCSSPauliFlip_mem_cubeIntersectingChecks
        D_field sys h_sys_supp ξ₀.1.2 ξ₀.2.1 ξ₀.2.2 (hγ_val.2.1 ξ₀ hξ₀).1 c hc
      exact ⟨c, cubeIntersectingChecks_subset_rcaCollarChecks sys h_geom hr0_le
        (Finset.mem_Icc.mp hr).1 hA hc_int⟩
    | tail _ h_step =>
      rcases Finset.not_disjoint_iff.mp h_step.2.2.2 with ⟨c, _, hc_p⟩
      exact ⟨c, hc_p⟩
  have h_pw_get := List.pairwise_iff_get.mp hK_pw
  have h_disj_col : ∀ i j : Fin K.length, i ≠ j →
      Disjoint (worldlinePolymerNativeCollar sys C_RCA (K.get i))
        (worldlinePolymerNativeCollar sys C_RCA (K.get j)) := by
    intro i j hij
    rcases lt_or_gt_of_ne hij with h_lt | h_gt
    · exact not_not.mp (h_pw_get i j h_lt)
    · exact (not_not.mp (h_pw_get j i h_gt)).symm
  refine ⟨fun i j hij => ?_, ?_⟩
  · have h_mon : Disjoint (worldlinePolymerMonomers (K.get i))
        (worldlinePolymerMonomers (K.get j)) := by
      refine Finset.disjoint_left.mpr fun p hp_i hp_j => ?_
      rcases h_mon_col_ne (K.get i) (List.get_mem K i) p hp_i with ⟨c, hc⟩
      exact Finset.disjoint_left.mp (h_disj_col i j hij)
        (Finset.mem_biUnion.mpr ⟨p, hp_i, hc⟩)
        (Finset.mem_biUnion.mpr ⟨p, hp_j, hc⟩)
    exact ⟨h_mon, Finset.disjoint_left.mpr fun ϑ hϑ_i hϑ_j =>
      Finset.disjoint_left.mp h_mon (Finset.mem_union_right _ hϑ_i) (Finset.mem_union_right _ hϑ_j)⟩
  · ext ϑ
    simp only [Finset.mem_biUnion, Finset.mem_univ, true_and]
    clear h_mon_col_ne h_pw_get h_disj_col hK_valid hK_pw
    induction K with
    | nil => simp
    | cons hd tl ih =>
      rw [List.foldr_cons, Finset.mem_union, ih]
      constructor
      · rintro (h_hd | ⟨i, h_tl⟩)
        · exact ⟨⟨0, Nat.succ_pos _⟩, h_hd⟩
        · exact ⟨i.succ, h_tl⟩
      · rintro ⟨i, hi⟩
        cases i using Fin.cases with
        | zero => exact Or.inl hi
        | succ j => exact Or.inr ⟨j, hi⟩

private lemma worldlineBareAction_and_mayerBond_shuffleListOfOwner_eq
    {L q_code r_0 m_max w_0 R_cut : ℕ} [NeZero L] {C_RCA β : ℝ}
    (D_field : Box3D L → LocalCSSDescriptor q_code r_0 m_max)
    (sys : SysCSS[L, q_code, m_max])
    (h_sys_checks : ∀ idx, sys.checkProj idx = staticCSSCheckProj D_field idx ∧
      sys.support idx = staticCSSCheckSupport D_field idx ∧ sys.weight idx = 1)
    (h_geom : sys.IsGeometricallyLocal r_0 w_0)
    (hr0_le : 1 + 4 * (r_0 : ℝ) ≤ C_RCA)
    (d_loc : ℕ → Finset (Box3D L) → (IdxCSS[L, q_code, m_max] → Bool) → ℝ)
    (hd_collar : ∀ r ∈ Finset.Icc 1 (min R_cut L), ∀ A ∈ boxCubes 3 L r,
      ∀ σ₁ σ₂, restrictSyndromeToCollar (rcaCollarChecks sys C_RCA r A) σ₁ =
        restrictSyndromeToCollar (rcaCollarChecks sys C_RCA r A) σ₂ →
        d_loc r A σ₁ = d_loc r A σ₂)
    (K : WorldlineUrsellCluster L q_code)
    (hK_valid : ∀ γ ∈ K, IsValidWorldlinePolymer D_field sys C_RCA R_cut γ)
    (hK_pw : K.Pairwise (fun γ₁ γ₂ => ¬ArePolymersIncompatible sys C_RCA γ₁ γ₂))
    {owner : Fin (clusterTotalJumpLength K) → Fin K.length}
    (h_own : owner ∈ validShuffleOwnerFinset K)
    (σ₀ : IdxCSS[L, q_code, m_max] → Bool)
    (τ : Fin (clusterTotalJumpLength K) → ℝ) :
    Real.exp (-worldlineBareAction D_field sys (shuffleListOfOwner K owner) σ₀ β
        (fun j => τ (Fin.cast (length_shuffleListOfOwner K owner) j))) *
      ∏ ϑ ∈ K.foldr (fun γ acc => γ.2 ∪ acc) ∅,
        worldlineMayerBondFactor D_field (shuffleListOfOwner K owner) d_loc σ₀ β ϑ
          (fun j => τ (Fin.cast (length_shuffleListOfOwner K owner) j)) =
    ∏ a : Fin K.length,
      (Real.exp (-worldlineBareAction D_field sys (K.get a).1 σ₀ β
        (fun i => τ (shufflePosOfOwner h_own a i))) *
        ∏ ϑ ∈ (K.get a).2,
          worldlineMayerBondFactor D_field (K.get a).1 d_loc σ₀ β ϑ
            (fun i => τ (shufflePosOfOwner h_own a i))) := by
  have h_sys_supp : ∀ idx, sys.support idx = staticCSSCheckSupport D_field idx :=
    fun idx => (h_sys_checks idx).2.1
  let τ_comp : ∀ a : Fin K.length, Fin (K.get a).1.length → ℝ :=
    fun a i => τ (shufflePosOfOwner h_own a i)
  let δ : Fin K.length → ℝ → IdxCSS[L, q_code, m_max] → Bool :=
    fun a t => worldlineTrajectorySyndrome D_field (K.get a).1 (fun _ => false) (τ_comp a) t
  let σ_tot : ℝ → IdxCSS[L, q_code, m_max] → Bool :=
    fun t => (List.finRange K.length).foldr (fun a acc => syndromeXor (δ a t) acc) σ₀
  have h_traj_eq : ∀ t : ℝ,
      worldlineTrajectorySyndrome D_field (shuffleListOfOwner K owner) σ₀
        (fun j => τ (Fin.cast (length_shuffleListOfOwner K owner) j)) t = σ_tot t :=
    worldlineTrajectorySyndrome_shuffleListOfOwner_eq D_field K h_own σ₀ τ
  have h_pw_get := List.pairwise_iff_get.mp hK_pw
  have h_disj_col : ∀ a b : Fin K.length, a ≠ b →
      Disjoint (worldlinePolymerNativeCollar sys C_RCA (K.get a))
        (worldlinePolymerNativeCollar sys C_RCA (K.get b)) := by
    intro a b hab
    rcases lt_or_gt_of_ne hab with h_lt | h_gt
    · exact not_not.mp (h_pw_get a b h_lt)
    · exact (not_not.mp (h_pw_get b a h_gt)).symm
  have h_fin_pw : (List.finRange K.length).Pairwise (fun a b =>
      Disjoint (worldlinePolymerNativeCollar sys C_RCA (K.get a))
        (worldlinePolymerNativeCollar sys C_RCA (K.get b))) := by
    rw [List.pairwise_iff_get]
    intro a b h_lt
    exact h_disj_col ((List.finRange K.length).get a) ((List.finRange K.length).get b)
      (Fin.ne_of_lt (by simpa using h_lt))
  have h_supp : ∀ a : Fin K.length, ∀ t : ℝ, ∀ c,
      δ a t c = true → c ∈ worldlinePolymerNativeCollar sys C_RCA (K.get a) :=
    fun a t c hc => (worldlineTrajectorySyndrome_xor_false_and_supp
      D_field sys h_sys_supp h_geom hr0_le (hK_valid (K.get a) (List.get_mem K a))
      σ₀ (τ_comp a) t).2 c hc
  have h_en_t : ∀ t : ℝ,
      sys.syndromeEnergy (worldlineTrajectorySyndrome D_field (shuffleListOfOwner K owner) σ₀
        (fun j => τ (Fin.cast (length_shuffleListOfOwner K owner) j)) t) -
        sys.syndromeEnergy σ₀ =
      ∑ a : Fin K.length,
        (sys.syndromeEnergy (worldlineTrajectorySyndrome D_field (K.get a).1 σ₀ (τ_comp a) t) -
          sys.syndromeEnergy σ₀) := by
    intro t
    rw [h_traj_eq t]
    have h_add := (syndromeEnergy_foldr_syndromeXor_disjoint_list_add
      sys (fun a => worldlinePolymerNativeCollar sys C_RCA (K.get a)) (fun a => δ a t)
      (List.finRange K.length) h_fin_pw (fun a _ => h_supp a t) σ₀).1
    rw [h_add, ← Fin.sum_univ_def]
    refine Finset.sum_congr rfl fun a _ => ?_
    have h_xor := (worldlineTrajectorySyndrome_xor_false_and_supp
      D_field sys h_sys_supp h_geom hr0_le (hK_valid (K.get a) (List.get_mem K a))
      σ₀ (τ_comp a) t).1
    rw [← h_xor]
  have h_bare_eq :
      worldlineBareAction D_field sys (shuffleListOfOwner K owner) σ₀ β
        (fun j => τ (Fin.cast (length_shuffleListOfOwner K owner) j)) =
      ∑ a : Fin K.length, worldlineBareAction D_field sys (K.get a).1 σ₀ β (τ_comp a) := by
    unfold worldlineBareAction
    have h_congr :
        (fun t : ℝ =>
          sys.syndromeEnergy (worldlineTrajectorySyndrome D_field (shuffleListOfOwner K owner) σ₀
            (fun j => τ (Fin.cast (length_shuffleListOfOwner K owner) j)) t) -
            sys.syndromeEnergy σ₀) =
        fun t : ℝ =>
          ∑ a : Fin K.length,
            (sys.syndromeEnergy (worldlineTrajectorySyndrome D_field (K.get a).1 σ₀ (τ_comp a) t) -
              sys.syndromeEnergy σ₀) := funext h_en_t
    rw [h_congr, MeasureTheory.integral_finset_sum]
    intro a _
    exact (measurable_and_integrableOn_worldlineTrajectorySyndrome
      D_field (K.get a).1 σ₀ (fun η => sys.syndromeEnergy η - sys.syndromeEnergy σ₀)).2 (τ_comp a) β
  have h_exp_eq :
      Real.exp (-worldlineBareAction D_field sys (shuffleListOfOwner K owner) σ₀ β
        (fun j => τ (Fin.cast (length_shuffleListOfOwner K owner) j))) =
      ∏ a : Fin K.length,
        Real.exp (-worldlineBareAction D_field sys (K.get a).1 σ₀ β (τ_comp a)) := by
    rw [h_bare_eq, ← Finset.sum_neg_distrib, Real.exp_sum]
  rcases disjoint_monomers_and_mayer_of_compatible_hd_collar
      D_field sys h_sys_supp h_geom hr0_le K hK_valid hK_pw with ⟨h_disj_mon, h_fold_eq⟩
  have h_pw_mayer : (↑(Finset.univ : Finset (Fin K.length)) : Set (Fin K.length)).PairwiseDisjoint
      (fun a => (K.get a).2) := fun a _ b _ hab => (h_disj_mon a b hab).2
  have h_agree_col : ∀ a : Fin K.length, ∀ t : ℝ,
      ∀ c ∈ worldlinePolymerNativeCollar sys C_RCA (K.get a),
      σ_tot t c = worldlineTrajectorySyndrome D_field (K.get a).1 σ₀ (τ_comp a) t c := by
    intro a t c hc_a
    have h_xor_a := congr_fun (worldlineTrajectorySyndrome_xor_false_and_supp
      D_field sys h_sys_supp h_geom hr0_le (hK_valid (K.get a) (List.get_mem K a))
      σ₀ (τ_comp a) t).1 c
    rw [h_xor_a]
    have h_other_false : ∀ b : Fin K.length, b ≠ a → δ b t c = false := by
      intro b hba
      cases hb : δ b t c
      · rfl
      · exact False.elim (Finset.disjoint_left.mp (h_disj_col a b hba.symm) hc_a (h_supp b t c hb))
    have h_fold_in : ∀ (l : List (Fin K.length)), l.Nodup →
        ((l.foldr (fun b acc => syndromeXor (δ b t) acc) σ₀) c =
          if a ∈ l then (syndromeXor (δ a t) σ₀) c else σ₀ c) := by
      intro l hl_nd
      induction l with
      | nil => simp
      | cons hd tl ih =>
        rcases List.nodup_cons.mp hl_nd with ⟨hd_not_tl, htl_nd⟩
        rw [List.foldr_cons]
        change bne (δ hd t c) ((tl.foldr (fun b acc => syndromeXor (δ b t) acc) σ₀) c) = _
        rw [ih htl_nd]
        by_cases h_eq : hd = a
        · subst h_eq; rw [if_neg hd_not_tl, if_pos List.mem_cons_self]; rfl
        · rw [h_other_false hd h_eq]
          simp only [List.mem_cons, Ne.symm h_eq, false_or]
          cases (if a ∈ tl then (syndromeXor (δ a t) σ₀) c else σ₀ c) <;> rfl
    have h_res := h_fold_in (List.finRange K.length) (List.nodup_finRange K.length)
    rw [if_pos (List.mem_finRange a)] at h_res
    exact h_res
  have h_mayer_eq :
      (∏ ϑ ∈ K.foldr (fun γ acc => γ.2 ∪ acc) ∅,
        worldlineMayerBondFactor D_field (shuffleListOfOwner K owner) d_loc σ₀ β ϑ
          (fun j => τ (Fin.cast (length_shuffleListOfOwner K owner) j))) =
      ∏ a : Fin K.length, ∏ ϑ ∈ (K.get a).2,
        worldlineMayerBondFactor D_field (K.get a).1 d_loc σ₀ β ϑ (τ_comp a) := by
    rw [h_fold_eq, Finset.prod_biUnion h_pw_mayer]
    refine Finset.prod_congr rfl fun a _ => Finset.prod_congr rfl fun ϑ hϑ => ?_
    unfold worldlineMayerBondFactor
    have hγ_a := hK_valid (K.get a) (List.get_mem K a)
    have hϑ_mon : ϑ ∈ worldlinePolymerMonomers (K.get a) := Finset.mem_union_right _ hϑ
    rcases mem_scaleCubeFinset_iff.mp (hγ_a.1 ϑ hϑ_mon) with ⟨hr, hA⟩
    have h_int_eq :
        (fun t : ℝ =>
          d_loc ϑ.1 ϑ.2
            (worldlineTrajectorySyndrome D_field (shuffleListOfOwner K owner) σ₀
              (fun j => τ (Fin.cast (length_shuffleListOfOwner K owner) j)) t) -
            d_loc ϑ.1 ϑ.2 σ₀) =
        fun t : ℝ =>
          d_loc ϑ.1 ϑ.2 (worldlineTrajectorySyndrome D_field (K.get a).1 σ₀ (τ_comp a) t) -
            d_loc ϑ.1 ϑ.2 σ₀ := by
      funext t
      rw [h_traj_eq t]
      congr 1
      refine hd_collar ϑ.1 hr ϑ.2 hA (σ_tot t)
        (worldlineTrajectorySyndrome D_field (K.get a).1 σ₀ (τ_comp a) t) ?_
      ext c
      unfold restrictSyndromeToCollar
      split_ifs with hc_col
      · exact h_agree_col a t c (Finset.mem_biUnion.mpr ⟨ϑ, hϑ_mon, hc_col⟩)
      · rfl
    rw [h_int_eq]
  rw [h_exp_eq, h_mayer_eq, ← Finset.prod_mul_distrib]

private lemma sum_multiPolymerShuffleFinset_eq_sum_validShuffleOwnerFinset
    {L q_code r_0 m_max w_0 R_cut : ℕ} [NeZero L] {C_RCA : ℝ}
    (D_field : Box3D L → LocalCSSDescriptor q_code r_0 m_max)
    (sys : SysCSS[L, q_code, m_max])
    (h_sys_supp : ∀ idx, sys.support idx = staticCSSCheckSupport D_field idx)
    (h_geom : sys.IsGeometricallyLocal r_0 w_0)
    (hr0_le : 1 + 4 * (r_0 : ℝ) ≤ C_RCA)
    (K : WorldlineUrsellCluster L q_code)
    (hK_valid : ∀ γ ∈ K, IsValidWorldlinePolymer D_field sys C_RCA R_cut γ)
    (hK_pw : K.Pairwise (fun γ₁ γ₂ => ¬ArePolymersIncompatible sys C_RCA γ₁ γ₂))
    (Φ : List (WorldlineJumpMonomer L q_code) → ℝ) :
    (∑ ξ_list ∈ multiPolymerShuffleFinset D_field R_cut K, Φ ξ_list) =
      ∑ owner ∈ validShuffleOwnerFinset K, Φ (shuffleListOfOwner K owner) := by
  rcases disjoint_monomers_and_mayer_of_compatible_hd_collar
      D_field sys h_sys_supp h_geom hr0_le K hK_valid hK_pw with ⟨h_disj_mon, _⟩
  symm
  refine Finset.sum_bij (fun owner _ => shuffleListOfOwner K owner)
    (fun owner h_own => ?_)
    (fun owner₁ h_own₁ owner₂ h_own₂ h_eq => ?_)
    (fun ξ_list hξ => ?_)
    (fun _ _ => rfl)
  · have h_card := (Finset.mem_filter.mp h_own).2
    let idx : ∀ j : Fin (clusterTotalJumpLength K), Fin (K.get (owner j)).1.length :=
      fun j => ⟨rankOfOwner owner j, by
        have h_lt := rankOfOwner_lt_card_fiber owner j
        rwa [h_card (owner j)] at h_lt⟩
    have h_mem_len : shuffleListOfOwner K owner ∈
        worldlineJumpListFinsetOfLength D_field R_cut (clusterTotalJumpLength K) := by
      unfold worldlineJumpListFinsetOfLength
      have h_in_all : ∀ j : Fin (clusterTotalJumpLength K),
          (K.get (owner j)).1.get (idx j) ∈ worldlineAllJumpMonomerFinset D_field R_cut := by
        intro j
        have hγ_val := hK_valid (K.get (owner j)) (List.get_mem K (owner j))
        exact ((isValidWorldlinePolymer_monomers_and_jumps_iff D_field (K.get (owner j))).mp
          ⟨hγ_val.1, hγ_val.2.1⟩).1 _ (List.get_mem (K.get (owner j)).1 (idx j))
      refine Finset.mem_image.mpr
        ⟨fun j => ⟨(K.get (owner j)).1.get (idx j), h_in_all j⟩,
          Fintype.mem_piFinset.mpr (fun _ => Finset.mem_univ _), ?_⟩
      unfold shuffleListOfOwner
      refine congrArg List.ofFn (funext fun j => ?_)
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (idx j).2, Option.getD_some]
      rfl
    refine Finset.mem_filter.mpr ⟨h_mem_len, owner, idx, ?_, ?_, ?_⟩
    · intro j₁ j₂ h_lt h_eq
      exact rankOfOwner_strictMono_on_fiber owner h_lt h_eq
    · intro a i
      rcases rankOfOwner_surj_and_unique owner a (h_card a) i with ⟨j, hj_own, hj_rank⟩
      exact ⟨j, hj_own, hj_rank⟩
    · intro j
      unfold shuffleListOfOwner
      rw [List.getD_eq_getElem?_getD, List.getElem?_ofFn, dif_pos j.2, Option.getD_some,
        List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (idx j).2, Option.getD_some]
      rfl
  · (try dsimp only at h_eq)
    funext j
    have h_card₁ := (Finset.mem_filter.mp h_own₁).2 (owner₁ j)
    have h_card₂ := (Finset.mem_filter.mp h_own₂).2 (owner₂ j)
    have h_lt₁ : rankOfOwner owner₁ j < (K.get (owner₁ j)).1.length := by
      have h1 := rankOfOwner_lt_card_fiber owner₁ j; rwa [h_card₁] at h1
    have h_lt₂ : rankOfOwner owner₂ j < (K.get (owner₂ j)).1.length := by
      have h2 := rankOfOwner_lt_card_fiber owner₂ j; rwa [h_card₂] at h2
    have h_elem_eq :
        (shuffleListOfOwner K owner₁)[j.1]'(by rw [length_shuffleListOfOwner]; exact j.2) =
        (shuffleListOfOwner K owner₂)[j.1]'(by rw [length_shuffleListOfOwner]; exact j.2) := by
      simp [h_eq]
    unfold shuffleListOfOwner at h_elem_eq
    rw [List.getElem_ofFn, List.getElem_ofFn,
      List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h_lt₁, Option.getD_some,
      List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h_lt₂, Option.getD_some] at h_elem_eq
    have hp₁ : ((K.get (owner₁ j)).1[rankOfOwner owner₁ j]).1 ∈
        worldlinePolymerMonomers (K.get (owner₁ j)) :=
      Finset.mem_union_left _ (List.mem_toFinset.mpr
        (List.mem_map_of_mem (List.getElem_mem h_lt₁)))
    have hp₂ : ((K.get (owner₂ j)).1[rankOfOwner owner₂ j]).1 ∈
        worldlinePolymerMonomers (K.get (owner₂ j)) :=
      Finset.mem_union_left _ (List.mem_toFinset.mpr
        (List.mem_map_of_mem (List.getElem_mem h_lt₂)))
    rw [h_elem_eq] at hp₁
    by_contra h_ne
    exact Finset.disjoint_left.mp (h_disj_mon (owner₁ j) (owner₂ j) h_ne).1 hp₁ hp₂
  · rcases Finset.mem_filter.mp hξ with ⟨h_mem_len, owner, idx, h_mono, h_surj, h_getD⟩
    rcases idx_eq_rankOfOwner_and_card_fiber K owner idx h_mono h_surj with ⟨h_card, h_idx_eq⟩
    have h_own : owner ∈ validShuffleOwnerFinset K :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, h_card⟩
    have h_len : ξ_list.length = clusterTotalJumpLength K :=
      length_eq_of_mem_worldlineJumpListFinsetOfLength D_field R_cut _ h_mem_len
    refine ⟨owner, h_own, ?_⟩
    refine List.ext_getElem (by rw [length_shuffleListOfOwner, h_len]) (fun n hn₁ hn₂ => ?_)
    let j : Fin (clusterTotalJumpLength K) := ⟨n, by rwa [length_shuffleListOfOwner] at hn₁⟩
    have h_j := h_getD j
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hn₂, Option.getD_some] at h_j
    dsimp only [shuffleListOfOwner] at hn₁ ⊢
    rw [List.getElem_ofFn, ← h_idx_eq j,
      List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (idx j).2, Option.getD_some]
    exact h_j.symm

private def sigmaFinSuccEquiv {p : ℕ} (m : Fin (p + 1) → ℕ) :
    Fin (m 0) ⊕ (Σ a : Fin p, Fin (m a.succ)) ≃ (Σ a : Fin (p + 1), Fin (m a)) where
  toFun
    | Sum.inl i => ⟨0, i⟩
    | Sum.inr ⟨a, i⟩ => ⟨a.succ, i⟩
  invFun x := Fin.cases (motive := fun a => Fin (m a) → Fin (m 0) ⊕ (Σ a' : Fin p, Fin (m a'.succ)))
    (fun i => Sum.inl i) (fun a' i => Sum.inr ⟨a', i⟩) x.1 x.2
  left_inv x := by
    rcases x with i | ⟨a, i⟩
    · simp [Fin.cases_zero]
    · simp [Fin.cases_succ]
  right_inv x := by
    rcases x with ⟨a, i⟩
    refine Fin.cases (motive := fun a => ∀ i : Fin (m a),
      (match Fin.cases (motive := fun a => Fin (m a) → Fin (m 0) ⊕ (Σ a' : Fin p, Fin (m a'.succ)))
        (fun i => Sum.inl i) (fun a' i => Sum.inr ⟨a', i⟩) a i with
      | Sum.inl i => (⟨0, i⟩ : Σ a : Fin (p + 1), Fin (m a))
      | Sum.inr ⟨a', i⟩ => ⟨a'.succ, i⟩) = ⟨a, i⟩)
      (fun i => by simp [Fin.cases_zero])
      (fun a' i => by simp [Fin.cases_succ]) a i

private lemma integral_sigma_pi_prod_eq_prod :
    ∀ (p : ℕ) (m : Fin p → ℕ) (F : ∀ a : Fin p, (Fin (m a) → ℝ) → ℝ),
      (∫ ω : (Σ a : Fin p, Fin (m a)) → ℝ, ∏ a : Fin p, F a (fun i => ω ⟨a, i⟩)) =
        ∏ a : Fin p, ∫ τ_a : Fin (m a) → ℝ, F a τ_a
  | 0, m, F => by
    haveI : IsEmpty (Σ a : Fin 0, Fin (m a)) := ⟨fun x => Fin.elim0 x.1⟩
    simp only [Finset.univ_eq_empty, Finset.prod_empty, MeasureTheory.integral_const,
      smul_eq_mul, mul_one]
    have h_univ : (Set.univ : Set ((Σ a : Fin 0, Fin (m a)) → ℝ)) =
        Set.pi Set.univ (fun _ => Set.univ) := by ext; simp
    have h_vol : MeasureTheory.volume (Set.univ : Set ((Σ a : Fin 0, Fin (m a)) → ℝ)) = 1 := by
      rw [h_univ, MeasureTheory.volume_pi_pi]
      simp
    simp [MeasureTheory.measureReal_def, h_vol]
  | p + 1, m, F => by
    let e₁ : ((Σ a : Fin (p + 1), Fin (m a)) → ℝ) ≃ᵐ
        ((Fin (m 0) ⊕ (Σ a : Fin p, Fin (m a.succ))) → ℝ) :=
      MeasurableEquiv.piCongrLeft (fun _ => ℝ) (sigmaFinSuccEquiv m).symm
    have mp₁ : MeasureTheory.MeasurePreserving e₁ MeasureTheory.volume MeasureTheory.volume :=
      MeasureTheory.measurePreserving_piCongrLeft (fun _ => MeasureTheory.volume)
        (sigmaFinSuccEquiv m).symm
    let e₂ : ((Fin (m 0) ⊕ (Σ a : Fin p, Fin (m a.succ))) → ℝ) ≃ᵐ
        (Fin (m 0) → ℝ) × ((Σ a : Fin p, Fin (m a.succ)) → ℝ) :=
      MeasurableEquiv.sumPiEquivProdPi (fun _ => ℝ)
    have mp₂ : MeasureTheory.MeasurePreserving e₂ MeasureTheory.volume MeasureTheory.volume :=
      MeasureTheory.volume_measurePreserving_sumPiEquivProdPi (fun _ => ℝ)
    let e := e₁.trans e₂
    have mp : MeasureTheory.MeasurePreserving e MeasureTheory.volume MeasureTheory.volume :=
      mp₂.comp mp₁
    let g_prod : (Fin (m 0) → ℝ) × ((Σ a : Fin p, Fin (m a.succ)) → ℝ) → ℝ :=
      fun z => F 0 z.1 * ∏ a : Fin p, F a.succ (fun i => z.2 ⟨a, i⟩)
    have h_comp : ∀ ω : (Σ a : Fin (p + 1), Fin (m a)) → ℝ,
        (∏ a : Fin (p + 1), F a (fun i => ω ⟨a, i⟩)) = g_prod (e ω) := by
      intro ω
      dsimp only [g_prod, e, MeasurableEquiv.trans_apply]
      rw [Fin.prod_univ_succ]
      rfl
    have h_prod : (∫ y : (Fin (m 0) → ℝ) × ((Σ a : Fin p, Fin (m a.succ)) → ℝ), g_prod y) =
        (∫ y₁ : Fin (m 0) → ℝ, F 0 y₁) *
          ∫ y₂ : (Σ a : Fin p, Fin (m a.succ)) → ℝ, ∏ a : Fin p, F a.succ (fun i => y₂ ⟨a, i⟩) :=
      MeasureTheory.integral_prod_mul (F 0)
        (fun y₂ : (Σ a : Fin p, Fin (m a.succ)) → ℝ => ∏ a : Fin p, F a.succ (fun i => y₂ ⟨a, i⟩))
    simp_rw [h_comp]
    rw [mp.integral_comp' g_prod, h_prod,
      integral_sigma_pi_prod_eq_prod p (fun a => m a.succ) (fun a => F a.succ),
      Fin.prod_univ_succ]

private lemma volume_coord_eq_zero {ι : Type*} [Fintype ι] [DecidableEq ι]
    {p₁ p₂ : ι} (hne : p₁ ≠ p₂) :
    MeasureTheory.volume {ω : ι → ℝ | ω p₁ = ω p₂} = 0 := by
  let L : (ι → ℝ) →ₗ[ℝ] ℝ :=
    LinearMap.proj (R := ℝ) (φ := fun _ : ι => ℝ) p₁ -
      LinearMap.proj (R := ℝ) (φ := fun _ : ι => ℝ) p₂
  have h_set : {ω : ι → ℝ | ω p₁ = ω p₂} = (LinearMap.ker L : Set (ι → ℝ)) := by
    ext ω
    simp [L, LinearMap.mem_ker, sub_eq_zero]
  have h_ne_top : LinearMap.ker L ≠ ⊤ := by
    intro h_top
    have h_mem : (fun q : ι => if q = p₁ then (1 : ℝ) else 0) ∈ LinearMap.ker L := by
      rw [h_top]; trivial
    rw [LinearMap.mem_ker] at h_mem
    dsimp [L] at h_mem
    simp [hne.symm] at h_mem
  rw [h_set]
  exact MeasureTheory.Measure.addHaar_submodule MeasureTheory.volume (LinearMap.ker L) h_ne_top

private lemma volume_not_injective_eq_zero {ι : Type*} [Fintype ι] [DecidableEq ι] :
    MeasureTheory.volume {ω : ι → ℝ | ¬Function.Injective ω} = 0 := by
  have h_sub : {ω : ι → ℝ | ¬Function.Injective ω} ⊆
      ⋃ p₁ : ι, ⋃ p₂ : ι, ⋃ (_ : p₁ ≠ p₂), {ω : ι → ℝ | ω p₁ = ω p₂} := by
    intro ω hω
    unfold Function.Injective at hω
    push_neg at hω
    rcases hω with ⟨p₁, p₂, h_eq, h_ne⟩
    exact Set.mem_iUnion.mpr ⟨p₁, Set.mem_iUnion.mpr ⟨p₂, Set.mem_iUnion.mpr ⟨h_ne, h_eq⟩⟩⟩
  refine MeasureTheory.measure_mono_null h_sub ?_
  refine MeasureTheory.measure_iUnion_null fun p₁ => ?_
  refine MeasureTheory.measure_iUnion_null fun p₂ => ?_
  refine MeasureTheory.measure_iUnion_null fun h_ne => ?_
  exact volume_coord_eq_zero h_ne

private def shuffleSigmaEquivOfOwner {L q_code : ℕ}
    {K : WorldlineUrsellCluster L q_code}
    {owner : Fin (clusterTotalJumpLength K) → Fin K.length}
    (h_own : owner ∈ validShuffleOwnerFinset K) :
    (Σ a : Fin K.length, Fin (K.get a).1.length) ≃ Fin (clusterTotalJumpLength K) :=
  Equiv.ofBijective (fun p => shufflePosOfOwner h_own p.1 p.2) (shufflePosOfOwner_spec h_own).2.2

private lemma card_sigma_cluster_eq_clusterTotalJumpLength {L q_code : ℕ}
    (K : WorldlineUrsellCluster L q_code) :
    Fintype.card (Σ a : Fin K.length, Fin (K.get a).1.length) = clusterTotalJumpLength K := by
  rw [Fintype.card_sigma]
  simp only [Fintype.card_fin, clusterTotalJumpLength]
  rw [Fin.sum_univ_def]
  change ((List.finRange K.length).map ((fun γ : WorldlineDysonPolymer L q_code => γ.1.length) ∘ K.get)).sum =
    (K.map (fun γ => γ.1.length)).sum
  rw [← List.map_map, List.map_get_finRange]

private lemma inOrderedDysonSimplex_piCongrLeft_shuffleSigmaEquiv_imp
    {L q_code : ℕ} {β : ℝ}
    {K : WorldlineUrsellCluster L q_code}
    {owner : Fin (clusterTotalJumpLength K) → Fin K.length}
    (h_own : owner ∈ validShuffleOwnerFinset K)
    {ω : (Σ a : Fin K.length, Fin (K.get a).1.length) → ℝ}
    (h_simp : InOrderedDysonSimplex β
      (MeasurableEquiv.piCongrLeft (fun _ => ℝ) (shuffleSigmaEquivOfOwner h_own) ω)) :
    ∀ a : Fin K.length, InOrderedDysonSimplex β (fun i => ω ⟨a, i⟩) := by
  intro a
  have h_app : ∀ i : Fin (K.get a).1.length,
      MeasurableEquiv.piCongrLeft (fun _ : Fin (clusterTotalJumpLength K) => ℝ)
        (shuffleSigmaEquivOfOwner h_own) ω (shufflePosOfOwner h_own a i) = ω ⟨a, i⟩ := by
    intro i
    exact MeasurableEquiv.piCongrLeft_apply_apply
      (β := fun _ : Fin (clusterTotalJumpLength K) => ℝ)
      (shuffleSigmaEquivOfOwner h_own) ω ⟨a, i⟩
  refine ⟨fun i => ?_, fun i₁ i₂ h_lt => ?_⟩
  · (try dsimp only)
    rw [← h_app i]
    exact h_simp.1 (shufflePosOfOwner h_own a i)
  · (try dsimp only)
    rw [← h_app i₁, ← h_app i₂]
    exact h_simp.2 ((shufflePosOfOwner_spec h_own).2.1 a h_lt)

private lemma owner_eq_of_inOrderedDysonSimplex_piCongrLeft
    {L q_code : ℕ} {β : ℝ}
    {K : WorldlineUrsellCluster L q_code}
    {owner₁ owner₂ : Fin (clusterTotalJumpLength K) → Fin K.length}
    (h_own₁ : owner₁ ∈ validShuffleOwnerFinset K)
    (h_own₂ : owner₂ ∈ validShuffleOwnerFinset K)
    {ω : (Σ a : Fin K.length, Fin (K.get a).1.length) → ℝ}
    (h₁ : InOrderedDysonSimplex β
      (MeasurableEquiv.piCongrLeft (fun _ => ℝ) (shuffleSigmaEquivOfOwner h_own₁) ω))
    (h₂ : InOrderedDysonSimplex β
      (MeasurableEquiv.piCongrLeft (fun _ => ℝ) (shuffleSigmaEquivOfOwner h_own₂) ω)) :
    owner₁ = owner₂ := by
  let e₁ := shuffleSigmaEquivOfOwner h_own₁
  let e₂ := shuffleSigmaEquivOfOwner h_own₂
  let τ₁ := MeasurableEquiv.piCongrLeft (fun _ : Fin (clusterTotalJumpLength K) => ℝ) e₁ ω
  let τ₂ := MeasurableEquiv.piCongrLeft (fun _ : Fin (clusterTotalJumpLength K) => ℝ) e₂ ω
  have h_comp : ∀ j : Fin (clusterTotalJumpLength K), τ₁ (e₁ (e₂.symm j)) = τ₂ j := fun j => by
    dsimp [τ₁, τ₂]
    rw [MeasurableEquiv.piCongrLeft_apply_apply]
    have h_symm := MeasurableEquiv.piCongrLeft_apply_apply
      (β := fun _ : Fin (clusterTotalJumpLength K) => ℝ) e₂ ω (e₂.symm j)
    rw [e₂.apply_symm_apply] at h_symm
    exact h_symm.symm
  have h_sm : StrictMono (fun j => e₁ (e₂.symm j)) := fun j₁ j₂ h_lt => by
    rw [← h₁.2.lt_iff_lt]
    change τ₁ (e₁ (e₂.symm j₁)) < τ₁ (e₁ (e₂.symm j₂))
    rw [h_comp j₁, h_comp j₂]
    exact h₂.2 h_lt
  have h_id := strictMono_fin_eq_id (fun j => e₁ (e₂.symm j)) h_sm
  funext j
  let p := e₂.symm j
  have hp₁ : e₁ p = j := h_id j
  have hp₂ : e₂ p = j := e₂.apply_symm_apply j
  have ho₁ : owner₁ (e₁ p) = p.1 := (shufflePosOfOwner_spec h_own₁).1 p.1 p.2 |>.1
  have ho₂ : owner₂ (e₂ p) = p.1 := (shufflePosOfOwner_spec h_own₂).1 p.1 p.2 |>.1
  rw [hp₁] at ho₁
  rw [hp₂] at ho₂
  exact ho₁.trans ho₂.symm

private lemma exists_owner_inOrderedDysonSimplex_of_injective
    {L q_code : ℕ} {β : ℝ}
    (K : WorldlineUrsellCluster L q_code)
    {ω : (Σ a : Fin K.length, Fin (K.get a).1.length) → ℝ}
    (h_inj : Function.Injective ω)
    (h_simp : ∀ a : Fin K.length, InOrderedDysonSimplex β (fun i => ω ⟨a, i⟩)) :
    ∃ owner ∈ validShuffleOwnerFinset K,
      ∃ h_own : owner ∈ validShuffleOwnerFinset K,
        InOrderedDysonSimplex β
          (MeasurableEquiv.piCongrLeft (fun _ => ℝ) (shuffleSigmaEquivOfOwner h_own) ω) := by
  let Ω_idx := Σ a : Fin K.length, Fin (K.get a).1.length
  let rk : Ω_idx → ℕ := fun p => (Finset.univ.filter (fun q : Ω_idx => ω q < ω p)).card
  have h_rk_lt_of_lt : ∀ {p₁ p₂ : Ω_idx}, ω p₁ < ω p₂ → rk p₁ < rk p₂ := by
    intro p₁ p₂ h_lt
    dsimp [rk]
    refine Finset.card_lt_card (ssubset_iff_subset_ne.mpr ⟨fun q hq => ?_, fun h_eq => ?_⟩)
    · rw [Finset.mem_filter] at hq ⊢
      exact ⟨hq.1, lt_trans hq.2 h_lt⟩
    · have hp₁_in : p₁ ∈ Finset.univ.filter (fun q : Ω_idx => ω q < ω p₂) :=
        Finset.mem_filter.mpr ⟨Finset.mem_univ p₁, h_lt⟩
      rw [← h_eq, Finset.mem_filter] at hp₁_in
      exact lt_irrefl (ω p₁) hp₁_in.2
  have h_rk_bound : ∀ p : Ω_idx, rk p < clusterTotalJumpLength K := by
    intro p
    rw [← card_sigma_cluster_eq_clusterTotalJumpLength K, ← Finset.card_univ]
    refine Finset.card_lt_card (ssubset_iff_subset_ne.mpr ⟨Finset.filter_subset _ _, fun h_eq => ?_⟩)
    have hp_in : p ∈ (Finset.univ : Finset Ω_idx) := Finset.mem_univ p
    rw [← h_eq, Finset.mem_filter] at hp_in
    exact lt_irrefl (ω p) hp_in.2
  let rkFin : Ω_idx → Fin (clusterTotalJumpLength K) := fun p => ⟨rk p, h_rk_bound p⟩
  have h_rk_inj : Function.Injective rkFin := by
    intro p₁ p₂ h_eq
    by_contra h_ne
    rcases lt_or_gt_of_ne (h_inj.ne h_ne) with h_lt | h_gt
    · exact ne_of_lt (h_rk_lt_of_lt h_lt) (congrArg Fin.val h_eq)
    · exact ne_of_gt (h_rk_lt_of_lt h_gt) (congrArg Fin.val h_eq)
  have h_rk_bij : Function.Bijective rkFin := by
    rw [Fintype.bijective_iff_injective_and_card]
    exact ⟨h_rk_inj, (card_sigma_cluster_eq_clusterTotalJumpLength K).trans (Fintype.card_fin _).symm⟩
  let e_ω : Ω_idx ≃ Fin (clusterTotalJumpLength K) := Equiv.ofBijective rkFin h_rk_bij
  have h_e_lt_iff : ∀ p₁ p₂ : Ω_idx, e_ω p₁ < e_ω p₂ ↔ ω p₁ < ω p₂ := by
    intro p₁ p₂
    constructor
    · intro h_lt
      by_contra! h_ge
      rcases eq_or_lt_of_le h_ge with h_eq | h_gt
      · exact lt_irrefl (e_ω p₁) (by rw [h_inj h_eq] at h_lt; exact h_lt)
      · exact not_lt_of_gt h_lt (h_rk_lt_of_lt h_gt)
    · exact fun h_lt => h_rk_lt_of_lt h_lt
  let owner : Fin (clusterTotalJumpLength K) → Fin K.length := fun j => (e_ω.symm j).1
  let idx : ∀ j : Fin (clusterTotalJumpLength K), Fin (K.get (owner j)).1.length :=
    fun j => (e_ω.symm j).2
  have h_mono : ∀ j₁ j₂ : Fin (clusterTotalJumpLength K),
      j₁ < j₂ → owner j₁ = owner j₂ → (idx j₁).1 < (idx j₂).1 := by
    intro j₁ j₂ h_lt h_own_eq
    have h_ω_lt : ω (e_ω.symm j₁) < ω (e_ω.symm j₂) := by
      rw [← h_e_lt_iff, e_ω.apply_symm_apply, e_ω.apply_symm_apply]
      exact h_lt
    rcases hp₁ : e_ω.symm j₁ with ⟨a₁, i₁⟩
    rcases hp₂ : e_ω.symm j₂ with ⟨a₂, i₂⟩
    have ha : a₁ = a₂ := by
      have h1 : owner j₁ = a₁ := congrArg Sigma.fst hp₁
      have h2 : owner j₂ = a₂ := congrArg Sigma.fst hp₂
      exact h1.symm.trans (h_own_eq.trans h2)
    subst ha
    have h_idx₁ : (idx j₁).1 = i₁.1 := congrArg (fun p : Ω_idx => p.2.1) hp₁
    have h_idx₂ : (idx j₂).1 = i₂.1 := congrArg (fun p : Ω_idx => p.2.1) hp₂
    rw [h_idx₁, h_idx₂]
    rw [hp₁, hp₂] at h_ω_lt
    exact ((h_simp a₁).2.lt_iff_lt).mp h_ω_lt
  have h_surj : ∀ (a : Fin K.length) (i : Fin (K.get a).1.length),
      ∃ j : Fin (clusterTotalJumpLength K), ∃ _ : owner j = a, (idx j).1 = i.1 := by
    intro a i
    refine ⟨e_ω ⟨a, i⟩, congrArg Sigma.fst (e_ω.symm_apply_apply ⟨a, i⟩),
      congrArg (fun p : Ω_idx => p.2.1) (e_ω.symm_apply_apply ⟨a, i⟩)⟩
  rcases idx_eq_rankOfOwner_and_card_fiber K owner idx h_mono h_surj with ⟨h_card, h_idx_eq⟩
  have h_own : owner ∈ validShuffleOwnerFinset K :=
    Finset.mem_filter.mpr ⟨Finset.mem_univ _, h_card⟩
  have h_equiv_eq : shuffleSigmaEquivOfOwner h_own = e_ω := by
    refine Equiv.ext fun p => ?_
    rcases p with ⟨a, i⟩
    let j := e_ω ⟨a, i⟩
    let j' := shufflePosOfOwner h_own a i
    change j' = j
    have hj_sym : e_ω.symm j = ⟨a, i⟩ := e_ω.symm_apply_apply ⟨a, i⟩
    have hj_own : owner j = a := congrArg Sigma.fst hj_sym
    have hj_rk : rankOfOwner owner j = i.1 :=
      (h_idx_eq j).symm.trans (congrArg (fun p : Ω_idx => p.2.1) hj_sym)
    have hj'_spec := (shufflePosOfOwner_spec h_own).1 a i
    by_contra h_ne
    rcases lt_or_gt_of_ne h_ne with h_lt | h_gt
    · exact ne_of_lt (rankOfOwner_strictMono_on_fiber owner h_lt (hj'_spec.1.trans hj_own.symm))
        (hj'_spec.2.trans hj_rk.symm)
    · exact ne_of_gt (rankOfOwner_strictMono_on_fiber owner h_gt (hj_own.trans hj'_spec.1.symm))
        (hj'_spec.2.trans hj_rk.symm)
  refine ⟨owner, h_own, h_own, ?_⟩
  rw [h_equiv_eq]
  have h_app : ∀ j : Fin (clusterTotalJumpLength K),
      MeasurableEquiv.piCongrLeft (fun _ : Fin (clusterTotalJumpLength K) => ℝ) e_ω ω j =
        ω (e_ω.symm j) := fun j => by
    have h1 := MeasurableEquiv.piCongrLeft_apply_apply
      (β := fun _ : Fin (clusterTotalJumpLength K) => ℝ) e_ω ω (e_ω.symm j)
    rwa [e_ω.apply_symm_apply] at h1
  refine ⟨fun j => ?_, fun j₁ j₂ h_lt => ?_⟩
  · rw [h_app j]
    rcases e_ω.symm j with ⟨a, i⟩
    exact (h_simp a).1 i
  · rw [h_app j₁, h_app j₂, ← h_e_lt_iff, e_ω.apply_symm_apply, e_ω.apply_symm_apply]
    exact h_lt

private lemma measurable_setIntegral_worldlineTrajectorySyndrome_and_bound
    {L q_code r_0 m_max : ℕ}
    (D_field : Box3D L → LocalCSSDescriptor q_code r_0 m_max)
    (ξ_list : List (WorldlineJumpMonomer L q_code))
    (σ₀ : IdxCSS[L, q_code, m_max] → Bool) (β : ℝ)
    (g : (IdxCSS[L, q_code, m_max] → Bool) → ℝ) :
    Measurable (fun τ : Fin ξ_list.length → ℝ =>
      ∫ t in Set.Icc 0 β, g (worldlineTrajectorySyndrome D_field ξ_list σ₀ τ t)) ∧
    ∃ C : ℝ, 0 ≤ C ∧ ∀ τ : Fin ξ_list.length → ℝ,
      |∫ t in Set.Icc 0 β, g (worldlineTrajectorySyndrome D_field ξ_list σ₀ τ t)| ≤ C := by
  let F_dec : (Fin ξ_list.length → Bool) → ℝ := fun b =>
    g (((List.finRange ξ_list.length).filter b).foldr
      (fun j acc => syndromeXor
        (staticCSSPauliFlip D_field (ξ_list.get j).2.1 (ξ_list.get j).2.2) acc) σ₀)
  have hF_meas : Measurable F_dec := measurable_of_finite F_dec
  let dec_map : (Fin ξ_list.length → ℝ) × ℝ → (Fin ξ_list.length → Bool) :=
    fun p j => decide (p.1 j ≤ p.2)
  have h_dec_meas : Measurable dec_map := by
    refine measurable_pi_iff.mpr fun j => ?_
    have h_le : MeasurableSet {p : (Fin ξ_list.length → ℝ) × ℝ | p.1 j ≤ p.2} :=
      isClosed_le ((continuous_apply j).comp continuous_fst) continuous_snd |>.measurableSet
    have h_eq : (fun p : (Fin ξ_list.length → ℝ) × ℝ => decide (p.1 j ≤ p.2)) =
        fun p => if p ∈ {p : (Fin ξ_list.length → ℝ) × ℝ | p.1 j ≤ p.2} then true else false := by
      ext p; simp
    rw [h_eq]
    exact Measurable.ite h_le measurable_const measurable_const
  have hH_meas : Measurable (fun p : (Fin ξ_list.length → ℝ) × ℝ =>
      g (worldlineTrajectorySyndrome D_field ξ_list σ₀ p.1 p.2)) :=
    hF_meas.comp h_dec_meas
  refine ⟨hH_meas.stronglyMeasurable.integral_prod_right'.measurable, ?_⟩
  let C_g : ℝ := Finset.univ.sup' Finset.univ_nonempty (fun σ' => |g σ'|)
  have hCg_nn : 0 ≤ C_g := le_trans (abs_nonneg (g σ₀))
    (Finset.le_sup' (fun σ' => |g σ'|) (Finset.mem_univ σ₀))
  refine ⟨max 0 β * C_g, mul_nonneg (le_max_left 0 β) hCg_nn, fun τ => ?_⟩
  rcases le_or_gt 0 β with hβ | hβ
  · rw [max_eq_right hβ]
    exact abs_setIntegral_Icc_le_of_abs_le hβ hCg_nn _
      (fun t _ => Finset.le_sup' (fun σ' => |g σ'|) (Finset.mem_univ _))
  · rw [Set.Icc_eq_empty (not_le.mpr hβ), MeasureTheory.Measure.restrict_empty,
      MeasureTheory.integral_zero_measure, abs_zero]
    exact mul_nonneg (le_max_left 0 β) hCg_nn

private lemma measurable_and_bounded_polymerIntegrand
    {L q_code r_0 m_max : ℕ}
    (D_field : Box3D L → LocalCSSDescriptor q_code r_0 m_max)
    (sys : SysCSS[L, q_code, m_max])
    (d_loc : ℕ → Finset (Box3D L) → (IdxCSS[L, q_code, m_max] → Bool) → ℝ)
    (γ : WorldlineDysonPolymer L q_code)
    (σ₀ : IdxCSS[L, q_code, m_max] → Bool) (β : ℝ) :
    Measurable (fun τ : Fin γ.1.length → ℝ =>
      Real.exp (-worldlineBareAction D_field sys γ.1 σ₀ β τ) *
        ∏ ϑ ∈ γ.2, worldlineMayerBondFactor D_field γ.1 d_loc σ₀ β ϑ τ) ∧
    ∃ B : ℝ, 0 ≤ B ∧ ∀ τ : Fin γ.1.length → ℝ,
      |Real.exp (-worldlineBareAction D_field sys γ.1 σ₀ β τ) *
        ∏ ϑ ∈ γ.2, worldlineMayerBondFactor D_field γ.1 d_loc σ₀ β ϑ τ| ≤ B := by
  rcases measurable_setIntegral_worldlineTrajectorySyndrome_and_bound
      D_field γ.1 σ₀ β (fun σ' => sys.syndromeEnergy σ' - sys.syndromeEnergy σ₀) with
    ⟨h_bare_meas, C_bare, _, h_bare_bound⟩
  have h_exp_meas : Measurable (fun τ : Fin γ.1.length → ℝ =>
      Real.exp (-worldlineBareAction D_field sys γ.1 σ₀ β τ)) :=
    Real.measurable_exp.comp h_bare_meas.neg
  have h_mayer : ∀ ϑ : ℕ × Finset (Box3D L),
      Measurable (fun τ : Fin γ.1.length → ℝ =>
        worldlineMayerBondFactor D_field γ.1 d_loc σ₀ β ϑ τ) ∧
      ∃ C_ϑ : ℝ, 0 ≤ C_ϑ ∧ ∀ τ : Fin γ.1.length → ℝ,
        |worldlineMayerBondFactor D_field γ.1 d_loc σ₀ β ϑ τ| ≤ C_ϑ := by
    intro ϑ
    rcases measurable_setIntegral_worldlineTrajectorySyndrome_and_bound
        D_field γ.1 σ₀ β (fun σ' => d_loc ϑ.1 ϑ.2 σ' - d_loc ϑ.1 ϑ.2 σ₀) with
      ⟨h_m_meas, C_m, _, h_m_bound⟩
    refine ⟨(Real.measurable_exp.comp h_m_meas.neg).sub measurable_const,
      Real.exp C_m + 1, by positivity, fun τ => ?_⟩
    unfold worldlineMayerBondFactor
    have h1 : |Real.exp (-∫ t in Set.Icc 0 β,
        (d_loc ϑ.1 ϑ.2 (worldlineTrajectorySyndrome D_field γ.1 σ₀ τ t) - d_loc ϑ.1 ϑ.2 σ₀)) - 1| ≤
        Real.exp (-∫ t in Set.Icc 0 β,
          (d_loc ϑ.1 ϑ.2 (worldlineTrajectorySyndrome D_field γ.1 σ₀ τ t) - d_loc ϑ.1 ϑ.2 σ₀)) + 1 := by
      have := abs_sub (Real.exp (-∫ t in Set.Icc 0 β,
        (d_loc ϑ.1 ϑ.2 (worldlineTrajectorySyndrome D_field γ.1 σ₀ τ t) - d_loc ϑ.1 ϑ.2 σ₀))) 1
      rw [abs_of_pos (Real.exp_pos _), abs_one] at this
      exact this
    have h2 : Real.exp (-∫ t in Set.Icc 0 β,
        (d_loc ϑ.1 ϑ.2 (worldlineTrajectorySyndrome D_field γ.1 σ₀ τ t) - d_loc ϑ.1 ϑ.2 σ₀)) ≤
        Real.exp C_m :=
      Real.exp_le_exp.mpr (le_trans (neg_le_abs _) (h_m_bound τ))
    linarith
  have h_prod_meas : Measurable (fun τ : Fin γ.1.length → ℝ =>
      ∏ ϑ ∈ γ.2, worldlineMayerBondFactor D_field γ.1 d_loc σ₀ β ϑ τ) :=
    Finset.measurable_prod γ.2 (fun ϑ _ => (h_mayer ϑ).1)
  refine ⟨h_exp_meas.mul h_prod_meas,
    Real.exp C_bare * ∏ ϑ ∈ γ.2, Classical.choose (h_mayer ϑ).2,
    mul_nonneg (le_of_lt (Real.exp_pos _))
      (Finset.prod_nonneg fun ϑ _ => (Classical.choose_spec (h_mayer ϑ).2).1),
    fun τ => ?_⟩
  rw [abs_mul, abs_of_pos (Real.exp_pos _), Finset.abs_prod]
  refine mul_le_mul (Real.exp_le_exp.mpr (le_trans (neg_le_abs _) (h_bare_bound τ)))
    (Finset.prod_le_prod₀ (fun _ _ => abs_nonneg _)
      (fun ϑ _ => (Classical.choose_spec (h_mayer ϑ).2).2 τ))
    (Finset.prod_nonneg fun _ _ => abs_nonneg _)
    (le_of_lt (Real.exp_pos _))

private lemma finset_prod_ite_eq_ite_forall {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (P : ι → Prop) [DecidablePred P] (f : ι → ℝ) :
    (∏ a ∈ s, if P a then f a else 0) = if (∀ a ∈ s, P a) then (∏ a ∈ s, f a) else 0 := by
  by_cases h_all : ∀ a ∈ s, P a
  · rw [if_pos h_all]
    exact Finset.prod_congr rfl fun a ha => if_pos (h_all a ha)
  · rw [if_neg h_all]
    push_neg at h_all
    rcases h_all with ⟨a₀, ha₀, hna₀⟩
    exact Finset.prod_eq_zero ha₀ (if_neg hna₀)

private lemma list_prod_map_eq_fin_prod {α : Type*} (l : List α) (f : α → ℝ) :
    (l.map f).prod = ∏ a : Fin l.length, f (l.get a) := by
  rw [Fin.prod_univ_def]
  change (l.map f).prod = ((List.finRange l.length).map (f ∘ l.get)).prod
  rw [← List.map_map, List.map_get_finRange]

/-- **Connected-Component Simplex Shuffle and Bare-Action Factorization** (Part II, Section 3.5 (`subsec:worldline-expansion`), Lemma 3.9 (`lem:worldline-factorization-time-reversal`), Equation `eq:energy-additivity-disjoint-loops`): For any pairwise collar-compatible tuple $\mathcal{K} = (\gamma_1, \dots, \gamma_p)$ of valid worldline polymers, the sum over all shuffle interleavings $\xi$ of the component jump lists $\gamma_1.1, \dots, \gamma_p.1$ of the global ordered Dyson simplex integral with bare action `worldlineBareAction` and Mayer bonds $\Theta = \bigsqcup_{a=1}^p \gamma_a.2$ factorizes into the product of the individual polymer simplex integrals. -/
lemma multiPolymer_shuffle_simplex_integral_factorization_of_compatible
    {L q_code r_0 m_max w_0 R_cut : ℕ} [NeZero L]
    {C_RCA β : ℝ}
    (D_field : Box3D L → LocalCSSDescriptor q_code r_0 m_max)
    (sys : SysCSS[L, q_code, m_max])
    (h_sys_checks : ∀ idx, sys.checkProj idx = staticCSSCheckProj D_field idx ∧
      sys.support idx = staticCSSCheckSupport D_field idx ∧ sys.weight idx = 1)
    (h_geom : sys.IsGeometricallyLocal r_0 w_0)
    (hr0_le : 1 + 4 * (r_0 : ℝ) ≤ C_RCA)
    (hC_RCA : 1 ≤ C_RCA)
    (d_loc : ℕ → Finset (Box3D L) → (IdxCSS[L, q_code, m_max] → Bool) → ℝ)
    (hd_collar : ∀ r ∈ Finset.Icc 1 (min R_cut L), ∀ A ∈ boxCubes 3 L r,
      ∀ σ₁ σ₂, restrictSyndromeToCollar (rcaCollarChecks sys C_RCA r A) σ₁ =
        restrictSyndromeToCollar (rcaCollarChecks sys C_RCA r A) σ₂ →
        d_loc r A σ₁ = d_loc r A σ₂)
    (K : WorldlineUrsellCluster L q_code)
    (hK_valid : ∀ γ ∈ K, IsValidWorldlinePolymer D_field sys C_RCA R_cut γ)
    (hK_pw : K.Pairwise (fun γ₁ γ₂ => ¬ArePolymersIncompatible sys C_RCA γ₁ γ₂))
    (σ : IdxCSS[L, q_code, m_max] → Bool) :
    (∀ ξ_list ∈ multiPolymerShuffleFinset D_field R_cut K,
      ((-1 : ℝ) ^ ξ_list.length) = (K.map (fun γ => (-1 : ℝ) ^ γ.1.length)).prod) ∧
    (∑ ξ_list ∈ multiPolymerShuffleFinset D_field R_cut K,
      ∫ τ : Fin ξ_list.length → ℝ,
        if InOrderedDysonSimplex β τ then
          Real.exp (-worldlineBareAction D_field sys ξ_list σ β τ) *
            ∏ ϑ ∈ K.foldr (fun γ acc => γ.2 ∪ acc) ∅,
              worldlineMayerBondFactor D_field ξ_list d_loc σ β ϑ τ
        else 0) =
    (K.map (fun γ =>
      ∫ τ : Fin γ.1.length → ℝ,
        if InOrderedDysonSimplex β τ then
          Real.exp (-worldlineBareAction D_field sys γ.1 σ β τ) *
            ∏ ϑ ∈ γ.2, worldlineMayerBondFactor D_field γ.1 d_loc σ β ϑ τ
        else 0)).prod := by
  refine ⟨fun ξ_list hξ => ?_, ?_⟩
  · rcases Finset.mem_filter.mp hξ with ⟨h_mem_len, _⟩
    rw [length_eq_of_mem_worldlineJumpListFinsetOfLength D_field R_cut _ h_mem_len]
    exact list_prod_neg_one_pow_length K
  · have h_sys_supp : ∀ idx, sys.support idx = staticCSSCheckSupport D_field idx :=
      fun idx => (h_sys_checks idx).2.1
    rw [sum_multiPolymerShuffleFinset_eq_sum_validShuffleOwnerFinset
      D_field sys h_sys_supp h_geom hr0_le K hK_valid hK_pw,
      list_prod_map_eq_fin_prod]
    let G : ∀ a : Fin K.length, (Fin (K.get a).1.length → ℝ) → ℝ := fun a τ_a =>
      Real.exp (-worldlineBareAction D_field sys (K.get a).1 σ β τ_a) *
        ∏ ϑ ∈ (K.get a).2, worldlineMayerBondFactor D_field (K.get a).1 d_loc σ β ϑ τ_a
    let Ω_idx := Σ a : Fin K.length, Fin (K.get a).1.length
    let Φ : (Ω_idx → ℝ) → ℝ := fun ω => ∏ a : Fin K.length, G a (fun i => ω ⟨a, i⟩)
    have h_term_eq : ∀ owner ∈ validShuffleOwnerFinset K,
        ∀ h_own : owner ∈ validShuffleOwnerFinset K,
        (∫ τ : Fin (shuffleListOfOwner K owner).length → ℝ,
          if InOrderedDysonSimplex β τ then
            Real.exp (-worldlineBareAction D_field sys (shuffleListOfOwner K owner) σ β τ) *
              ∏ ϑ ∈ K.foldr (fun γ acc => γ.2 ∪ acc) ∅,
                worldlineMayerBondFactor D_field (shuffleListOfOwner K owner) d_loc σ β ϑ τ
          else 0) =
        ∫ ω : Ω_idx → ℝ,
          if InOrderedDysonSimplex β
            (MeasurableEquiv.piCongrLeft (fun _ => ℝ) (shuffleSigmaEquivOfOwner h_own) ω) then
            Φ ω
          else 0 := by
      intro owner _ h_own
      have h_len := length_shuffleListOfOwner K owner
      let e_len : (Fin (clusterTotalJumpLength K) → ℝ) ≃ᵐ
          (Fin (shuffleListOfOwner K owner).length → ℝ) :=
        MeasurableEquiv.piCongrLeft (fun _ => ℝ) (finCongr h_len.symm)
      have mp_len : MeasureTheory.MeasurePreserving e_len
          MeasureTheory.volume MeasureTheory.volume :=
        MeasureTheory.measurePreserving_piCongrLeft (fun _ => MeasureTheory.volume)
          (finCongr h_len.symm)
      have h_elen_app : ∀ (τ : Fin (clusterTotalJumpLength K) → ℝ),
          e_len τ = fun j => τ (Fin.cast h_len j) := by
        intro τ; funext j
        have h1 := MeasurableEquiv.piCongrLeft_apply_apply
          (β := fun _ : Fin (shuffleListOfOwner K owner).length => ℝ)
          (finCongr h_len.symm) τ (Fin.cast h_len j)
        exact h1
      have h_simp_cast : ∀ (τ : Fin (clusterTotalJumpLength K) → ℝ),
          InOrderedDysonSimplex β (fun j => τ (Fin.cast h_len j)) ↔ InOrderedDysonSimplex β τ := by
        intro τ
        constructor
        · rintro ⟨h_b, h_sm⟩
          refine ⟨fun j => ?_, fun j₁ j₂ h_lt => ?_⟩
          · simpa using h_b (Fin.cast h_len.symm j)
          · have h_lt' : Fin.cast h_len.symm j₁ < Fin.cast h_len.symm j₂ := h_lt
            simpa using h_sm h_lt'
        · rintro ⟨h_b, h_sm⟩
          refine ⟨fun j => h_b (Fin.cast h_len j), fun j₁ j₂ h_lt => ?_⟩
          have h_lt' : Fin.cast h_len j₁ < Fin.cast h_len j₂ := h_lt
          exact h_sm h_lt'
      rw [← mp_len.integral_comp']
      have h_step1 : ∀ τ : Fin (clusterTotalJumpLength K) → ℝ,
          (if InOrderedDysonSimplex β (e_len τ) then
            Real.exp (-worldlineBareAction D_field sys (shuffleListOfOwner K owner) σ β (e_len τ)) *
              ∏ ϑ ∈ K.foldr (fun γ acc => γ.2 ∪ acc) ∅,
                worldlineMayerBondFactor D_field (shuffleListOfOwner K owner) d_loc σ β ϑ (e_len τ)
          else 0) =
          (if InOrderedDysonSimplex β τ then
            ∏ a : Fin K.length, G a (fun i => τ (shufflePosOfOwner h_own a i))
          else 0) := by
        intro τ
        rw [h_elen_app τ, h_simp_cast τ,
          worldlineBareAction_and_mayerBond_shuffleListOfOwner_eq
            D_field sys h_sys_checks h_geom hr0_le d_loc hd_collar K hK_valid hK_pw h_own σ τ]
      simp_rw [h_step1]
      let e_own : (Ω_idx → ℝ) ≃ᵐ (Fin (clusterTotalJumpLength K) → ℝ) :=
        MeasurableEquiv.piCongrLeft (fun _ => ℝ) (shuffleSigmaEquivOfOwner h_own)
      have mp_own : MeasureTheory.MeasurePreserving e_own
          MeasureTheory.volume MeasureTheory.volume :=
        MeasureTheory.measurePreserving_piCongrLeft (fun _ => MeasureTheory.volume)
          (shuffleSigmaEquivOfOwner h_own)
      rw [← mp_own.integral_comp']
      refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun ω => ?_)
      dsimp only [e_own, Φ]
      split_ifs
      · refine Finset.prod_congr rfl fun a _ => congrArg (G a) (funext fun i => ?_)
        exact MeasurableEquiv.piCongrLeft_apply_apply
          (β := fun _ : Fin (clusterTotalJumpLength K) => ℝ)
          (shuffleSigmaEquivOfOwner h_own) ω ⟨a, i⟩
      · rfl
    rw [← Finset.sum_attach (validShuffleOwnerFinset K)]
    have h_att_congr : ∀ o ∈ (validShuffleOwnerFinset K).attach,
        (∫ τ : Fin (shuffleListOfOwner K o.1).length → ℝ,
          if InOrderedDysonSimplex β τ then
            Real.exp (-worldlineBareAction D_field sys (shuffleListOfOwner K o.1) σ β τ) *
              ∏ ϑ ∈ K.foldr (fun γ acc => γ.2 ∪ acc) ∅,
                worldlineMayerBondFactor D_field (shuffleListOfOwner K o.1) d_loc σ β ϑ τ
          else 0) =
        ∫ ω : Ω_idx → ℝ,
          if InOrderedDysonSimplex β
            (MeasurableEquiv.piCongrLeft (fun _ => ℝ) (shuffleSigmaEquivOfOwner o.2) ω) then
            Φ ω
          else 0 := fun o _ => h_term_eq o.1 o.2 o.2
    rw [Finset.sum_congr rfl h_att_congr]
    have hG_mb : ∀ a : Fin K.length,
        Measurable (G a) ∧ ∃ B_a : ℝ, 0 ≤ B_a ∧ ∀ τ_a : Fin (K.get a).1.length → ℝ, |G a τ_a| ≤ B_a :=
      fun a => measurable_and_bounded_polymerIntegrand D_field sys d_loc (K.get a) σ β
    have hΦ_meas : Measurable Φ := by
      refine Finset.measurable_prod Finset.univ fun a _ => ?_
      exact (hG_mb a).1.comp (measurable_pi_iff.mpr fun i => measurable_pi_apply (⟨a, i⟩ : Ω_idx))
    let B_Φ : ℝ := ∏ a : Fin K.length, Classical.choose (hG_mb a).2
    have hΦ_bound : ∀ ω : Ω_idx → ℝ, ‖Φ ω‖ ≤ B_Φ := by
      intro ω
      rw [Real.norm_eq_abs]
      dsimp [Φ, B_Φ]
      rw [Finset.abs_prod]
      exact Finset.prod_le_prod₀ (fun _ _ => abs_nonneg _)
        (fun a _ => (Classical.choose_spec (hG_mb a).2).2 (fun i => ω ⟨a, i⟩))
    let B_box : Set (Ω_idx → ℝ) := Set.pi Set.univ (fun _ : Ω_idx => Set.Icc 0 β)
    have hB_box_lt : MeasureTheory.volume B_box < ⊤ := by
      dsimp [B_box]
      rw [MeasureTheory.volume_pi_pi]
      refine ENNReal.prod_lt_top fun _ _ => ?_
      rw [Real.volume_Icc]
      exact ENNReal.ofReal_lt_top
    have h_int_o : ∀ o ∈ (validShuffleOwnerFinset K).attach,
        MeasureTheory.Integrable (fun ω : Ω_idx → ℝ =>
          if InOrderedDysonSimplex β
            (MeasurableEquiv.piCongrLeft (fun _ => ℝ) (shuffleSigmaEquivOfOwner o.2) ω) then
            Φ ω
          else 0) := by
      intro o _
      let S_o : Set (Ω_idx → ℝ) :=
        (MeasurableEquiv.piCongrLeft (fun _ => ℝ) (shuffleSigmaEquivOfOwner o.2)) ⁻¹'
          {τ : Fin (clusterTotalJumpLength K) → ℝ | KPOrderedDysonSimplex β τ}
      have hS_o_meas : MeasurableSet S_o :=
        (measurableSet_kpOrderedDysonSimplex β).preimage (MeasurableEquiv.measurable _)
      have hS_o_sub : S_o ⊆ B_box := by
        intro ω hω p _
        rcases p with ⟨a, i⟩
        exact (inOrderedDysonSimplex_piCongrLeft_shuffleSigmaEquiv_imp o.2 hω a).1 i
      have h_vol_lt : MeasureTheory.volume S_o < ⊤ :=
        lt_of_le_of_lt (MeasureTheory.measure_mono hS_o_sub) hB_box_lt
      have h_int_on : MeasureTheory.IntegrableOn Φ S_o MeasureTheory.volume :=
        MeasureTheory.IntegrableOn.of_bound h_vol_lt hΦ_meas.aestronglyMeasurable B_Φ
          (Filter.Eventually.of_forall hΦ_bound)
      have h_ind_eq : (fun ω : Ω_idx → ℝ =>
          if InOrderedDysonSimplex β
            (MeasurableEquiv.piCongrLeft (fun _ => ℝ) (shuffleSigmaEquivOfOwner o.2) ω) then
            Φ ω
          else 0) = S_o.indicator Φ := by
        ext ω
        by_cases h : InOrderedDysonSimplex β
          (MeasurableEquiv.piCongrLeft (fun _ => ℝ) (shuffleSigmaEquivOfOwner o.2) ω)
        · have h' : ω ∈ S_o := h
          rw [if_pos h, Set.indicator_of_mem h']
        · have h' : ω ∉ S_o := h
          rw [if_neg h, Set.indicator_of_notMem h']
      rw [h_ind_eq]
      exact h_int_on.integrable_indicator hS_o_meas
    rw [← MeasureTheory.integral_finset_sum (validShuffleOwnerFinset K).attach h_int_o]
    have h_ae_eq :
        (fun ω : Ω_idx → ℝ =>
          ∑ o ∈ (validShuffleOwnerFinset K).attach,
            if InOrderedDysonSimplex β
              (MeasurableEquiv.piCongrLeft (fun _ => ℝ) (shuffleSigmaEquivOfOwner o.2) ω) then
              Φ ω
            else 0) =ᵐ[MeasureTheory.volume]
        (fun ω : Ω_idx → ℝ =>
          ∏ a : Fin K.length,
            if InOrderedDysonSimplex β (fun i => ω ⟨a, i⟩) then G a (fun i => ω ⟨a, i⟩) else 0) := by
      have h_inj_ae : ∀ᵐ ω : Ω_idx → ℝ ∂MeasureTheory.volume, Function.Injective ω := by
        rw [MeasureTheory.ae_iff]
        exact volume_not_injective_eq_zero
      refine h_inj_ae.mono fun ω h_inj => ?_
      (try dsimp only)
      rw [finset_prod_ite_eq_ite_forall]
      by_cases h_all : ∀ a ∈ (Finset.univ : Finset (Fin K.length)),
          InOrderedDysonSimplex β (fun i => ω ⟨a, i⟩)
      · rw [if_pos h_all]
        have h_all' : ∀ a : Fin K.length, InOrderedDysonSimplex β (fun i => ω ⟨a, i⟩) :=
          fun a => h_all a (Finset.mem_univ a)
        rcases exists_owner_inOrderedDysonSimplex_of_injective K h_inj h_all' with
          ⟨owner₀, _, h_own₀, h_simp₀⟩
        rw [Finset.sum_eq_single ⟨owner₀, h_own₀⟩]
        · rw [if_pos h_simp₀]
        · intro o _ h_ne
          rw [if_neg]
          intro h_simp_o
          apply h_ne
          ext1
          exact owner_eq_of_inOrderedDysonSimplex_piCongrLeft o.2 h_own₀ h_simp_o h_simp₀
        · intro h_not
          exact False.elim (h_not (Finset.mem_attach _ ⟨owner₀, h_own₀⟩))
      · rw [if_neg h_all]
        refine Finset.sum_eq_zero fun o _ => if_neg fun h_simp_o => h_all fun a _ =>
          inOrderedDysonSimplex_piCongrLeft_shuffleSigmaEquiv_imp o.2 h_simp_o a
    rw [MeasureTheory.integral_congr_ae h_ae_eq]
    exact integral_sigma_pi_prod_eq_prod K.length (fun a => (K.get a).1.length)
      (fun a τ_a => if InOrderedDysonSimplex β τ_a then G a τ_a else 0)

def MonomerStepRel {L q_code m_max : ℕ} [NeZero L]
    (sys : SysCSS[L, q_code, m_max]) (C_RCA : ℝ)
    (M : Finset (ℕ × Finset (Box3D L))) (u v : ℕ × Finset (Box3D L)) : Prop :=
  u ∈ M ∧ v ∈ M ∧ u ≠ v ∧
    ¬Disjoint (rcaCollarChecks sys C_RCA u.1 u.2) (rcaCollarChecks sys C_RCA v.1 v.2)

private lemma monomerStepRel_symm {L q_code m_max : ℕ} [NeZero L]
    (sys : SysCSS[L, q_code, m_max]) (C_RCA : ℝ) (M : Finset (ℕ × Finset (Box3D L)))
    {u v : ℕ × Finset (Box3D L)} (h : MonomerStepRel sys C_RCA M u v) :
    MonomerStepRel sys C_RCA M v u :=
  ⟨h.2.1, h.1, h.2.2.1.symm, fun h_disj => h.2.2.2 h_disj.symm⟩

private lemma reflTransGen_monomerStepRel_symm {L q_code m_max : ℕ} [NeZero L]
    (sys : SysCSS[L, q_code, m_max]) (C_RCA : ℝ) (M : Finset (ℕ × Finset (Box3D L)))
    {u v : ℕ × Finset (Box3D L)}
    (h : Relation.ReflTransGen (MonomerStepRel sys C_RCA M) u v) :
    Relation.ReflTransGen (MonomerStepRel sys C_RCA M) v u := by
  induction h with
  | refl => exact .refl
  | tail _ hbc ih => exact (Relation.ReflTransGen.single (monomerStepRel_symm sys C_RCA M hbc)).trans ih

def monomerConnComp {L q_code m_max : ℕ} [NeZero L]
    (sys : SysCSS[L, q_code, m_max]) (C_RCA : ℝ)
    (M : Finset (ℕ × Finset (Box3D L))) (p : ℕ × Finset (Box3D L)) :
    Finset (ℕ × Finset (Box3D L)) :=
  M.filter (fun q => Relation.ReflTransGen (MonomerStepRel sys C_RCA M) p q)

def monomerComponents {L q_code m_max : ℕ} [NeZero L]
    (sys : SysCSS[L, q_code, m_max]) (C_RCA : ℝ)
    (M : Finset (ℕ × Finset (Box3D L))) : Finset (Finset (ℕ × Finset (Box3D L))) :=
  M.image (monomerConnComp sys C_RCA M)

lemma monomerConnComp_properties {L q_code m_max : ℕ} [NeZero L]
    (sys : SysCSS[L, q_code, m_max]) (C_RCA : ℝ) (M : Finset (ℕ × Finset (Box3D L))) :
    (∀ p ∈ M, p ∈ monomerConnComp sys C_RCA M p) ∧
    (∀ p, monomerConnComp sys C_RCA M p ⊆ M) ∧
    (∀ p q, q ∈ monomerConnComp sys C_RCA M p →
      monomerConnComp sys C_RCA M q = monomerConnComp sys C_RCA M p) ∧
    (∀ C ∈ monomerComponents sys C_RCA M,
      C.Nonempty ∧ C ⊆ M ∧
      KPIsConnectedSubgraph
        (fun p q => p ≠ q ∧ ¬Disjoint (rcaCollarChecks sys C_RCA p.1 p.2)
          (rcaCollarChecks sys C_RCA q.1 q.2)) C ∧
      ∀ p ∈ C, monomerConnComp sys C_RCA M p = C) ∧
    (∀ C₁ ∈ monomerComponents sys C_RCA M, ∀ C₂ ∈ monomerComponents sys C_RCA M,
      C₁ ≠ C₂ → Disjoint C₁ C₂ ∧
      ∀ u ∈ C₁, ∀ v ∈ C₂,
        Disjoint (rcaCollarChecks sys C_RCA u.1 u.2) (rcaCollarChecks sys C_RCA v.1 v.2)) := by
  have h_self : ∀ p ∈ M, p ∈ monomerConnComp sys C_RCA M p :=
    fun p hp => Finset.mem_filter.mpr ⟨hp, Relation.ReflTransGen.refl⟩
  have h_sub : ∀ p, monomerConnComp sys C_RCA M p ⊆ M := fun p => Finset.filter_subset _ M
  have h_eq : ∀ p q, q ∈ monomerConnComp sys C_RCA M p →
      monomerConnComp sys C_RCA M q = monomerConnComp sys C_RCA M p := by
    intro p q hq
    have h_pq := (Finset.mem_filter.mp hq).2
    have h_qp := reflTransGen_monomerStepRel_symm sys C_RCA M h_pq
    ext x; simp only [monomerConnComp, Finset.mem_filter]
    exact ⟨fun ⟨hx, h_qx⟩ => ⟨hx, h_pq.trans h_qx⟩, fun ⟨hx, h_px⟩ => ⟨hx, h_qp.trans h_px⟩⟩
  refine ⟨h_self, h_sub, h_eq, ?_, ?_⟩
  · intro C hC
    rcases Finset.mem_image.mp hC with ⟨p, hp, rfl⟩
    have h_ne : (monomerConnComp sys C_RCA M p).Nonempty := ⟨p, h_self p hp⟩
    have h_path_lift : ∀ x y,
        Relation.ReflTransGen (MonomerStepRel sys C_RCA M) x y →
        x ∈ monomerConnComp sys C_RCA M p →
        Relation.ReflTransGen (MonomerStepRel sys C_RCA (monomerConnComp sys C_RCA M p)) x y ∧
        y ∈ monomerConnComp sys C_RCA M p := by
      intro x y h_xy
      induction h_xy with
      | refl => intro hx; exact ⟨Relation.ReflTransGen.refl, hx⟩
      | tail h_ab h_bc ih =>
        intro hx; rcases ih hx with ⟨h_path_ab, hb_in⟩
        have h_pb := (Finset.mem_filter.mp hb_in).2
        have hc_in : _ ∈ monomerConnComp sys C_RCA M p :=
          Finset.mem_filter.mpr ⟨h_bc.2.1, Relation.ReflTransGen.tail h_pb h_bc⟩
        have h_step_C : MonomerStepRel sys C_RCA (monomerConnComp sys C_RCA M p) _ _ :=
          ⟨hb_in, hc_in, h_bc.2.2.1, h_bc.2.2.2⟩
        exact ⟨Relation.ReflTransGen.tail h_path_ab h_step_C, hc_in⟩
    refine ⟨h_ne, h_sub p, ⟨h_ne, fun u hu v hv => ?_⟩, fun q hq => h_eq p q hq⟩
    have h_uv := (reflTransGen_monomerStepRel_symm sys C_RCA M (Finset.mem_filter.mp hu).2).trans
      (Finset.mem_filter.mp hv).2
    exact (h_path_lift u v h_uv hu).1
  · intro C₁ hC₁ C₂ hC₂ h_ne
    rcases Finset.mem_image.mp hC₁ with ⟨p₁, _, rfl⟩
    rcases Finset.mem_image.mp hC₂ with ⟨p₂, _, rfl⟩
    have h_disj : Disjoint (monomerConnComp sys C_RCA M p₁) (monomerConnComp sys C_RCA M p₂) := by
      refine Finset.disjoint_left.mpr fun x hx₁ hx₂ => h_ne ?_
      rw [← h_eq p₁ x hx₁, ← h_eq p₂ x hx₂]
    refine ⟨h_disj, fun u hu v hv => ?_⟩
    by_contra h_not_disj
    have huv_ne : u ≠ v := fun h => Finset.disjoint_left.mp h_disj hu (h ▸ hv)
    have h_step : MonomerStepRel sys C_RCA M u v :=
      ⟨h_sub p₁ hu, h_sub p₂ hv, huv_ne, h_not_disj⟩
    have h_p₁v := Relation.ReflTransGen.tail (Finset.mem_filter.mp hu).2 h_step
    exact Finset.disjoint_left.mp h_disj (Finset.mem_filter.mpr ⟨h_sub p₂ hv, h_p₁v⟩) hv

lemma sum_filter_length_eq_length_of_partition {α : Type*} {p : ℕ}
    (P : Fin p → α → Bool) (l : List α)
    (h_ex : ∀ x ∈ l, ∃ a : Fin p, P a x = true)
    (h_uniq : ∀ x ∈ l, ∀ a b : Fin p, P a x = true → P b x = true → a = b) :
    (∑ a : Fin p, (l.filter (P a)).length) = l.length := by
  induction l with
  | nil => simp
  | cons hd tl ih =>
    rcases h_ex hd List.mem_cons_self with ⟨a₀, ha₀⟩
    have h_step : ∀ a : Fin p, ((hd :: tl).filter (P a)).length =
        (tl.filter (P a)).length + if a = a₀ then 1 else 0 := fun a => by
      rw [List.filter_cons]
      by_cases ha : a = a₀
      · subst ha; rw [if_pos ha₀, if_pos rfl, List.length_cons]
      · have h_false : P a hd = false := by
          cases h_val : P a hd
          · rfl
          · exact False.elim (ha (h_uniq hd List.mem_cons_self a a₀ h_val ha₀))
        rw [h_false, if_neg (by decide), if_neg ha, add_zero]
    simp_rw [h_step]
    rw [Finset.sum_add_distrib, ih (fun x hx => h_ex x (List.mem_cons_of_mem hd hx))
      (fun x hx => h_uniq x (List.mem_cons_of_mem hd hx)),
      Finset.sum_ite_eq' Finset.univ a₀, if_pos (Finset.mem_univ a₀), List.length_cons]

lemma filter_exists_strictMono_surj {α : Type*} (q : α → Bool) (l : List α) :
    ∃ (idx : Fin l.length → ℕ),
      (∀ j : Fin l.length, q (l[j.1]) = true →
        ∃ h : idx j < (l.filter q).length, l[j.1] = (l.filter q)[idx j]'h) ∧
      (∀ j₁ j₂ : Fin l.length, j₁ < j₂ → q (l[j₁.1]) = true → q (l[j₂.1]) = true →
        idx j₁ < idx j₂) ∧
      (∀ i : Fin (l.filter q).length, ∃ j : Fin l.length, q (l[j.1]) = true ∧ idx j = i.1) := by
  induction l with
  | nil => exact ⟨Fin.elim0, fun j => Fin.elim0 j, fun j₁ => Fin.elim0 j₁, fun i => Fin.elim0 i⟩
  | cons hd tl ih =>
    rcases ih with ⟨idx_tl, h_eq_tl, h_mono_tl, h_surj_tl⟩
    by_cases hq : q hd = true
    · refine ⟨Fin.cases 0 (fun j => idx_tl j + 1), ?_, ?_, ?_⟩
      · intro j; refine Fin.cases (fun _ => ⟨by simp [List.filter_cons, hq], by simp [List.filter_cons, hq]⟩)
          (fun j' hj' => ?_) j
        rcases h_eq_tl j' hj' with ⟨h_lt, h_val⟩
        exact ⟨by simp [List.filter_cons, hq]; omega, by simpa [List.filter_cons, hq] using h_val⟩
      · intro j₁ j₂
        refine Fin.cases ?_ (fun j₁' => ?_) j₁ <;> refine Fin.cases ?_ (fun j₂' => ?_) j₂ <;> intro h_lt
        · exact False.elim (lt_irrefl _ h_lt)
        · intro _ _; simp
        · exact False.elim (not_lt_of_gt (Fin.succ_pos j₁') h_lt)
        · intro hj₁' hj₂'
          simpa using Nat.succ_lt_succ (h_mono_tl j₁' j₂' (Fin.succ_lt_succ_iff.mp h_lt) hj₁' hj₂')
      · intro i
        have h_flt_len : ((hd :: tl).filter q).length = (tl.filter q).length + 1 := by
          simp [List.filter_cons, hq]
        rcases Fin.cases (motive := fun k : Fin ((tl.filter q).length + 1) =>
            ∃ j : Fin (hd :: tl).length, q ((hd :: tl)[j.1]) = true ∧
              (Fin.cases 0 (fun j' => idx_tl j' + 1) : Fin (tl.length + 1) → ℕ) j = k.1)
          ⟨⟨0, Nat.succ_pos _⟩, hq, rfl⟩
          (fun i' => by
            rcases h_surj_tl i' with ⟨j', hj'_q, hj'_eq⟩
            exact ⟨j'.succ, hj'_q, by simp [hj'_eq]⟩)
          (i.cast h_flt_len) with ⟨j, hj_q, hj_eq⟩
        exact ⟨j, hj_q, hj_eq⟩
    · have hq_f : q hd = false := Bool.eq_false_iff.mpr hq
      refine ⟨Fin.cases 0 (fun j => idx_tl j), ?_, ?_, ?_⟩
      · intro j; refine Fin.cases (fun h_abs => False.elim (hq h_abs)) (fun j' hj' => ?_) j
        rcases h_eq_tl j' hj' with ⟨h_lt, h_val⟩
        exact ⟨by simpa [List.filter_cons, hq_f] using h_lt, by simpa [List.filter_cons, hq_f] using h_val⟩
      · intro j₁ j₂
        refine Fin.cases ?_ (fun j₁' => ?_) j₁ <;> refine Fin.cases ?_ (fun j₂' => ?_) j₂ <;> intro h_lt
        · intro h_abs; exact False.elim (hq h_abs)
        · intro h_abs; exact False.elim (hq h_abs)
        · exact False.elim (not_lt_of_gt (Fin.succ_pos j₁') h_lt)
        · intro hj₁' hj₂'; simpa using h_mono_tl j₁' j₂' (Fin.succ_lt_succ_iff.mp h_lt) hj₁' hj₂'
      · intro i
        have h_flt_len : ((hd :: tl).filter q).length = (tl.filter q).length := by
          simp [List.filter_cons, hq_f]
        rcases h_surj_tl (i.cast h_flt_len) with ⟨j', hj'_q, hj'_eq⟩
        exact ⟨j'.succ, hj'_q, hj'_eq⟩

lemma mem_multiPolymerShuffleFinset_of_filter_partition
    {L q_code r_0 m_max R_cut m : ℕ}
    (D_field : Box3D L → LocalCSSDescriptor q_code r_0 m_max)
    (K : WorldlineUrsellCluster L q_code) (ξ_list : List (WorldlineJumpMonomer L q_code))
    (hξ_mem : ξ_list ∈ worldlineJumpListFinsetOfLength D_field R_cut m)
    (P : Fin K.length → WorldlineJumpMonomer L q_code → Bool)
    (h_ex : ∀ ξ ∈ ξ_list, ∃ a : Fin K.length, P a ξ = true)
    (h_uniq : ∀ ξ ∈ ξ_list, ∀ a b : Fin K.length, P a ξ = true → P b ξ = true → a = b)
    (h_flt : ∀ a : Fin K.length, (K.get a).1 = ξ_list.filter (P a)) :
    (K.map (fun γ => γ.1.length)).sum = m ∧ ξ_list ∈ multiPolymerShuffleFinset D_field R_cut K := by
  have h_len_ξ := length_eq_of_mem_worldlineJumpListFinsetOfLength D_field R_cut m hξ_mem
  have h_sum_len : (K.map (fun γ => γ.1.length)).sum = m := by
    have h_ofFn : K.map (fun γ => γ.1.length) =
        List.ofFn (fun a : Fin K.length => ((ξ_list.filter (P a)).length)) := by
      refine List.ext_getElem (by simp) fun i h1 h2 => ?_
      rw [List.getElem_map, List.getElem_ofFn, ← h_flt ⟨i, by simpa using h1⟩]; rfl
    rw [h_ofFn, List.sum_ofFn, sum_filter_length_eq_length_of_partition P ξ_list h_ex h_uniq, h_len_ξ]
  refine ⟨h_sum_len, Finset.mem_filter.mpr ⟨h_sum_len.symm ▸ hξ_mem, ?_⟩⟩
  let M := (K.map (fun γ => γ.1.length)).sum
  have hM : ξ_list.length = M := h_len_ξ.trans h_sum_len.symm
  choose owner_fn h_owner_fn using fun j : Fin M =>
    h_ex (ξ_list[j.1]'(by omega)) (List.getElem_mem (by omega))
  choose idx_fn h_idx_eq h_idx_mono h_idx_surj using fun a : Fin K.length =>
    filter_exists_strictMono_surj (P a) ξ_list
  have h_own_iff : ∀ (j : Fin M) (a : Fin K.length),
      P a (ξ_list[j.1]'(by omega)) = true ↔ owner_fn j = a := fun j a =>
    ⟨fun ha => h_uniq _ (List.getElem_mem _) _ _ (h_owner_fn j) ha, by rintro rfl; exact h_owner_fn j⟩
  let idx : ∀ j : Fin M, Fin (K.get (owner_fn j)).1.length := fun j =>
    let j' : Fin ξ_list.length := j.cast hM.symm
    ⟨idx_fn (owner_fn j) j', by rw [h_flt (owner_fn j)]; exact (h_idx_eq (owner_fn j) j' (h_owner_fn j)).1⟩
  refine ⟨owner_fn, idx, fun j₁ j₂ h_lt h_eq => ?_, fun a i => ?_, fun j => ?_⟩
  · dsimp [idx]; rw [← h_eq]
    exact h_idx_mono (owner_fn j₁) (j₁.cast hM.symm) (j₂.cast hM.symm) h_lt
      (h_owner_fn j₁) ((h_own_iff j₂ (owner_fn j₁)).mpr h_eq.symm)
  · rcases h_idx_surj a ⟨i.1, by rw [← h_flt a]; exact i.2⟩ with ⟨j', hj'_P, hj'_eq⟩
    let j : Fin M := j'.cast hM
    have h_own : owner_fn j = a := (h_own_iff j a).mp hj'_P
    exact ⟨j, h_own, by dsimp [idx]; rw [h_own]; exact hj'_eq⟩
  · let j' : Fin ξ_list.length := j.cast hM.symm
    rcases h_idx_eq (owner_fn j) j' (h_owner_fn j) with ⟨h_lt, h_val⟩
    have hj_lt : j.1 < ξ_list.length := j'.2
    change ξ_list.getD j.1 default = (K.get (owner_fn j)).1[(idx j).1]'(idx j).2
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj_lt, Option.getD_some]
    exact h_val.trans (by congr 1; exact (h_flt (owner_fn j)).symm)

lemma worldlineJumpListFlip_filter_eq_of_false_outside
    {L q_code r_0 m_max : ℕ}
    (D_field : Box3D L → LocalCSSDescriptor q_code r_0 m_max)
    (l : List (WorldlineJumpMonomer L q_code)) (q : WorldlineJumpMonomer L q_code → Bool)
    (c : IdxCSS[L, q_code, m_max])
    (h_out : ∀ ξ ∈ l, q ξ = false → staticCSSPauliFlip D_field ξ.2.1 ξ.2.2 c = false) :
    worldlineJumpListFlip D_field (l.filter q) c = worldlineJumpListFlip D_field l c := by
  induction l with
  | nil => rfl
  | cons hd tl ih =>
    rw [List.filter_cons]
    have ih' := ih (fun ξ hξ => h_out ξ (List.mem_cons_of_mem hd hξ))
    by_cases hq : q hd = true
    · rw [if_pos hq]
      change bne (staticCSSPauliFlip D_field hd.2.1 hd.2.2 c) (worldlineJumpListFlip D_field (tl.filter q) c) =
        bne (staticCSSPauliFlip D_field hd.2.1 hd.2.2 c) (worldlineJumpListFlip D_field tl c)
      rw [ih']
    · rw [if_neg hq, ih']
      change worldlineJumpListFlip D_field tl c =
        bne (staticCSSPauliFlip D_field hd.2.1 hd.2.2 c) (worldlineJumpListFlip D_field tl c)
      rw [h_out hd List.mem_cons_self (Bool.eq_false_iff.mpr hq), Bool.false_bne]

def validClosedJumpListFinset
    {L q_code r_0 m_max : ℕ}
    (D_field : Box3D L → LocalCSSDescriptor q_code r_0 m_max) (R_cut m : ℕ) :
    Finset (List (WorldlineJumpMonomer L q_code)) :=
  (worldlineJumpListFinsetOfLength D_field R_cut m).filter (fun ξ_list =>
    2 ≤ ξ_list.length ∧
    staticCSSPauliFlip D_field (worldlinePolymerLoopX (ξ_list, ∅))
      (worldlinePolymerLoopZ (ξ_list, ∅)) = (fun _ => false))

def connMayerFinset
    {L q_code m_max : ℕ} [NeZero L]
    (sys : SysCSS[L, q_code, m_max]) (C_RCA : ℝ) (R_cut : ℕ)
    (ξ_list : List (WorldlineJumpMonomer L q_code)) :
    Finset (Finset (ℕ × Finset (Box3D L))) :=
  (worldlineScaleCubeFinset L R_cut).powerset.filter (fun Θ =>
    ∀ C ∈ monomerComponents sys C_RCA ((ξ_list.map Prod.fst).toFinset ∪ Θ),
      ∃ ξ ∈ ξ_list, ξ.1 ∈ C)

def componentPolymer
    {L q_code : ℕ}
    (ξ_list : List (WorldlineJumpMonomer L q_code))
    (Θ C : Finset (ℕ × Finset (Box3D L))) : WorldlineDysonPolymer L q_code :=
  (ξ_list.filter (fun ξ => decide (ξ.1 ∈ C)), Θ ∩ C)

lemma rcaCollarChecks_nonempty_of_mem_worldlinePolymerMonomers
    {L q_code r_0 m_max w_0 R_cut : ℕ} [NeZero L] {C_RCA : ℝ}
    (D_field : Box3D L → LocalCSSDescriptor q_code r_0 m_max)
    (sys : SysCSS[L, q_code, m_max])
    (h_sys_supp : ∀ idx, sys.support idx = staticCSSCheckSupport D_field idx)
    (h_geom : sys.IsGeometricallyLocal r_0 w_0)
    (hr0_le : 1 + 4 * (r_0 : ℝ) ≤ C_RCA)
    {γ : WorldlineDysonPolymer L q_code}
    (hγ : IsValidWorldlinePolymer D_field sys C_RCA R_cut γ)
    {u : ℕ × Finset (Box3D L)} (hu : u ∈ worldlinePolymerMonomers γ) :
    (rcaCollarChecks sys C_RCA u.1 u.2).Nonempty := by
  have h_len2 : 2 ≤ γ.1.length := hγ.2.2.1.1
  let ξ₀ : WorldlineJumpMonomer L q_code := γ.1[0]'(by omega)
  have hξ₀_in : ξ₀ ∈ γ.1 := List.getElem_mem (by omega)
  have hp₀ : ξ₀.1 ∈ worldlinePolymerMonomers γ :=
    Finset.mem_union_left _ (List.mem_toFinset.mpr (List.mem_map_of_mem hξ₀_in))
  have h_path := hγ.2.2.2.2 ξ₀.1 hp₀ u hu
  cases h_path with
  | refl =>
    have h_flip_ne := (hγ.2.1 ξ₀ hξ₀_in).2.1
    have h_ex_c : ∃ c : IdxCSS[L, q_code, m_max],
        staticCSSPauliFlip D_field ξ₀.2.1 ξ₀.2.2 c = true := by
      by_contra! h_all
      apply h_flip_ne; funext c
      cases h_val : staticCSSPauliFlip D_field ξ₀.2.1 ξ₀.2.2 c
      · rfl
      · exact False.elim (h_all c h_val)
    rcases h_ex_c with ⟨c, hc⟩
    rcases mem_scaleCubeFinset_iff.mp (hγ.1 ξ₀.1 hp₀) with ⟨hr, hA⟩
    have hc_int := staticCSSPauliFlip_mem_cubeIntersectingChecks
      D_field sys h_sys_supp ξ₀.1.2 ξ₀.2.1 ξ₀.2.2 (hγ.2.1 ξ₀ hξ₀_in).1 c hc
    exact ⟨c, cubeIntersectingChecks_subset_rcaCollarChecks sys h_geom hr0_le
      (Finset.mem_Icc.mp hr).1 hA hc_int⟩
  | tail _ h_step =>
    rcases Finset.not_disjoint_iff.mp h_step.2.2.2 with ⟨c, _, hc_u⟩
    exact ⟨c, hc_u⟩

lemma componentPolymer_monomers_and_valid
    {L q_code r_0 m_max w_0 R_cut m : ℕ} [NeZero L] {C_RCA : ℝ}
    (D_field : Box3D L → LocalCSSDescriptor q_code r_0 m_max)
    (sys : SysCSS[L, q_code, m_max])
    (h_sys_supp : ∀ idx, sys.support idx = staticCSSCheckSupport D_field idx)
    (h_geom : sys.IsGeometricallyLocal r_0 w_0)
    (hr0_le : 1 + 4 * (r_0 : ℝ) ≤ C_RCA)
    {ξ_list : List (WorldlineJumpMonomer L q_code)}
    (hξ_list : ξ_list ∈ validClosedJumpListFinset D_field R_cut m)
    {Θ : Finset (ℕ × Finset (Box3D L))}
    (hΘ : Θ ∈ connMayerFinset sys C_RCA R_cut ξ_list)
    {C : Finset (ℕ × Finset (Box3D L))}
    (hC : C ∈ monomerComponents sys C_RCA ((ξ_list.map Prod.fst).toFinset ∪ Θ)) :
    worldlinePolymerMonomers (componentPolymer ξ_list Θ C) = C ∧
    IsValidWorldlinePolymer D_field sys C_RCA R_cut (componentPolymer ξ_list Θ C) := by
  let M := (ξ_list.map Prod.fst).toFinset ∪ Θ
  rcases Finset.mem_filter.mp hξ_list with ⟨hξ_mem, hξ_ge2, hξ_closed⟩
  rcases (mem_worldlineJumpListFinsetOfLength_iff_local D_field R_cut m ξ_list).mp hξ_mem with
    ⟨hξ_len, hξ_all⟩
  rcases Finset.mem_filter.mp hΘ with ⟨hΘ_pow, hΘ_conn⟩
  have hΘ_sub : Θ ⊆ worldlineScaleCubeFinset L R_cut := Finset.mem_powerset.mp hΘ_pow
  rcases monomerConnComp_properties sys C_RCA M with
    ⟨hM_self, hM_sub, hM_eq, h_comp_props, h_comp_disj⟩
  rcases h_comp_props C hC with ⟨hC_ne, hC_sub_M, hC_conn, hC_comp_eq⟩
  have hM_sub_sc : M ⊆ worldlineScaleCubeFinset L R_cut := by
    intro p hp
    rcases Finset.mem_union.mp hp with hp_j | hp_m
    · rcases List.mem_map.mp (List.mem_toFinset.mp hp_j) with ⟨ξ, hξ_in, rfl⟩
      exact ((mem_worldlineAllJumpMonomerFinset_iff D_field ξ).mp (hξ_all ξ hξ_in)).1
    · exact hΘ_sub hp_m
  have h_mon_eq : worldlinePolymerMonomers (componentPolymer ξ_list Θ C) = C := by
    ext p
    simp only [worldlinePolymerMonomers, componentPolymer, Finset.mem_union,
      List.mem_toFinset, List.mem_map, List.mem_filter, decide_eq_true_eq, Finset.mem_inter]
    constructor
    · rintro (⟨_, ⟨_, h⟩, rfl⟩ | ⟨_, h⟩) <;> exact h
    · intro hp_C
      rcases Finset.mem_union.mp (hC_sub_M hp_C) with hp_j | hp_m
      · rcases List.mem_map.mp (List.mem_toFinset.mp hp_j) with ⟨ξ, hξ_in, rfl⟩
        exact Or.inl ⟨ξ, ⟨hξ_in, hp_C⟩, rfl⟩
      · exact Or.inr ⟨hp_m, hp_C⟩
  have h_closed_C : worldlineJumpListFlip D_field (componentPolymer ξ_list Θ C).1 = (fun _ => false) := by
    have h_ξ_flip0 : worldlineJumpListFlip D_field ξ_list = (fun _ => false) := by
      rwa [worldlineJumpListFlip_eq_staticCSSPauliFlip_loop D_field (ξ_list, ∅)]
    have h_ξ_rca : ∀ ξ ∈ ξ_list, ∀ c, staticCSSPauliFlip D_field ξ.2.1 ξ.2.2 c = true →
        c ∈ rcaCollarChecks sys C_RCA ξ.1.1 ξ.1.2 := by
      intro ξ hξ_in c hc
      rcases (mem_worldlineAllJumpMonomerFinset_iff D_field ξ).mp (hξ_all ξ hξ_in) with ⟨h_sc, h_jmp⟩
      rcases mem_scaleCubeFinset_iff.mp h_sc with ⟨hr, hA⟩
      have h_supp := (((mem_worldlineScaleCubeJumpFinset_iff_and_injOn D_field ξ.1.1 ξ.1.2).1 ξ).mp h_jmp).2.1
      exact cubeIntersectingChecks_subset_rcaCollarChecks sys h_geom hr0_le (Finset.mem_Icc.mp hr).1 hA
        (staticCSSPauliFlip_mem_cubeIntersectingChecks D_field sys h_sys_supp ξ.1.2 ξ.2.1 ξ.2.2 h_supp c hc)
    funext c; by_cases hc_in : ∃ u ∈ C, c ∈ rcaCollarChecks sys C_RCA u.1 u.2
    · rcases hc_in with ⟨u, hu_C, hc_u⟩
      change worldlineJumpListFlip D_field (ξ_list.filter (fun ξ => decide (ξ.1 ∈ C))) c = false
      rw [worldlineJumpListFlip_filter_eq_of_false_outside D_field ξ_list
        (fun ξ => decide (ξ.1 ∈ C)) c (fun ξ hξ_in h_out => ?_), congrFun h_ξ_flip0 c]
      by_contra h_not_f
      have hc_ξ := h_ξ_rca ξ hξ_in c (Bool.eq_true_of_not_eq_false h_not_f)
      have hξ_M : ξ.1 ∈ M := Finset.mem_union_left _ (List.mem_toFinset.mpr (List.mem_map_of_mem hξ_in))
      let C' := monomerConnComp sys C_RCA M ξ.1
      have hC'_mem : C' ∈ monomerComponents sys C_RCA M := Finset.mem_image.mpr ⟨ξ.1, hξ_M, rfl⟩
      have hξ_C' : ξ.1 ∈ C' := hM_self ξ.1 hξ_M
      have hC_ne_C' : C ≠ C' := fun h_eq_C =>
        Bool.noConfusion (h_out.symm.trans (decide_eq_true (h_eq_C ▸ hξ_C')))
      exact Finset.disjoint_left.mp ((h_comp_disj C hC C' hC'_mem hC_ne_C').2 u hu_C ξ.1 hξ_C') hc_u hc_ξ
    · push_neg at hc_in
      have h_all_f : ∀ l : List (WorldlineJumpMonomer L q_code),
          (∀ ξ ∈ l, staticCSSPauliFlip D_field ξ.2.1 ξ.2.2 c = false) → worldlineJumpListFlip D_field l c = false := by
        intro l; induction l with
        | nil => intro _; rfl
        | cons hd tl ih =>
          intro h_l; change bne (staticCSSPauliFlip D_field hd.2.1 hd.2.2 c) (worldlineJumpListFlip D_field tl c) = false
          rw [h_l hd List.mem_cons_self, ih (fun ξ hξ => h_l ξ (List.mem_cons_of_mem hd hξ)), Bool.false_bne]
      refine h_all_f _ (fun ξ hξ_flt => ?_)
      rcases List.mem_filter.mp hξ_flt with ⟨hξ_in, hξ_C⟩
      by_contra h_not_f
      exact hc_in ξ.1 (of_decide_eq_true hξ_C) (h_ξ_rca ξ hξ_in c (Bool.eq_true_of_not_eq_false h_not_f))
  refine ⟨h_mon_eq, fun p hp => hM_sub_sc (hC_sub_M (h_mon_eq ▸ hp)),
    fun ξ hξ => (((mem_worldlineScaleCubeJumpFinset_iff_and_injOn D_field ξ.1.1 ξ.1.2).1 ξ).mp ((mem_worldlineAllJumpMonomerFinset_iff D_field ξ).mp (hξ_all ξ (List.mem_of_mem_filter hξ))).2).2,
    ⟨?_, ?_⟩, h_mon_eq.symm ▸ hC_conn⟩
  · rcases hΘ_conn C hC with ⟨ξ₀, hξ₀_in, hξ₀_C⟩
    have hξ₀_flt : ξ₀ ∈ (componentPolymer ξ_list Θ C).1 := List.mem_filter.mpr ⟨hξ₀_in, decide_eq_true hξ₀_C⟩
    cases h_l : (componentPolymer ξ_list Θ C).1 with
    | nil => rw [h_l] at hξ₀_flt; exact False.elim (List.not_mem_nil hξ₀_flt)
    | cons ξ₁ tl =>
      cases tl with
      | nil =>
        have hξ₁_in : ξ₁ ∈ ξ_list := List.mem_of_mem_filter (h_l ▸ List.mem_cons_self)
        rcases (mem_worldlineAllJumpMonomerFinset_iff D_field ξ₁).mp (hξ_all ξ₁ hξ₁_in) with ⟨_, h_jmp⟩
        have h_ne := (((mem_worldlineScaleCubeJumpFinset_iff_and_injOn D_field ξ₁.1.1 ξ₁.1.2).1 ξ₁).mp h_jmp).2.2.1
        have h_zero : staticCSSPauliFlip D_field ξ₁.2.1 ξ₁.2.2 = (fun _ => false) := by
          funext c; have hc := congrFun h_closed_C c
          rw [h_l] at hc; dsimp [worldlineJumpListFlip, syndromeXor] at hc; simpa using hc
        exact False.elim (h_ne h_zero)
      | cons _ _ => simp
  · rwa [← worldlineJumpListFlip_eq_staticCSSPauliFlip_loop D_field (componentPolymer ξ_list Θ C)]

lemma list_prod_avg_weightedLoopOp_mul_syndromeProjector_eq_symmetrized
    {L q_code r_0 m_max L_star R_cut : ℕ} [NeZero L] {C_RCA : ℝ} (hC_RCA : 1 ≤ C_RCA)
    (D_field : Box3D L → LocalCSSDescriptor q_code r_0 m_max) (h_valid : ValidDescriptorField D_field)
    (sys : SysCSS[L, q_code, m_max])
    (h_sys_checks : ∀ idx, sys.checkProj idx = staticCSSCheckProj D_field idx ∧
      sys.support idx = staticCSSCheckSupport D_field idx ∧ sys.weight idx = 1)
    (h_tqo1 : SatisfiesTQO1 sys L_star) (h_tqo2 : SatisfiesSectorFilteredLinearTQO2 sys 1 L_star C_RCA)
    (hR_le : R_cut ≤ L_star) (V : QuasiLocalPerturbation 3 L (SiteCSS[L, q_code]))
    (K : WorldlineUrsellCluster L q_code)
    (hK_valid : ∀ γ ∈ K, IsValidWorldlinePolymer D_field sys C_RCA R_cut γ)
    (hK_pw : K.Pairwise (fun γ₁ γ₂ => ¬ArePolymersIncompatible sys C_RCA γ₁ γ₂))
    (h_comm : ∀ ν ∈ syndromeClosedPauliFinset D_field,
      symplecticPauliSign ν (K.map (fun γ => (worldlinePolymerLoopX γ, worldlinePolymerLoopZ γ))).sum = 1)
    {σ₀ : IdxCSS[L, q_code, m_max] → Bool} (hσ₀ : σ₀ ∈ realizableSyndromes D_field) :
    (K.map (fun γ => (1 / 2 : ℂ) •
      (worldlinePolymerWeightedLoopOp D_field sys V γ +
        worldlinePolymerWeightedLoopOp D_field sys V (γ.1.reverse, γ.2)))).prod *
      sys.syndromeProjector σ₀ =
    (K.map (worldlinePolymerSymmetrizedWeightedLoopOp D_field sys C_RCA V)).prod *
      sys.syndromeProjector σ₀ := by
  let avgOp : WorldlineDysonPolymer L q_code → ℬ_CSS[L, q_code] := fun γ => (1 / 2 : ℂ) •
    (worldlinePolymerWeightedLoopOp D_field sys V γ + worldlinePolymerWeightedLoopOp D_field sys V (γ.1.reverse, γ.2))
  let symOp : WorldlineDysonPolymer L q_code → ℬ_CSS[L, q_code] := worldlinePolymerSymmetrizedWeightedLoopOp D_field sys C_RCA V
  let c_γ : WorldlineDysonPolymer L q_code → ℝ := fun γ =>
    worldlinePolymerLoopAmplitude D_field sys C_RCA V γ (restrictSyndromeToCollar (worldlinePolymerNativeCollar sys C_RCA γ) σ₀) *
      spanningSurfaceSign (worldlinePolymerSpanningSurface D_field sys C_RCA γ) σ₀
  let L_γ : WorldlineDysonPolymer L q_code → ℬ_CSS[L, q_code] := fun γ =>
    hermitianPauliZX (worldlinePolymerLogicalCoset D_field sys C_RCA γ).1 (worldlinePolymerLogicalCoset D_field sys C_RCA γ).2
  have h_single : ∀ γ : WorldlineDysonPolymer L q_code, IsValidWorldlinePolymer D_field sys C_RCA R_cut γ →
      avgOp γ * sys.syndromeProjector σ₀ = ((c_γ γ : ℝ) : ℂ) • (sys.syndromeProjector σ₀ * L_γ γ) ∧
      symOp γ * sys.syndromeProjector σ₀ = ((c_γ γ : ℝ) : ℂ) • sys.syndromeProjector σ₀ := by
    intro γ hγ; let μ := worldlinePolymerLogicalCoset D_field sys C_RCA γ
    have hμ_closed := (isSpanningCheckSurfaceForPolymer_of_isValidWorldlinePolymer D_field h_valid sys h_sys_checks γ hγ).1
    have hM_zx : ∃ z₁ : ℂ, hermitianPauliZX μ.1 μ.2 = z₁ • (weylPauliZ μ.1 * weylPauliX μ.2) := by
      unfold hermitianPauliZX; split_ifs <;> [exact ⟨1, (one_smul ℂ _).symm⟩; exact ⟨Complex.I, rfl⟩]
    rcases hM_zx with ⟨z₁, hz₁⟩
    have hL_comm : L_γ γ * sys.syndromeProjector σ₀ = sys.syndromeProjector σ₀ * L_γ γ := by
      change hermitianPauliZX μ.1 μ.2 * sys.syndromeProjector σ₀ = sys.syndromeProjector σ₀ * hermitianPauliZX μ.1 μ.2
      rw [hz₁, clm_smul_mul, clm_mul_smul,
        ((weylPauliZX_comm_checkProj_and_syndromeProjector_of_syndromeClosed D_field sys h_sys_checks hμ_closed).2.1 σ₀).eq]
    have h_avg := (worldlinePolymerWeightedLoopOp_and_loopAmplitude_reverse_eq
      D_field h_valid sys h_sys_checks h_tqo1 h_tqo2 hR_le V γ hγ hσ₀).2.1
    rcases hermitianPauliZX_isSelfAdjoint_and_sq_eq_one μ.1 μ.2 with ⟨hM_sa, hM_sq⟩
    have hM_adj : (hermitianPauliZX μ.1 μ.2)† = hermitianPauliZX μ.1 μ.2 := ContinuousLinearMap.isSelfAdjoint_iff'.mp hM_sa
    refine ⟨by change avgOp γ * sys.syndromeProjector σ₀ = _; rw [h_avg, ← hL_comm], ?_⟩
    calc symOp γ * sys.syndromeProjector σ₀
      _ = (hermitianPauliZX μ.1 μ.2)† * (avgOp γ * sys.syndromeProjector σ₀) := by
          unfold symOp worldlinePolymerSymmetrizedWeightedLoopOp avgOp; dsimp only [μ]
          rw [clm_smul_mul, clm_smul_mul, clm_mul_smul, mul_assoc]
      _ = (hermitianPauliZX μ.1 μ.2)† * (((c_γ γ : ℝ) : ℂ) • (hermitianPauliZX μ.1 μ.2 * sys.syndromeProjector σ₀)) := by rw [h_avg]
      _ = ((c_γ γ : ℝ) : ℂ) • sys.syndromeProjector σ₀ := by rw [clm_mul_smul, ← mul_assoc, hM_adj, hM_sq, one_mul]
  have h_ind : ∀ l : List (WorldlineDysonPolymer L q_code), (∀ γ ∈ l, IsValidWorldlinePolymer D_field sys C_RCA R_cut γ) →
      (l.map avgOp).prod * sys.syndromeProjector σ₀ = (((l.map c_γ).prod : ℝ) : ℂ) • (sys.syndromeProjector σ₀ * (l.map L_γ).prod) ∧
      (l.map symOp).prod * sys.syndromeProjector σ₀ = (((l.map c_γ).prod : ℝ) : ℂ) • sys.syndromeProjector σ₀ := by
    intro l hl; induction l with
    | nil => simp
    | cons hd tl ih =>
      rcases ih (fun γ hγ => hl γ (List.mem_cons_of_mem hd hγ)) with ⟨ih_avg, ih_sym⟩
      rcases h_single hd (hl hd List.mem_cons_self) with ⟨hd_avg, hd_sym⟩
      simp only [List.map_cons, List.prod_cons, Complex.ofReal_mul]
      exact ⟨by rw [mul_assoc, ih_avg, clm_mul_smul, ← mul_assoc (avgOp hd), hd_avg,
        clm_smul_mul, smul_smul, mul_comm ((c_γ hd : ℝ) : ℂ), mul_assoc],
        by rw [mul_assoc, ih_sym, clm_mul_smul, hd_sym, smul_smul, mul_comm ((c_γ hd : ℝ) : ℂ)]⟩
  rcases h_ind K hK_valid with ⟨hK_avg, hK_sym⟩
  have hL_one : (K.map L_γ).prod = 1 :=
    list_prod_hermitianPauliZX_worldlinePolymerLogicalCoset_eq_one hC_RCA D_field h_valid sys h_sys_checks K hK_valid hK_pw
      (sum_worldlinePolymerLogicalCoset_eq_zero_of_all_symplecticPauliSign_eq_one D_field h_valid sys h_sys_checks K hK_valid h_comm)
  rw [hK_avg, hL_one, mul_one, hK_sym]

end DirectWorldlineCluster
end
