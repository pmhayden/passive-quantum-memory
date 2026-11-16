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

import Proofs.KMSSafeSubspaceODE.KMSFourthRootAndPinchedGibbs

open scoped Classical InnerProduct ComplexConjugate BigOperators
open Filter Topology Asymptotics ContinuousLinearMap KMSPinchedGibbs

noncomputable section

/-!
# Dressed Syndrome Projector Resolution and Sector Energy Form Sandwich

Establishes telescoping sum identities for `indexedSingleCubeApproxM` (`indexedSingleCubeApproxM_eq_sum_indexedSingleCubeDiffD`), defines QAC-dressed syndrome projectors (`indexedDressedSyndromeProjector`, `indexedDressedSyndromeSubsetProj`), proves their resolution of the identity (`indexed_dressed_syndrome_resolution`), and derives the dressed sector energy form sandwich (`dressed_sector_energy_sandwich_of_ne_zero`).

## References

* Part I, Section 7.1 (`subsec:single-cube-telescoping`), Proposition 7.2 (`prop:single-cube-telescoping`)
* Part I, Section 7.3 (`subsec:zero-temp-dressed-memory`), Theorem 7.4 (`thm:zero-temp-dressed-memory`)
* Part II, Section 5.2 (`subsec:low-temp-crossover`), Proposition 5.2 (`prop:bhm-relative-form-bound`)
-/

namespace PerturbedThermalBarrier

/-! ## 1. Telescoping Sum Identities & Unconditional Syndrome Collar Difference Bound -/

@[simp] lemma singleCubeApproxM_zero {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    (sys : CommutingProjectorHamiltonian D L Site) (C : ℝ) (u : BoxD D L)
    (X : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site) :
    singleCubeApproxM sys C u 0 X = 0 := by
  simp [singleCubeApproxM]

@[simp] lemma indexedSingleCubeApproxM_zero {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (sys : IndexedCommutingProjectorHamiltonian D L Site ι) (C : ℝ) (u : BoxD D L)
    (X : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site) :
    indexedSingleCubeApproxM sys C u 0 X = 0 := by
  simp [indexedSingleCubeApproxM]

/-- Exact telescoping identity $M_m(u) = \sum_{k=1}^m D_k(u)$ for `IndexedCommutingProjectorHamiltonian`. -/
lemma indexedSingleCubeApproxM_eq_sum_indexedSingleCubeDiffD {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (sys : IndexedCommutingProjectorHamiltonian D L Site ι) (C : ℝ) (u : BoxD D L) (m : ℕ)
    (X : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site) :
    indexedSingleCubeApproxM sys C u m X =
      ∑ k ∈ Finset.Icc 1 m, indexedSingleCubeDiffD sys C u k X := by
  induction m with
  | zero =>
    simp [indexedSingleCubeApproxM]
  | succ m ih =>
    rw [Finset.sum_Icc_succ_top (Nat.succ_le_succ (Nat.zero_le m)), ← ih]
    dsimp [indexedSingleCubeDiffD]
    simp

/-! ## 2. Indexed Commuting-Projector Syndrome Resolution & Dressed Syndrome Sector Projectors -/

private lemma clm_smul_zero_aux {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (c : ℂ) : c • (0 : E →L[ℂ] E) = 0 := by
  ext φ; simp

private lemma clm_commute_smul_left_aux {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (c : ℂ) {A B : E →L[ℂ] E} (h : Commute A B) : Commute (c • A) B := by
  rw [commute_iff_eq, clm_smul_mul, clm_mul_smul, h.eq]

@[reducible] private def synFactorAux {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {ι : Type*} (Q : ι → (H →L[ℂ] H)) (σ : ι → Bool) (i : ι) : H →L[ℂ] H :=
  if σ i then Q i else 1 - Q i

@[reducible] private def listSynProjAux {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {ι : Type*} (Q : ι → (H →L[ℂ] H)) (σ : ι → Bool) (L : List ι) : H →L[ℂ] H :=
  (L.map (synFactorAux Q σ)).prod

private lemma isStarProjection_synFactorAux {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] {ι : Type*} {Q : ι → (H →L[ℂ] H)}
    (h_proj : ∀ i, IsStarProjection (Q i)) (σ : ι → Bool) (i : ι) :
    IsStarProjection (synFactorAux Q σ i) := by
  dsimp [synFactorAux]
  split_ifs
  · exact h_proj i
  · exact (h_proj i).one_sub

private lemma commute_Q_synFactorAux {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {ι : Type*} {Q : ι → (H →L[ℂ] H)} (h_comm : ∀ i₁ i₂, Commute (Q i₁) (Q i₂))
    (σ : ι → Bool) (i₁ i₂ : ι) : Commute (Q i₁) (synFactorAux Q σ i₂) := by
  dsimp [synFactorAux]
  split_ifs
  · exact h_comm i₁ i₂
  · exact commute_one_sub_right (h_comm i₁ i₂)

private lemma commute_synFactorAux_listSynProjAux {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] {ι : Type*} {Q : ι → (H →L[ℂ] H)}
    (h_comm : ∀ i₁ i₂, Commute (Q i₁) (Q i₂))
    (σ₁ σ₂ : ι → Bool) (i : ι) (L : List ι) :
    Commute (synFactorAux Q σ₁ i) (listSynProjAux Q σ₂ L) := by
  dsimp [listSynProjAux]
  apply Commute.list_prod_right
  intro x hx
  rcases List.mem_map.mp hx with ⟨i₂, _, rfl⟩
  dsimp [synFactorAux]
  have hc := h_comm i i₂
  split_ifs
  · exact hc
  · exact commute_one_sub_right hc
  · exact commute_one_sub_left hc
  · exact commute_one_sub_right (commute_one_sub_left hc)

private lemma commute_Q_listSynProjAux {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {ι : Type*} {Q : ι → (H →L[ℂ] H)} (h_comm : ∀ i₁ i₂, Commute (Q i₁) (Q i₂))
    (σ : ι → Bool) (i : ι) (L : List ι) : Commute (Q i) (listSynProjAux Q σ L) := by
  dsimp [listSynProjAux]
  apply Commute.list_prod_right
  intro x hx
  rcases List.mem_map.mp hx with ⟨i₂, _, rfl⟩
  exact commute_Q_synFactorAux h_comm σ i i₂

private lemma isStarProjection_listSynProjAux {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] {ι : Type*} {Q : ι → (H →L[ℂ] H)}
    (h_proj : ∀ i, IsStarProjection (Q i)) (h_comm : ∀ i₁ i₂, Commute (Q i₁) (Q i₂))
    (σ : ι → Bool) (L : List ι) : IsStarProjection (listSynProjAux Q σ L) := by
  induction L with
  | nil => simp [listSynProjAux, IsStarProjection, IsIdempotentElem.one, isSelfAdjoint_iff]
  | cons i₀ L ih =>
    change IsStarProjection (synFactorAux Q σ i₀ * listSynProjAux Q σ L)
    have hP := isStarProjection_synFactorAux h_proj σ i₀
    have hPQ := commute_synFactorAux_listSynProjAux h_comm σ σ i₀ L
    refine ⟨?_, ?_⟩
    · rw [IsIdempotentElem]
      calc (synFactorAux Q σ i₀ * listSynProjAux Q σ L) *
            (synFactorAux Q σ i₀ * listSynProjAux Q σ L)
        _ = (synFactorAux Q σ i₀ * synFactorAux Q σ i₀) *
            (listSynProjAux Q σ L * listSynProjAux Q σ L) := by
          rw [mul_assoc, ← mul_assoc _ (synFactorAux Q σ i₀), hPQ.symm.eq]; simp only [mul_assoc]
        _ = synFactorAux Q σ i₀ * listSynProjAux Q σ L := by
          rw [hP.isIdempotentElem.eq, ih.isIdempotentElem.eq]
    · rw [isSelfAdjoint_iff, star_mul, hP.isSelfAdjoint.star_eq, ih.isSelfAdjoint.star_eq,
        hPQ.symm.eq]

private lemma mul_listSynProjAux_of_mem {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] {ι : Type*} [DecidableEq ι] {Q : ι → (H →L[ℂ] H)}
    (h_proj : ∀ i, IsStarProjection (Q i)) (h_comm : ∀ i₁ i₂, Commute (Q i₁) (Q i₂))
    (σ : ι → Bool) {i : ι} {L : List ι} (hi : i ∈ L) :
    Q i * listSynProjAux Q σ L = if σ i then listSynProjAux Q σ L else 0 := by
  induction L with
  | nil => nomatch hi
  | cons i₀ L ih =>
    change Q i * (synFactorAux Q σ i₀ * listSynProjAux Q σ L) =
      if σ i then synFactorAux Q σ i₀ * listSynProjAux Q σ L else 0
    rcases List.mem_cons.mp hi with rfl | hi_tail
    · rw [← mul_assoc]; dsimp [synFactorAux]
      by_cases hσ : σ i
      · rw [if_pos hσ, if_pos hσ, (h_proj i).isIdempotentElem.eq]
      · rw [if_neg hσ, if_neg hσ, mul_sub, mul_one, (h_proj i).isIdempotentElem.eq,
          sub_self, zero_mul]
    · have h_c := commute_Q_synFactorAux h_comm σ i i₀
      calc Q i * (synFactorAux Q σ i₀ * listSynProjAux Q σ L)
        _ = synFactorAux Q σ i₀ * (Q i * listSynProjAux Q σ L) := by
          rw [← mul_assoc, h_c.eq, mul_assoc]
        _ = if σ i then synFactorAux Q σ i₀ * listSynProjAux Q σ L else 0 := by
          rw [ih hi_tail]; split_ifs <;> simp

private def syndromesOnList {ι : Type*} [DecidableEq ι] : List ι → Finset (ι → Bool)
  | [] => {fun _ => false}
  | i :: L =>
    (syndromesOnList L).image (fun σ => Function.update σ i false) ∪
    (syndromesOnList L).image (fun σ => Function.update σ i true)

private lemma syndromesOnList_false_of_not_mem {ι : Type*} [DecidableEq ι]
    {L : List ι} {σ : ι → Bool} (hσ : σ ∈ syndromesOnList L) {i : ι} (hi : i ∉ L) :
    σ i = false := by
  induction L generalizing σ with
  | nil => rw [syndromesOnList, Finset.mem_singleton] at hσ; subst hσ; rfl
  | cons i₀ L ih =>
    rw [syndromesOnList, Finset.mem_union] at hσ
    have hne : i ≠ i₀ := fun h => hi (h ▸ List.mem_cons_self)
    rcases hσ with h | h <;> {
      rcases Finset.mem_image.mp h with ⟨σ₀, hσ₀, rfl⟩
      rw [Function.update_of_ne hne]
      exact ih hσ₀ (fun hm => hi (List.mem_cons_of_mem _ hm))
    }

private lemma mem_syndromesOnList_of_outside_false {ι : Type*} [DecidableEq ι]
    (L : List ι) (σ : ι → Bool) (h_out : ∀ i, i ∉ L → σ i = false) :
    σ ∈ syndromesOnList L := by
  induction L generalizing σ with
  | nil => rw [syndromesOnList, Finset.mem_singleton]; ext i; exact h_out i (by simp)
  | cons i₀ L ih =>
    rw [syndromesOnList, Finset.mem_union]
    let σ₀ := Function.update σ i₀ false
    have hσ₀ : σ₀ ∈ syndromesOnList L := ih σ₀ (fun i hi => by
      dsimp [σ₀]
      by_cases h : i = i₀
      · subst h; simp
      · rw [Function.update_of_ne h]; exact h_out i (by simp [h, hi]))
    cases h_val : σ i₀
    · left; refine Finset.mem_image.mpr ⟨σ₀, hσ₀, ?_⟩
      ext i; dsimp [σ₀]; by_cases h : i = i₀ <;> [(subst h; simp [h_val]); simp [h]]
    · right; refine Finset.mem_image.mpr ⟨σ₀, hσ₀, ?_⟩
      ext i; dsimp [σ₀]; by_cases h : i = i₀ <;> [(subst h; simp [h_val]); simp [h]]

private lemma sum_syndromesOnList_listSynProjAux {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] {ι : Type*} [DecidableEq ι] (Q : ι → (H →L[ℂ] H))
    {L : List ι} (hL : L.Nodup) :
    (∑ σ ∈ syndromesOnList L, listSynProjAux Q σ L) = 1 := by
  induction L with
  | nil => simp [syndromesOnList, listSynProjAux]
  | cons i L ih =>
    rcases List.nodup_cons.mp hL with ⟨hi_not, hL_nodup⟩
    have h_upd : ∀ σ (b : Bool), listSynProjAux Q (Function.update σ i b) L = listSynProjAux Q σ L :=
      fun σ b => by
        dsimp [listSynProjAux]; congr 1; apply List.map_congr_left; intro i' hi'; dsimp [synFactorAux]
        have hne : i' ≠ i := fun h => hi_not (h ▸ hi')
        rw [Function.update_of_ne hne]
    have h_inj : ∀ b : Bool, Set.InjOn (fun σ : ι → Bool => Function.update σ i b)
        (syndromesOnList L) := by
      intro b σ₁ hσ₁ σ₂ hσ₂ h_eq; ext i'; by_cases hi' : i' = i
      · subst hi'
        rw [syndromesOnList_false_of_not_mem hσ₁ hi_not,
            syndromesOnList_false_of_not_mem hσ₂ hi_not]
      · simpa [Function.update_of_ne hi'] using congr_fun h_eq i'
    rw [syndromesOnList, Finset.sum_union (by
      rw [Finset.disjoint_left]; intro σ hf ht; rcases Finset.mem_image.mp hf with ⟨_, _, rfl⟩
      rcases Finset.mem_image.mp ht with ⟨_, _, h_eq⟩; have := congr_fun h_eq i; simp at this)]
    rw [Finset.sum_image (h_inj false), Finset.sum_image (h_inj true)]
    have hf : ∀ σ ∈ syndromesOnList L,
        listSynProjAux Q (Function.update σ i false) (i :: L) = (1 - Q i) * listSynProjAux Q σ L :=
      fun σ _ => by change synFactorAux Q _ i * listSynProjAux Q _ L = _; rw [h_upd]; dsimp [synFactorAux]; simp
    have ht : ∀ σ ∈ syndromesOnList L,
        listSynProjAux Q (Function.update σ i true) (i :: L) = Q i * listSynProjAux Q σ L :=
      fun σ _ => by change synFactorAux Q _ i * listSynProjAux Q _ L = _; rw [h_upd]; dsimp [synFactorAux]; simp
    rw [Finset.sum_congr rfl hf, Finset.sum_congr rfl ht, ← Finset.mul_sum, ← Finset.mul_sum,
        ← add_mul, sub_add_cancel, one_mul, ih hL_nodup]

/-- Complete syndrome resolution for `IndexedCommutingProjectorHamiltonian`. -/
lemma syndrome_resolution_indexed {D L : ℕ} {Site : BoxD D L → Type}
    [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)] {ι : Type} [Fintype ι] [DecidableEq ι]
    (sys : IndexedCommutingProjectorHamiltonian D L Site ι) :
    sys.syndromeProjector (fun _ => false) = sys.P0 ∧
    (∀ σ : ι → Bool, IsStarProjection (sys.syndromeProjector σ)) ∧
    (∀ σ₁ σ₂ : ι → Bool, σ₁ ≠ σ₂ → sys.syndromeProjector σ₁ * sys.syndromeProjector σ₂ = 0) ∧
    (∑ σ : ι → Bool, sys.syndromeProjector σ) = 1 ∧
    (∀ σ : ι → Bool, sys.H0 * sys.syndromeProjector σ =
      (sys.syndromeEnergy σ : ℂ) • sys.syndromeProjector σ) ∧
    (∀ σ : ι → Bool, ∀ i : ι, sys.checkProj i * sys.syndromeProjector σ =
      if σ i then sys.syndromeProjector σ else 0) ∧
    (∀ σ : ι → Bool, ∀ i : ι, Commute (sys.checkProj i) (sys.syndromeProjector σ)) ∧
    (∀ σ : ι → Bool, Commute sys.H0 (sys.syndromeProjector σ)) := by
  have h_mem : ∀ i : ι, i ∈ (Finset.univ : Finset ι).toList :=
    fun i => Finset.mem_toList.mpr (Finset.mem_univ i)
  have h_abs : ∀ σ i, sys.checkProj i * sys.syndromeProjector σ =
      if σ i then sys.syndromeProjector σ else 0 :=
    fun σ i => mul_listSynProjAux_of_mem sys.is_projector sys.pairwise_commute σ (h_mem i)
  have h_comm_i : ∀ σ i, Commute (sys.checkProj i) (sys.syndromeProjector σ) :=
    fun σ i => commute_Q_listSynProjAux sys.pairwise_commute σ i Finset.univ.toList
  have h_comm_H0 : ∀ σ, Commute sys.H0 (sys.syndromeProjector σ) := by
    intro σ; dsimp [IndexedCommutingProjectorHamiltonian.H0]
    exact Commute.sum_left _ _ _ (fun i _ => clm_commute_smul_left_aux _ (h_comm_i σ i))
  refine ⟨rfl, fun σ => isStarProjection_listSynProjAux sys.is_projector sys.pairwise_commute σ _,
    ?_, ?_, ?_, h_abs, h_comm_i, h_comm_H0⟩
  · intro σ₁ σ₂ hne
    obtain ⟨i, hi_ne⟩ : ∃ i, σ₁ i ≠ σ₂ i := by
      by_contra h_all; push_neg at h_all; exact hne (funext h_all)
    have h1 := h_abs σ₁ i
    have h2 := h_abs σ₂ i
    have hc1 := h_comm_i σ₁ i
    cases hσ₁ : σ₁ i <;> cases hσ₂ : σ₂ i
    · exact False.elim (hi_ne (hσ₁.trans hσ₂.symm))
    · rw [hσ₁, if_neg Bool.false_ne_true] at h1
      rw [hσ₂, if_pos rfl] at h2
      rw [← h2, ← mul_assoc, hc1.symm.eq, h1, zero_mul]
    · rw [hσ₁, if_pos rfl] at h1
      rw [hσ₂, if_neg Bool.false_ne_true] at h2
      rw [← h1, hc1.eq, mul_assoc, h2, mul_zero]
    · exact False.elim (hi_ne (hσ₁.trans hσ₂.symm))
  · have h_univ : syndromesOnList (Finset.univ : Finset ι).toList = Finset.univ := by
      ext σ; simp only [Finset.mem_univ, iff_true]
      exact mem_syndromesOnList_of_outside_false _ σ (fun i hi => False.elim (hi (h_mem i)))
    rw [← h_univ]
    exact sum_syndromesOnList_listSynProjAux sys.checkProj (Finset.nodup_toList _)
  · intro σ
    change (∑ i : ι, (sys.weight i : ℂ) • sys.checkProj i) * sys.syndromeProjector σ = _
    rw [Finset.sum_mul]
    have h_term : ∀ i : ι, ((sys.weight i : ℂ) • sys.checkProj i) * sys.syndromeProjector σ =
        if σ i = true then (sys.weight i : ℂ) • sys.syndromeProjector σ else 0 := fun i => by
      rw [clm_smul_mul, h_abs σ i]; split_ifs <;> [rfl; exact clm_smul_zero_aux _]
    simp_rw [h_term, ← Finset.sum_filter]
    dsimp [IndexedCommutingProjectorHamiltonian.syndromeEnergy]
    rw [← Finset.sum_smul]
    push_cast
    rfl

/-- Dressed syndrome sector projector $\widetilde{\Pi}_\sigma := U \Pi_{\mathrm{syn}}(\sigma) U^\dagger$
    for `IndexedCommutingProjectorHamiltonian`. -/
def indexedDressedSyndromeProjector {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (sys : IndexedCommutingProjectorHamiltonian D L Site ι)
    (U : unitary (ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site))
    (σ : ι → Bool) :
    ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site :=
  U.1 * sys.syndromeProjector σ * U.1†

/-- Dressed syndrome subset projector $\sum_{\sigma \in S} \widetilde{\Pi}_\sigma = U \Pi_{\mathrm{syn}}(S) U^\dagger$. -/
def indexedDressedSyndromeSubsetProj {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (sys : IndexedCommutingProjectorHamiltonian D L Site ι)
    (U : unitary (ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site))
    (S : Finset (ι → Bool)) :
    ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site :=
  ∑ σ ∈ S, indexedDressedSyndromeProjector sys U σ

lemma indexedDressedSyndromeSubsetProj_eq_conj {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (sys : IndexedCommutingProjectorHamiltonian D L Site ι)
    (U : unitary (ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site))
    (S : Finset (ι → Bool)) :
    indexedDressedSyndromeSubsetProj sys U S =
      U.1 * indexedBareFailureProjector sys S * U.1† := by
  dsimp [indexedDressedSyndromeSubsetProj, indexedDressedSyndromeProjector,
    indexedBareFailureProjector]
  rw [Finset.mul_sum, Finset.sum_mul]

/-- Unitary conjugation preserves `hilbertTrace`: $\operatorname{Tr}(U A U^\dagger) = \operatorname{Tr}(A)$. -/
lemma hilbertTrace_conj_unitary {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    (U : unitary (ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site))
    (A : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site) :
    hilbertTrace (U.1 * A * U.1†) = hilbertTrace A := by
  have hU : U.1† * U.1 = 1 := Unitary.coe_star_mul_self U
  rw [hilbertTrace_mul_comm_aux (U.1 * A) (U.1†), ← mul_assoc, hU, one_mul]

/-- Adjoint unitary conjugation preserves `hilbertTrace`: $\operatorname{Tr}(U^\dagger A U) = \operatorname{Tr}(A)$. -/
lemma hilbertTrace_conj_unitary_adj {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    (U : unitary (ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site))
    (A : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site) :
    hilbertTrace (U.1† * A * U.1) = hilbertTrace A := by
  have hU : U.1 * U.1† = 1 := Unitary.coe_mul_star_self U
  rw [hilbertTrace_mul_comm_aux (U.1† * A) U.1, ← mul_assoc, hU, one_mul]

/-- Complete resolution of the identity and eigenvalue algebra for `indexedDressedSyndromeProjector`. -/
theorem indexed_dressed_syndrome_resolution {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (sys : IndexedCommutingProjectorHamiltonian D L Site ι)
    (U : unitary (ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site)) :
    indexedDressedSyndromeProjector sys U (fun _ => false) = indexedDressedGroundProj sys U ∧
    (∀ i : ι, IsStarProjection (indexedDressedCheckOp sys U i)) ∧
    (∀ i j : ι, Commute (indexedDressedCheckOp sys U i) (indexedDressedCheckOp sys U j)) ∧
    (∀ σ : ι → Bool, IsStarProjection (indexedDressedSyndromeProjector sys U σ)) ∧
    (∀ σ₁ σ₂ : ι → Bool, σ₁ ≠ σ₂ →
      indexedDressedSyndromeProjector sys U σ₁ * indexedDressedSyndromeProjector sys U σ₂ = 0) ∧
    (∑ σ : ι → Bool, indexedDressedSyndromeProjector sys U σ) = 1 ∧
    (∀ σ : ι → Bool,
      indexedDressedH0Op sys U * indexedDressedSyndromeProjector sys U σ =
        (sys.syndromeEnergy σ : ℂ) • indexedDressedSyndromeProjector sys U σ) ∧
    (∀ σ : ι → Bool,
      hilbertTrace (indexedDressedSyndromeProjector sys U σ) =
        hilbertTrace (sys.syndromeProjector σ)) := by
  have h_res := syndrome_resolution_indexed sys
  have hU_star_self : U.1† * U.1 = 1 := Unitary.coe_star_mul_self U
  have hU_self_star : U.1 * U.1† = 1 := Unitary.coe_mul_star_self U
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · dsimp [indexedDressedSyndromeProjector, indexedDressedGroundProj]
    rw [h_res.1]
  · intro i
    exact isStarProjection_unitary_conj U (sys.is_projector i)
  · intro i j
    exact commute_unitary_conj U (sys.pairwise_commute i j)
  · intro σ
    exact isStarProjection_unitary_conj U (h_res.2.1 σ)
  · intro σ₁ σ₂ hne
    dsimp [indexedDressedSyndromeProjector]
    calc (U.1 * sys.syndromeProjector σ₁ * U.1†) * (U.1 * sys.syndromeProjector σ₂ * U.1†)
      _ = U.1 * sys.syndromeProjector σ₁ * (U.1† * U.1) * sys.syndromeProjector σ₂ * U.1† := by
        simp only [mul_assoc]
      _ = U.1 * (sys.syndromeProjector σ₁ * sys.syndromeProjector σ₂) * U.1† := by
        rw [hU_star_self, mul_one]; simp only [mul_assoc]
      _ = 0 := by rw [h_res.2.2.1 σ₁ σ₂ hne, mul_zero, zero_mul]
  · dsimp [indexedDressedSyndromeProjector]
    rw [← Finset.sum_mul, ← Finset.mul_sum, h_res.2.2.2.1, mul_one, hU_self_star]
  · intro σ
    dsimp [indexedDressedH0Op, indexedDressedSyndromeProjector]
    calc (U.1 * sys.H0 * U.1†) * (U.1 * sys.syndromeProjector σ * U.1†)
      _ = U.1 * sys.H0 * (U.1† * U.1) * sys.syndromeProjector σ * U.1† := by
        simp only [mul_assoc]
      _ = U.1 * (sys.H0 * sys.syndromeProjector σ) * U.1† := by
        rw [hU_star_self, mul_one]; simp only [mul_assoc]
      _ = U.1 * ((sys.syndromeEnergy σ : ℂ) • sys.syndromeProjector σ) * U.1† := by
        rw [h_res.2.2.2.2.1 σ]
      _ = (sys.syndromeEnergy σ : ℂ) • (U.1 * sys.syndromeProjector σ * U.1†) := by
        rw [clm_mul_smul, clm_smul_mul]
  · intro σ
    exact hilbertTrace_conj_unitary U (sys.syndromeProjector σ)

/-! ## 3. Dressed Sector Excitation Energy Sandwich (`dressed_sector_energy_sandwich_of_ne_zero`) -/

/-- **Dressed Syndrome Sector Excitation Energy Sandwich (`dressed_sector_energy_sandwich_of_ne_zero`)**:
    Under `SatisfiesDressedEnergySandwich sys V U c_shift δ_split`, for every non-zero syndrome
    $\sigma \ne (\text{fun } \_ \Rightarrow \text{false})$ and every state $\phi$ in the dressed
    syndrome sector $\widetilde{\Pi}_\sigma \phi = \phi$:
    1. $\widetilde{P}_0 \phi = 0$ (orthogonality to the dressed ground space);
    2. $\operatorname{Re}\langle \phi, \widetilde{H}_0 \phi \rangle = E_{\mathrm{syn}}(\sigma) \|\phi\|^2$;
    3. $(\frac{3}{4} E_{\mathrm{syn}}(\sigma) - \frac{1}{2} \delta_{\mathrm{split}}) \|\phi\|^2 \le
       \operatorname{Re}\langle \phi, ((H_0 + V_{\mathrm{tot}}) - c_{\mathrm{shift}} \cdot 1) \phi \rangle \le
       (\frac{5}{4} E_{\mathrm{syn}}(\sigma) + \frac{1}{2} \delta_{\mathrm{split}}) \|\phi\|^2$. -/
theorem dressed_sector_energy_sandwich_of_ne_zero {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (sys : IndexedCommutingProjectorHamiltonian D L Site ι)
    (V : QuasiLocalPerturbation D L Site)
    (U : unitary (ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site))
    {c_shift δ_split : ℝ}
    (h_sand : SatisfiesDressedEnergySandwich sys V U c_shift δ_split)
    {σ : ι → Bool} (hσ_ne : σ ≠ (fun _ => false))
    {ϕ : ManyBodyHilbertSpace Site}
    (hϕ : indexedDressedSyndromeProjector sys U σ ϕ = ϕ) :
    indexedDressedGroundProj sys U ϕ = 0 ∧
    RCLike.re (inner ℂ ϕ (indexedDressedH0Op sys U ϕ)) = sys.syndromeEnergy σ * ‖ϕ‖ ^ 2 ∧
    ((3 / 4 : ℝ) * sys.syndromeEnergy σ - (1 / 2 : ℝ) * δ_split) * ‖ϕ‖ ^ 2 ≤
      RCLike.re (inner ℂ ϕ ((sys.H0 + V.totalPerturbation - (c_shift : ℂ) • 1) ϕ)) ∧
    RCLike.re (inner ℂ ϕ ((sys.H0 + V.totalPerturbation - (c_shift : ℂ) • 1) ϕ)) ≤
      ((5 / 4 : ℝ) * sys.syndromeEnergy σ + (1 / 2 : ℝ) * δ_split) * ‖ϕ‖ ^ 2 := by
  have h_res := indexed_dressed_syndrome_resolution sys U
  have hP0_ϕ : indexedDressedGroundProj sys U ϕ = 0 := by
    rw [← h_res.1, ← hϕ]
    change (indexedDressedSyndromeProjector sys U (fun _ => false) *
      indexedDressedSyndromeProjector sys U σ) ϕ = 0
    rw [h_res.2.2.2.2.1 (fun _ => false) σ hσ_ne.symm, ContinuousLinearMap.zero_apply]
  have hH0_ϕ : indexedDressedH0Op sys U ϕ = (sys.syndromeEnergy σ : ℂ) • ϕ := by
    calc indexedDressedH0Op sys U ϕ
      _ = (indexedDressedH0Op sys U * indexedDressedSyndromeProjector sys U σ) ϕ := by
        rw [ContinuousLinearMap.mul_apply, hϕ]
      _ = ((sys.syndromeEnergy σ : ℂ) • indexedDressedSyndromeProjector sys U σ) ϕ := by
        rw [h_res.2.2.2.2.2.2.1 σ]
      _ = (sys.syndromeEnergy σ : ℂ) • ϕ := by
        rw [ContinuousLinearMap.smul_apply, hϕ]
  have h_re_H0 : RCLike.re (inner ℂ ϕ (indexedDressedH0Op sys U ϕ)) =
      sys.syndromeEnergy σ * ‖ϕ‖ ^ 2 := by
    rw [hH0_ϕ, inner_smul_right, re_ofReal_mul, inner_self_eq_norm_sq]
  have h_bounds := h_sand ϕ hP0_ϕ
  rw [h_re_H0] at h_bounds
  unfold bhmSandwichLower bhmSandwichUpper bhmPerturbedGap at h_bounds
  refine ⟨hP0_ϕ, h_re_H0, ?_, ?_⟩
  · linarith [h_bounds.1]
  · linarith [h_bounds.2]

end PerturbedThermalBarrier

end
