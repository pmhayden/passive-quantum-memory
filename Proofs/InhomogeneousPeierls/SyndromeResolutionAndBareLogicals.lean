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

import Proofs.InhomogeneousPeierls.OperatorTQOFromF2TQO
import Defs.SafeSubspaceAndKMS

/-!
# Syndrome Resolution of Identity, Gibbs Partition Trace Formula, and Bare Logical Operators

Proves completeness of orthogonal syndrome projectors (`syndrome_resolution_indexed`) and expands the Gibbs partition function as a Boltzmann-weighted sum of syndrome sector traces (`gibbsPartitionZ_eq_sum_syndromeProjector`). Defines syndrome subset projectors (`syndromeSubsetProj`) and verifies algebra, commutation, and anticommutation properties of bare logical Pauli operators on `bdlInhomogeneousSystem k` (`bdl_bare_logical_props`).

## References

* Part I, Section 5.4 (`subsec:safe-decoded-observables`), Definition 5.6 (`def:safe-decoded-observables`), Proposition 5.7 (`prop:safe-subspace-immunity`)
* Part II, Section 2 (`subsec:setup`), Definition 2.1 (`def:bdl-lattice`), Definition 2.5 (`def:syndrome-safe`)
-/

noncomputable section

open scoped Classical BigOperators InnerProduct ComplexConjugate
open ContinuousLinearMap

set_option linter.constructorNameAsVariable false
set_option maxRecDepth 200000

/-! ## 1. General `IndexedCommutingProjectorHamiltonian` Syndrome Resolution & Spectral Gibbs Trace -/

private lemma clm_smul_zero {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (c : ℂ) : c • (0 : E →L[ℂ] E) = 0 := by
  ext φ; simp

private lemma clm_commute_smul_left {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (c : ℂ) {A B : E →L[ℂ] E} (h : Commute A B) : Commute (c • A) B := by
  rw [commute_iff_eq, clm_smul_mul, clm_mul_smul, h.eq]

@[reducible] def synFactor {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {ι : Type*} (Q : ι → (H →L[ℂ] H)) (σ : ι → Bool) (i : ι) : H →L[ℂ] H :=
  if σ i then Q i else 1 - Q i

@[reducible] def listSynProj {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {ι : Type*} (Q : ι → (H →L[ℂ] H)) (σ : ι → Bool) (L : List ι) : H →L[ℂ] H :=
  (L.map (synFactor Q σ)).prod

private lemma isStarProjection_synFactor {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] {ι : Type*} {Q : ι → (H →L[ℂ] H)}
    (h_proj : ∀ i, IsStarProjection (Q i)) (σ : ι → Bool) (i : ι) :
    IsStarProjection (synFactor Q σ i) := by
  dsimp [synFactor]
  split_ifs
  · exact h_proj i
  · refine ⟨?_, ?_⟩
    · rw [IsIdempotentElem]
      calc (1 - Q i) * (1 - Q i) = 1 - Q i - Q i + Q i * Q i := by noncomm_ring
        _ = 1 - Q i := by rw [(h_proj i).isIdempotentElem.eq]; abel
    · rw [isSelfAdjoint_iff, star_sub, star_one, (h_proj i).isSelfAdjoint.star_eq]

private lemma commute_Q_synFactor {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {ι : Type*} {Q : ι → (H →L[ℂ] H)} (h_comm : ∀ i₁ i₂, Commute (Q i₁) (Q i₂))
    (σ : ι → Bool) (i₁ i₂ : ι) : Commute (Q i₁) (synFactor Q σ i₂) := by
  dsimp [synFactor]
  split_ifs
  · exact h_comm i₁ i₂
  · exact (Commute.one_right (Q i₁)).sub_right (h_comm i₁ i₂)

private lemma commute_synFactor_listSynProj {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {ι : Type*} {Q : ι → (H →L[ℂ] H)} (h_comm : ∀ i₁ i₂, Commute (Q i₁) (Q i₂))
    (σ₁ σ₂ : ι → Bool) (i : ι) (L : List ι) :
    Commute (synFactor Q σ₁ i) (listSynProj Q σ₂ L) := by
  dsimp [listSynProj]
  apply Commute.list_prod_right
  intro x hx
  rcases List.mem_map.mp hx with ⟨i₂, _, rfl⟩
  dsimp [synFactor]
  split_ifs
  · exact h_comm i i₂
  · exact (Commute.one_right (Q i)).sub_right (h_comm i i₂)
  · exact (Commute.one_left (Q i₂)).sub_left (h_comm i i₂)
  · exact ((Commute.one_left _).sub_left (Commute.one_right _)).sub_right
      ((Commute.one_left (Q i₂)).sub_left (h_comm i i₂))

private lemma commute_Q_listSynProj {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {ι : Type*} {Q : ι → (H →L[ℂ] H)} (h_comm : ∀ i₁ i₂, Commute (Q i₁) (Q i₂))
    (σ : ι → Bool) (i : ι) (L : List ι) : Commute (Q i) (listSynProj Q σ L) := by
  dsimp [listSynProj]
  apply Commute.list_prod_right
  intro x hx
  rcases List.mem_map.mp hx with ⟨i₂, _, rfl⟩
  exact commute_Q_synFactor h_comm σ i i₂

private lemma isStarProjection_listSynProj {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] {ι : Type*} {Q : ι → (H →L[ℂ] H)}
    (h_proj : ∀ i, IsStarProjection (Q i)) (h_comm : ∀ i₁ i₂, Commute (Q i₁) (Q i₂))
    (σ : ι → Bool) (L : List ι) : IsStarProjection (listSynProj Q σ L) := by
  induction L with
  | nil =>
    change IsStarProjection 1
    exact ⟨IsIdempotentElem.one, by rw [isSelfAdjoint_iff, star_one]⟩
  | cons i₀ L ih =>
    change IsStarProjection (synFactor Q σ i₀ * listSynProj Q σ L)
    have hP := isStarProjection_synFactor h_proj σ i₀
    have hPQ := commute_synFactor_listSynProj h_comm σ σ i₀ L
    refine ⟨?_, ?_⟩
    · rw [IsIdempotentElem]
      calc (synFactor Q σ i₀ * listSynProj Q σ L) * (synFactor Q σ i₀ * listSynProj Q σ L)
        _ = (synFactor Q σ i₀ * synFactor Q σ i₀) * (listSynProj Q σ L * listSynProj Q σ L) := by
          rw [mul_assoc, ← mul_assoc _ (synFactor Q σ i₀), hPQ.symm.eq]; simp only [mul_assoc]
        _ = synFactor Q σ i₀ * listSynProj Q σ L := by
          rw [hP.isIdempotentElem.eq, ih.isIdempotentElem.eq]
    · rw [isSelfAdjoint_iff, star_mul, hP.isSelfAdjoint.star_eq, ih.isSelfAdjoint.star_eq, hPQ.symm.eq]

private lemma mul_listSynProj_of_mem {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] {ι : Type*} [DecidableEq ι] {Q : ι → (H →L[ℂ] H)}
    (h_proj : ∀ i, IsStarProjection (Q i)) (h_comm : ∀ i₁ i₂, Commute (Q i₁) (Q i₂))
    (σ : ι → Bool) {i : ι} {L : List ι} (hi : i ∈ L) :
    Q i * listSynProj Q σ L = if σ i then listSynProj Q σ L else 0 := by
  induction L with
  | nil => nomatch hi
  | cons i₀ L ih =>
    change Q i * (synFactor Q σ i₀ * listSynProj Q σ L) =
      if σ i then synFactor Q σ i₀ * listSynProj Q σ L else 0
    rcases List.mem_cons.mp hi with rfl | hi_tail
    · rw [← mul_assoc]; dsimp [synFactor]
      by_cases hσ : σ i
      · rw [if_pos hσ, if_pos hσ, (h_proj i).isIdempotentElem.eq]
      · rw [if_neg hσ, if_neg hσ, mul_sub, mul_one, (h_proj i).isIdempotentElem.eq, sub_self, zero_mul]
    · have h_c := commute_Q_synFactor h_comm σ i i₀
      calc Q i * (synFactor Q σ i₀ * listSynProj Q σ L)
        _ = synFactor Q σ i₀ * (Q i * listSynProj Q σ L) := by rw [← mul_assoc, h_c.eq, mul_assoc]
        _ = if σ i then synFactor Q σ i₀ * listSynProj Q σ L else 0 := by
          rw [ih hi_tail]; split_ifs <;> simp

private def syndromesOnListAux {ι : Type*} [DecidableEq ι] : List ι → Finset (ι → Bool)
  | [] => {fun _ => false}
  | i :: L =>
    (syndromesOnListAux L).image (fun σ => Function.update σ i false) ∪
    (syndromesOnListAux L).image (fun σ => Function.update σ i true)

private lemma syndromesOnListAux_false_of_not_mem {ι : Type*} [DecidableEq ι]
    {L : List ι} {σ : ι → Bool} (hσ : σ ∈ syndromesOnListAux L) {i : ι} (hi : i ∉ L) :
    σ i = false := by
  induction L generalizing σ with
  | nil => rw [syndromesOnListAux, Finset.mem_singleton] at hσ; subst hσ; rfl
  | cons i₀ L ih =>
    rw [syndromesOnListAux, Finset.mem_union] at hσ
    have hne : i ≠ i₀ := fun h => hi (h ▸ List.mem_cons_self)
    rcases hσ with h | h <;> {
      rcases Finset.mem_image.mp h with ⟨σ₀, hσ₀, rfl⟩
      rw [Function.update_of_ne hne]
      exact ih hσ₀ (fun hm => hi (List.mem_cons_of_mem _ hm))
    }

private lemma mem_syndromesOnListAux_of_outside_false {ι : Type*} [DecidableEq ι]
    (L : List ι) (σ : ι → Bool) (h_out : ∀ i, i ∉ L → σ i = false) :
    σ ∈ syndromesOnListAux L := by
  induction L generalizing σ with
  | nil => rw [syndromesOnListAux, Finset.mem_singleton]; ext i; exact h_out i (by simp)
  | cons i₀ L ih =>
    rw [syndromesOnListAux, Finset.mem_union]
    let σ₀ := Function.update σ i₀ false
    have hσ₀ : σ₀ ∈ syndromesOnListAux L := ih σ₀ (fun i hi => by
      dsimp [σ₀]
      by_cases h : i = i₀
      · subst h; simp
      · rw [Function.update_of_ne h]; exact h_out i (by simp [h, hi]))
    cases h_val : σ i₀
    · left; refine Finset.mem_image.mpr ⟨σ₀, hσ₀, ?_⟩
      ext i; dsimp [σ₀]; by_cases h : i = i₀ <;> [(subst h; simp [h_val]); simp [h]]
    · right; refine Finset.mem_image.mpr ⟨σ₀, hσ₀, ?_⟩
      ext i; dsimp [σ₀]; by_cases h : i = i₀ <;> [(subst h; simp [h_val]); simp [h]]

private lemma sum_syndromesOnListAux_listSynProj {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] {ι : Type*} [DecidableEq ι] (Q : ι → (H →L[ℂ] H))
    {L : List ι} (hL : L.Nodup) :
    (∑ σ ∈ syndromesOnListAux L, listSynProj Q σ L) = 1 := by
  induction L with
  | nil => simp [syndromesOnListAux, listSynProj]
  | cons i L ih =>
    rcases List.nodup_cons.mp hL with ⟨hi_not, hL_nodup⟩
    have h_upd : ∀ σ (b : Bool), listSynProj Q (Function.update σ i b) L = listSynProj Q σ L :=
      fun σ b => by
        dsimp [listSynProj]; congr 1; apply List.map_congr_left; intro i' hi'; dsimp [synFactor]
        have hne : i' ≠ i := fun h => hi_not (h ▸ hi')
        rw [Function.update_of_ne hne]
    have h_inj : ∀ b : Bool, Set.InjOn (fun σ : ι → Bool => Function.update σ i b)
        (syndromesOnListAux L) := by
      intro b σ₁ hσ₁ σ₂ hσ₂ h_eq; ext i'; by_cases hi' : i' = i
      · subst hi'
        rw [syndromesOnListAux_false_of_not_mem hσ₁ hi_not,
            syndromesOnListAux_false_of_not_mem hσ₂ hi_not]
      · simpa [Function.update_of_ne hi'] using congr_fun h_eq i'
    rw [syndromesOnListAux, Finset.sum_union (by
      rw [Finset.disjoint_left]; intro σ hf ht; rcases Finset.mem_image.mp hf with ⟨_, _, rfl⟩
      rcases Finset.mem_image.mp ht with ⟨_, _, h_eq⟩; have := congr_fun h_eq i; simp at this)]
    rw [Finset.sum_image (h_inj false), Finset.sum_image (h_inj true)]
    have hf : ∀ σ ∈ syndromesOnListAux L,
        listSynProj Q (Function.update σ i false) (i :: L) = (1 - Q i) * listSynProj Q σ L :=
      fun σ _ => by change synFactor Q _ i * listSynProj Q _ L = _; rw [h_upd]; dsimp [synFactor]; simp
    have ht : ∀ σ ∈ syndromesOnListAux L,
        listSynProj Q (Function.update σ i true) (i :: L) = Q i * listSynProj Q σ L :=
      fun σ _ => by change synFactor Q _ i * listSynProj Q _ L = _; rw [h_upd]; dsimp [synFactor]; simp
    rw [Finset.sum_congr rfl hf, Finset.sum_congr rfl ht, ← Finset.mul_sum, ← Finset.mul_sum,
        ← add_mul, sub_add_cancel, one_mul, ih hL_nodup]

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
    fun σ i => mul_listSynProj_of_mem sys.is_projector sys.pairwise_commute σ (h_mem i)
  have h_comm_i : ∀ σ i, Commute (sys.checkProj i) (sys.syndromeProjector σ) :=
    fun σ i => commute_Q_listSynProj sys.pairwise_commute σ i Finset.univ.toList
  have h_comm_H0 : ∀ σ, Commute sys.H0 (sys.syndromeProjector σ) := by
    intro σ; dsimp [IndexedCommutingProjectorHamiltonian.H0]
    exact Commute.sum_left _ _ _ (fun i _ => clm_commute_smul_left _ (h_comm_i σ i))
  refine ⟨rfl, fun σ => isStarProjection_listSynProj sys.is_projector sys.pairwise_commute σ _,
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
  · have h_univ : syndromesOnListAux (Finset.univ : Finset ι).toList = Finset.univ := by
      ext σ; simp only [Finset.mem_univ, iff_true]
      exact mem_syndromesOnListAux_of_outside_false _ σ (fun i hi => False.elim (hi (h_mem i)))
    rw [← h_univ]
    exact sum_syndromesOnListAux_listSynProj sys.checkProj (Finset.nodup_toList _)
  · intro σ
    change (∑ i : ι, (sys.weight i : ℂ) • sys.checkProj i) * sys.syndromeProjector σ = _
    rw [Finset.sum_mul]
    have h_term : ∀ i : ι, ((sys.weight i : ℂ) • sys.checkProj i) * sys.syndromeProjector σ =
        if σ i = true then (sys.weight i : ℂ) • sys.syndromeProjector σ else 0 := fun i => by
      rw [clm_smul_mul, h_abs σ i]; split_ifs <;> [rfl; exact clm_smul_zero _]
    simp_rw [h_term, ← Finset.sum_filter]
    dsimp [IndexedCommutingProjectorHamiltonian.syndromeEnergy]
    rw [← Finset.sum_smul]
    push_cast
    rfl

lemma hilbertTrace_gibbsDensityOp_mul_syndromeProjector {D L : ℕ} {Site : BoxD D L → Type}
    [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)] {ι : Type} [Fintype ι] [DecidableEq ι]
    (sys : IndexedCommutingProjectorHamiltonian D L Site ι) (β : ℝ) (σ : ι → Bool) :
    hilbertTrace (gibbsDensityOp (opEigenbasis sys.H0 sys.isSelfAdjoint_H0)
        (opEigenvalues sys.H0 sys.isSelfAdjoint_H0) β * sys.syndromeProjector σ) =
      (gibbsPartitionZ (opEigenvalues sys.H0 sys.isSelfAdjoint_H0) β)⁻¹ *
        (Real.exp (-β * sys.syndromeEnergy σ) * hilbertTrace (sys.syndromeProjector σ)) := by
  let ψ := opEigenbasis sys.H0 sys.isSelfAdjoint_H0
  let E_eig := opEigenvalues sys.H0 sys.isSelfAdjoint_H0
  have h_res := syndrome_resolution_indexed sys
  have h_P_H0 : sys.syndromeProjector σ * sys.H0 =
      (sys.syndromeEnergy σ : ℂ) • sys.syndromeProjector σ :=
    (h_res.2.2.2.2.2.2.2 σ).symm.eq.trans (h_res.2.2.2.2.1 σ)
  rw [hilbertTrace_gibbsDensityOp_mul_eq ψ E_eig β
    (opEigenbasis_orthonormal sys.H0 sys.isSelfAdjoint_H0)
    (hilbertTrace_eq_sum_opEigenbasis sys.H0 sys.isSelfAdjoint_H0) (sys.syndromeProjector σ)]
  rw [hilbertTrace_eq_sum_opEigenbasis sys.H0 sys.isSelfAdjoint_H0 (sys.syndromeProjector σ)]
  dsimp [gibbsProb]
  simp_rw [mul_assoc]
  rw [← Finset.mul_sum]
  congr 1
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun ω _ => ?_
  let t := RCLike.re (inner ℂ (ψ ω) (sys.syndromeProjector σ (ψ ω)))
  have h1 : (sys.syndromeProjector σ * sys.H0) (ψ ω) =
      (E_eig ω : ℂ) • sys.syndromeProjector σ (ψ ω) := by
    change sys.syndromeProjector σ (sys.H0 (ψ ω)) = _
    rw [opEigenbasis_apply_H sys.H0 sys.isSelfAdjoint_H0 ω, map_smul]
  have h2 : (sys.syndromeProjector σ * sys.H0) (ψ ω) =
      (sys.syndromeEnergy σ : ℂ) • sys.syndromeProjector σ (ψ ω) := by
    rw [h_P_H0, ContinuousLinearMap.smul_apply]
  have h_eq_vec : (E_eig ω : ℂ) • sys.syndromeProjector σ (ψ ω) =
      (sys.syndromeEnergy σ : ℂ) • sys.syndromeProjector σ (ψ ω) := h1.symm.trans h2
  have h_in := congr_arg (fun v => RCLike.re (inner ℂ (ψ ω) v)) h_eq_vec
  have h_eq_re : E_eig ω * t = sys.syndromeEnergy σ * t := by
    simpa only [t, inner_smul_right, re_ofReal_mul] using h_in
  have h_zero : (E_eig ω - sys.syndromeEnergy σ) * t = 0 := by linarith
  rcases mul_eq_zero.mp h_zero with hE | ht
  · have hE' : E_eig ω = sys.syndromeEnergy σ := sub_eq_zero.mp hE
    rw [hE']
  · change Real.exp (-β * E_eig ω) * t = Real.exp (-β * sys.syndromeEnergy σ) * t
    rw [ht, mul_zero, mul_zero]

lemma gibbsPartitionZ_eq_sum_syndromeProjector {D L : ℕ} {Site : BoxD D L → Type}
    [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)] [∀ x, Nonempty (Site x)]
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (sys : IndexedCommutingProjectorHamiltonian D L Site ι) (β : ℝ) :
    gibbsPartitionZ (opEigenvalues sys.H0 sys.isSelfAdjoint_H0) β =
      ∑ σ : ι → Bool, Real.exp (-β * sys.syndromeEnergy σ) *
        hilbertTrace (sys.syndromeProjector σ) := by
  let ψ := opEigenbasis sys.H0 sys.isSelfAdjoint_H0
  let E_eig := opEigenvalues sys.H0 sys.isSelfAdjoint_H0
  have h_res := syndrome_resolution_indexed sys
  have h_one : hilbertTrace (gibbsDensityOp ψ E_eig β * 1) = 1 := by
    rw [hilbertTrace_gibbsDensityOp_mul_eq ψ E_eig β
      (opEigenbasis_orthonormal sys.H0 sys.isSelfAdjoint_H0)
      (hilbertTrace_eq_sum_opEigenbasis sys.H0 sys.isSelfAdjoint_H0) 1]
    have h_inner : ∀ ω, RCLike.re (inner ℂ (ψ ω) ((1 : _ →L[ℂ] _) (ψ ω))) = 1 := fun ω => by
      change RCLike.re (inner ℂ (ψ ω) (ψ ω)) = 1
      rw [opEigenbasis_orthonormal sys.H0 sys.isSelfAdjoint_H0 ω ω, if_pos rfl]
      exact RCLike.one_re
    simp_rw [h_inner, mul_one]
    exact sum_gibbsProb_eq_one E_eig β
  have h_sum : hilbertTrace (gibbsDensityOp ψ E_eig β * 1) =
      (gibbsPartitionZ E_eig β)⁻¹ *
        ∑ σ : ι → Bool, Real.exp (-β * sys.syndromeEnergy σ) *
          hilbertTrace (sys.syndromeProjector σ) := by
    rw [← h_res.2.2.2.1, Finset.mul_sum, hilbertTrace_sum]
    refine (Finset.sum_congr rfl (fun σ _ =>
      hilbertTrace_gibbsDensityOp_mul_syndromeProjector sys β σ)).trans ?_
    rw [← Finset.mul_sum]
  have hZ_ne : gibbsPartitionZ E_eig β ≠ 0 := ne_of_gt (gibbsPartitionZ_pos E_eig β)
  have h_eq := h_one.symm.trans h_sum
  calc gibbsPartitionZ E_eig β
    _ = gibbsPartitionZ E_eig β * 1 := (mul_one _).symm
    _ = gibbsPartitionZ E_eig β * ((gibbsPartitionZ E_eig β)⁻¹ *
          ∑ σ : ι → Bool, Real.exp (-β * sys.syndromeEnergy σ) *
            hilbertTrace (sys.syndromeProjector σ)) := by rw [← h_eq]
    _ = ∑ σ : ι → Bool, Real.exp (-β * sys.syndromeEnergy σ) *
          hilbertTrace (sys.syndromeProjector σ) := by
      rw [← mul_assoc, mul_inv_cancel₀ hZ_ne, one_mul]

lemma hilbertTrace_syndromeProjector_nonneg {D L : ℕ} {Site : BoxD D L → Type}
    [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)] {ι : Type} [Fintype ι] [DecidableEq ι]
    (sys : IndexedCommutingProjectorHamiltonian D L Site ι) (σ : ι → Bool) :
    0 ≤ hilbertTrace (sys.syndromeProjector σ) := by
  unfold hilbertTrace
  apply Finset.sum_nonneg
  intro x _
  have hP := (syndrome_resolution_indexed sys).2.1 σ
  have h_adj : (sys.syndromeProjector σ)† = sys.syndromeProjector σ :=
    ContinuousLinearMap.isSelfAdjoint_iff'.mp hP.isSelfAdjoint
  have h_id : sys.syndromeProjector σ (sys.syndromeProjector σ (basisVecGlobal Site x)) =
      sys.syndromeProjector σ (basisVecGlobal Site x) := by
    change (sys.syndromeProjector σ * sys.syndromeProjector σ) (basisVecGlobal Site x) = _
    rw [hP.isIdempotentElem.eq]
  rw [← h_id, ← ContinuousLinearMap.adjoint_inner_left, h_adj]
  exact inner_self_nonneg

/-! ## 2. Check-Flip Intertwining & Syndrome-Shift Trace Invariance -/

private lemma intertwine_synFactor {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {ι : Type*} {Q : ι → (H →L[ℂ] H)} {U : H →L[ℂ] H} {flip : ι → Bool}
    (hU_flip : ∀ i : ι, U * Q i = (if flip i then 1 - Q i else Q i) * U)
    (σ : ι → Bool) (i : ι) :
    U * synFactor Q σ i = synFactor Q (fun i' => xor (σ i') (flip i')) i * U := by
  have hi := hU_flip i
  by_cases hσ : σ i = true <;> by_cases hf : flip i = true <;>
    simp [synFactor, hσ, hf] at hi ⊢
  · exact hi
  · exact hi
  · rw [mul_sub, mul_one, hi, sub_mul, one_mul, sub_sub_cancel]
  · rw [mul_sub, mul_one, sub_mul, one_mul, hi]

private lemma intertwine_listSynProj {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {ι : Type*} {Q : ι → (H →L[ℂ] H)} {U : H →L[ℂ] H} {flip : ι → Bool}
    (hU_flip : ∀ i : ι, U * Q i = (if flip i then 1 - Q i else Q i) * U)
    (σ : ι → Bool) (L : List ι) :
    U * listSynProj Q σ L = listSynProj Q (fun i' => xor (σ i') (flip i')) L * U := by
  induction L with
  | nil => simp [listSynProj]
  | cons i₀ L ih =>
    change U * (synFactor Q σ i₀ * listSynProj Q σ L) =
      (synFactor Q (fun i' => xor (σ i') (flip i')) i₀ *
        listSynProj Q (fun i' => xor (σ i') (flip i')) L) * U
    rw [← mul_assoc, intertwine_synFactor hU_flip σ i₀, mul_assoc, ih, ← mul_assoc]

lemma intertwine_syndromeProjector_of_checkFlip {D L : ℕ} {Site : BoxD D L → Type}
    [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)] {ι : Type} [Fintype ι] [DecidableEq ι]
    (sys : IndexedCommutingProjectorHamiltonian D L Site ι)
    {U : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site} {flip : ι → Bool}
    (hU_flip : ∀ i : ι, U * sys.checkProj i = (if flip i then 1 - sys.checkProj i else sys.checkProj i) * U)
    (σ : ι → Bool) :
    U * sys.syndromeProjector σ = sys.syndromeProjector (fun i => xor (σ i) (flip i)) * U :=
  intertwine_listSynProj hU_flip σ (Finset.univ : Finset ι).toList

lemma hilbertTrace_syndromeProjector_xor_eq {D L : ℕ} {Site : BoxD D L → Type}
    [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)] {ι : Type} [Fintype ι] [DecidableEq ι]
    (sys : IndexedCommutingProjectorHamiltonian D L Site ι)
    {U : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site} {flip : ι → Bool}
    (hU_inv : U * U = 1)
    (hU_flip : ∀ i : ι, U * sys.checkProj i = (if flip i then 1 - sys.checkProj i else sys.checkProj i) * U)
    (σ : ι → Bool) :
    hilbertTrace (sys.syndromeProjector (fun i => xor (σ i) (flip i))) =
      hilbertTrace (sys.syndromeProjector σ) := by
  have h_inter := intertwine_syndromeProjector_of_checkFlip sys hU_flip σ
  have h_eq : sys.syndromeProjector (fun i => xor (σ i) (flip i)) =
      (U * sys.syndromeProjector σ) * U := by
    calc sys.syndromeProjector (fun i => xor (σ i) (flip i))
      _ = sys.syndromeProjector (fun i => xor (σ i) (flip i)) * (U * U) := by rw [hU_inv, mul_one]
      _ = (sys.syndromeProjector (fun i => xor (σ i) (flip i)) * U) * U := by rw [mul_assoc]
      _ = (U * sys.syndromeProjector σ) * U := by rw [← h_inter]
  rw [h_eq, hilbertTrace_mul_comm_aux (U * sys.syndromeProjector σ) U, ← mul_assoc, hU_inv, one_mul]

/-! ## 3. Syndrome Subset Projectors & Norm Bound for Self-Adjoint Involutions -/

def syndromeSubsetProj {D L : ℕ} {Site : BoxD D L → Type}
    [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)] {ι : Type} [Fintype ι] [DecidableEq ι]
    (sys : IndexedCommutingProjectorHamiltonian D L Site ι) (S : Finset (ι → Bool)) :
    ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site :=
  ∑ σ ∈ S, sys.syndromeProjector σ

lemma syndromeSubsetProj_props {D L : ℕ} {Site : BoxD D L → Type}
    [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)] {ι : Type} [Fintype ι] [DecidableEq ι]
    (sys : IndexedCommutingProjectorHamiltonian D L Site ι) (S : Finset (ι → Bool)) :
    IsStarProjection (syndromeSubsetProj sys S) ∧
    Commute sys.H0 (syndromeSubsetProj sys S) ∧
    (∀ i : ι, Commute (sys.checkProj i) (syndromeSubsetProj sys S)) ∧
    ((fun _ => false) ∈ S → sys.P0 * syndromeSubsetProj sys S = sys.P0) ∧
    1 - syndromeSubsetProj sys S = syndromeSubsetProj sys (Finset.univ \ S) := by
  have h_res := syndrome_resolution_indexed sys
  have h_mul : ∀ σ ∈ S, syndromeSubsetProj sys S * sys.syndromeProjector σ =
      sys.syndromeProjector σ := fun σ hσ => by
    dsimp [syndromeSubsetProj]; rw [Finset.sum_mul, Finset.sum_eq_single σ]
    · exact (h_res.2.1 σ).isIdempotentElem.eq
    · intro τ _ hne; exact h_res.2.2.1 τ σ hne
    · intro h_abs; exact False.elim (h_abs hσ)
  refine ⟨⟨?_, ?_⟩, ?_, ?_, ?_, ?_⟩
  · rw [IsIdempotentElem]
    dsimp [syndromeSubsetProj]; rw [Finset.mul_sum]
    exact Finset.sum_congr rfl h_mul
  · rw [ContinuousLinearMap.isSelfAdjoint_iff']
    dsimp [syndromeSubsetProj]; rw [map_sum]
    exact Finset.sum_congr rfl
      (fun σ _ => ContinuousLinearMap.isSelfAdjoint_iff'.mp (h_res.2.1 σ).isSelfAdjoint)
  · dsimp [syndromeSubsetProj]
    exact Commute.sum_right _ _ _ (fun σ _ => h_res.2.2.2.2.2.2.2 σ)
  · intro i; dsimp [syndromeSubsetProj]
    exact Commute.sum_right _ _ _ (fun σ _ => h_res.2.2.2.2.2.2.1 σ i)
  · intro h0
    rw [← h_res.1]
    dsimp [syndromeSubsetProj]; rw [Finset.mul_sum, Finset.sum_eq_single (fun _ => false)]
    · exact (h_res.2.1 (fun _ => false)).isIdempotentElem.eq
    · intro τ _ hne; exact h_res.2.2.1 (fun _ => false) τ (Ne.symm hne)
    · intro h_abs; exact False.elim (h_abs h0)
  · dsimp [syndromeSubsetProj]
    rw [← h_res.2.2.2.1, ← Finset.sum_sdiff (Finset.subset_univ S), add_sub_cancel_right]

lemma norm_le_one_of_isSelfAdjoint_and_mul_self_eq_one {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    {U : E →L[ℂ] E} (h_sa : IsSelfAdjoint U) (h_inv : U * U = 1) :
    ‖U‖ ≤ 1 := by
  have h_cstar : ‖star U * U‖ = ‖U‖ * ‖U‖ := CStarRing.norm_star_mul_self
  rw [h_sa.star_eq, h_inv] at h_cstar
  have h_one : ‖(1 : E →L[ℂ] E)‖ ≤ 1 := ContinuousLinearMap.norm_id_le
  nlinarith [norm_nonneg U]

/-! ## 4. Level-$k$ Inhomogeneous BDL Pullback/Pushforward & Bare Logicals -/

lemma sum_bdlPushChain_mul_eq (k : ℕ) (c : BDLWeldedQubit k → ZMod 2)
    (f : BoxSlot3D (bdlBoxSide k) qCodeBDL → ZMod 2) :
    (∑ p : BoxSlot3D (bdlBoxSide k) qCodeBDL, bdlPushChain k c p * f p) =
      ∑ q : BDLWeldedQubit k, c q * f (bdlQubitSiteSlot k q) := by
  refine (Finset.sum_subset (Finset.subset_univ (Finset.univ.image (bdlQubitSiteSlot k))) ?_).symm.trans ?_
  · intro p _ hp
    rw [bdlPushChain_eq_zero_of_not_mem_image k c p hp, zero_mul]
  · rw [Finset.sum_image (fun q₁ _ q₂ _ h => bdlQubitSiteSlot_injective k h)]
    refine Finset.sum_congr rfl fun q _ => ?_
    rw [bdlPushChain_apply_bdlQubitSiteSlot]

lemma sum_mul_bdlPushChain_eq (k : ℕ) (f : BoxSlot3D (bdlBoxSide k) qCodeBDL → ZMod 2)
    (c : BDLWeldedQubit k → ZMod 2) :
    (∑ p : BoxSlot3D (bdlBoxSide k) qCodeBDL, f p * bdlPushChain k c p) =
      ∑ q : BDLWeldedQubit k, f (bdlQubitSiteSlot k q) * c q := by
  simp_rw [mul_comm (f _), sum_bdlPushChain_mul_eq k c f]

lemma sum_bdlPushChain_mul_bdlPushChain_eq_dualPairing (k : ℕ)
    (a b : BDLWeldedQubit k → ZMod 2) :
    (∑ p : BoxSlot3D (bdlBoxSide k) qCodeBDL, bdlPushChain k a p * bdlPushChain k b p) =
      dualPairing a b := by
  rw [sum_bdlPushChain_mul_eq]
  simp_rw [bdlPushChain_apply_bdlQubitSiteSlot]
  rfl

lemma fiber_localRank_surjective_bdl {X V : Type*} [Fintype X] [DecidableEq X] [DecidableEq V]
    (f : X → V) (idx : X → ℕ) (h_inj : Function.Injective idx)
    (v : V) (c : ℕ) (hc : c < (Finset.univ.filter (fun x' : X => f x' = v)).card) :
    ∃ x : X, f x = v ∧
      ((Finset.univ.filter (fun x' : X => f x' = f x)).filter
        (fun x' => idx x' < idx x)).card = c := by
  let S := Finset.univ.filter (fun x' : X => f x' = v)
  have h_lt : ∀ x : X, ((Finset.univ.filter (fun x' : X => f x' = f x)).filter
      (fun x' => idx x' < idx x)).card < (Finset.univ.filter (fun x' : X => f x' = f x)).card := by
    intro x; apply Finset.card_lt_card; rw [Finset.ssubset_iff_subset_ne]
    refine ⟨Finset.filter_subset _ _, fun h_eq => ?_⟩
    have hx : x ∈ Finset.univ.filter (fun x' : X => f x' = f x) := by simp
    rw [← h_eq, Finset.mem_filter] at hx; exact Nat.lt_irrefl _ hx.2
  let g : S → Fin S.card := fun x =>
    ⟨((Finset.univ.filter (fun x' : X => f x' = f x.1)).filter (fun x' => idx x' < idx x.1)).card, by
      have hx : f x.1 = v := (Finset.mem_filter.mp x.2).2
      simpa [S, hx] using h_lt x.1⟩
  have hg_inj : Function.Injective g := by
    intro x₁ x₂ h
    have hf : f x₁.1 = f x₂.1 := (Finset.mem_filter.mp x₁.2).2.trans (Finset.mem_filter.mp x₂.2).2.symm
    have hr : (g x₁).val = (g x₂).val := congr_arg Fin.val h
    have h_mono : ∀ a b : X, f a = f b → idx a < idx b →
        ((Finset.univ.filter (fun x' : X => f x' = f a)).filter (fun x' => idx x' < idx a)).card <
        ((Finset.univ.filter (fun x' : X => f x' = f b)).filter (fun x' => idx x' < idx b)).card := by
      intro a b hab hlt; rw [hab]; apply Finset.card_lt_card; rw [Finset.ssubset_iff_subset_ne]
      refine ⟨fun y hy => ?_, fun h_eq => ?_⟩
      · simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hy ⊢
        exact ⟨hy.1, Nat.lt_trans hy.2 hlt⟩
      · have ha : a ∈ (Finset.univ.filter (fun x' : X => f x' = f b)).filter (fun x' => idx x' < idx b) :=
          Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, hab⟩, hlt⟩
        rw [← h_eq, Finset.mem_filter] at ha; exact Nat.lt_irrefl _ ha.2
    rcases lt_trichotomy (idx x₁.1) (idx x₂.1) with h1 | heq | h2
    · exact False.elim (ne_of_lt (h_mono x₁.1 x₂.1 hf h1) hr)
    · exact Subtype.ext (h_inj heq)
    · exact False.elim (ne_of_gt (h_mono x₂.1 x₁.1 hf.symm h2) hr)
  obtain ⟨x, hx⟩ := ((Fintype.bijective_iff_injective_and_card g).mpr
    ⟨hg_inj, by simp [Fintype.card_coe, Fintype.card_fin]⟩).2 ⟨c, hc⟩
  exact ⟨x.1, (Finset.mem_filter.mp x.2).2, congr_arg Fin.val hx⟩

lemma weylPauliZ_bdlPushChain_commute_checkProj (k : ℕ)
    (c : BDLWeldedQubit k → ZMod 2) (h_syn : syndrome (bdlWeldedCode k) c = 0)
    (idx : StaticCSSCheckIdx (bdlBoxSide k) qCodeBDL mMaxBDL) :
    Commute ((bdlInhomogeneousSystem k).checkProj idx) (weylPauliZ (bdlPushChain k c)) := by
  apply (commute_weylPauliZ_staticCSSCheckProj_of_ortho (bdlLocalDescriptor k) (bdlPushChain k c) ?_ idx).symm
  intro v idxX hm
  rw [numXChecks_val_eq_card_fiber] at hm
  have h_injX : Function.Injective (bdlCellIndexX k) :=
    Fin.val_injective.comp (Fintype.equivFin _).injective
  obtain ⟨mX, rfl, hmX_r⟩ :=
    fiber_localRank_surjective_bdl (bdlGridVertexX k) (bdlCellIndexX k) h_injX v idxX.val hm
  rw [sum_bdlPushChain_mul_eq]
  simp_rw [descriptorCheckXChain_bdlQubitSiteSlot_eq k mX idxX hmX_r,
    mul_comm (c _) ((bdlWeldedCode k).checkX mX _)]
  exact congr_fun h_syn mX

lemma weylPauliX_bdlPushChain_commute_checkProj (k : ℕ)
    (c : BDLWeldedQubit k → ZMod 2) (h_syn : syndrome (dualCode (bdlWeldedCode k)) c = 0)
    (idx : StaticCSSCheckIdx (bdlBoxSide k) qCodeBDL mMaxBDL) :
    Commute ((bdlInhomogeneousSystem k).checkProj idx) (weylPauliX (bdlPushChain k c)) := by
  apply (commute_weylPauliX_staticCSSCheckProj_of_ortho (bdlLocalDescriptor k) (bdlPushChain k c) ?_ ?_ idx).symm
  · intro ⟨v, s⟩ hb_ne
    by_contra h_not
    have hp_not : (v, s) ∉ Finset.univ.image (bdlQubitSiteSlot k) := by
      rintro hp
      rcases Finset.mem_image.mp hp with ⟨q, _, hq⟩
      rw [bdlQubitSiteSlot_eq k q] at hq
      have hqv : bdlGridVertexQ k q = v := (Prod.ext_iff.mp hq).1
      have hqs : bdlQubitLocalRank k q = s.val := congr_arg Fin.val (Prod.ext_iff.mp hq).2
      apply h_not
      dsimp [bdlLocalDescriptor, bdlLocalDescriptorOfPlacement]
      rw [decide_eq_true_iff, ← hqv, ← hqs]
      exact bdlQubitLocalRank_lt_card k q
    exact hb_ne (bdlPushChain_eq_zero_of_not_mem_image k c (v, s) hp_not)
  · intro v idxZ hm
    rw [numZChecks_val_eq_card_fiber] at hm
    have h_injZ : Function.Injective (bdlCellIndexZ k) :=
      Fin.val_injective.comp (Fintype.equivFin _).injective
    obtain ⟨mZ, rfl, hmZ_r⟩ :=
      fiber_localRank_surjective_bdl (bdlGridVertexZ k) (bdlCellIndexZ k) h_injZ v idxZ.val hm
    rw [sum_bdlPushChain_mul_eq]
    simp_rw [descriptorCheckZChain_bdlQubitSiteSlot_eq k mZ idxZ hmZ_r,
      mul_comm (c _) ((bdlWeldedCode k).checkZ mZ _)]
    exact congr_fun h_syn mZ

lemma bdl_bare_logical_props (k : ℕ) (L_Z L_X : BDLWeldedQubit k → ZMod 2)
    (h_syn_Z : syndrome (bdlWeldedCode k) L_Z = 0)
    (h_syn_X : syndrome (dualCode (bdlWeldedCode k)) L_X = 0)
    (h_pair : dualPairing L_Z L_X = 1) :
    let sys := bdlInhomogeneousSystem k
    let Z_log := weylPauliZ (bdlPushChain k L_Z)
    let X_log := weylPauliX (bdlPushChain k L_X)
    (IsSelfAdjoint Z_log ∧ Z_log * Z_log = 1 ∧ Commute sys.H0 Z_log ∧ Commute sys.P0 Z_log) ∧
    (IsSelfAdjoint X_log ∧ X_log * X_log = 1 ∧ Commute sys.H0 X_log ∧ Commute sys.P0 X_log) ∧
    (Z_log * X_log + X_log * Z_log) * sys.P0 = 0 ∧
    (Z_log * sys.P0 ≠ 0 ∧ X_log * sys.P0 ≠ 0) := by
  intro sys Z_log X_log
  have hZ_comm_i : ∀ idx, Commute Z_log (sys.checkProj idx) :=
    fun idx => (weylPauliZ_bdlPushChain_commute_checkProj k L_Z h_syn_Z idx).symm
  have hX_comm_i : ∀ idx, Commute X_log (sys.checkProj idx) :=
    fun idx => (weylPauliX_bdlPushChain_commute_checkProj k L_X h_syn_X idx).symm
  have hZ_H0 : Commute sys.H0 Z_log := commute_with_H0_of_commute_checkProj sys hZ_comm_i
  have hX_H0 : Commute sys.H0 X_log := commute_with_H0_of_commute_checkProj sys hX_comm_i
  have hZ_P0 : Commute sys.P0 Z_log := (commute_with_P0_of_commute_checkProj sys hZ_comm_i).symm
  have hX_P0 : Commute sys.P0 X_log := (commute_with_P0_of_commute_checkProj sys hX_comm_i).symm
  have hZ_inv : Z_log * Z_log = 1 := weylPauliZ_sq_eq_one _
  have hX_inv : X_log * X_log = 1 := weylPauliX_sq_eq_one _
  have h_anti : Z_log * X_log + X_log * Z_log = 0 := by
    change weylPauliZ (bdlPushChain k L_Z) * weylPauliX (bdlPushChain k L_X) +
      weylPauliX (bdlPushChain k L_X) * weylPauliZ (bdlPushChain k L_Z) = 0
    rw [weylPauliX_mul_weylPauliZ]
    have h_ph : pauliPhase (bdlPushChain k L_Z) (bdlPushChain k L_X) = -1 := by
      unfold pauliPhase
      rw [sum_bdlPushChain_mul_bdlPushChain_eq_dualPairing k L_Z L_X, h_pair]
      have h10 : (1 : ZMod 2) ≠ 0 := by decide
      rw [if_neg h10]
    rw [h_ph]
    ext φ; simp
  refine ⟨⟨weylPauliZ_isSelfAdjoint _, hZ_inv, hZ_H0, hZ_P0⟩,
    ⟨weylPauliX_isSelfAdjoint _, hX_inv, hX_H0, hX_P0⟩,
    by rw [h_anti, zero_mul], ⟨?_, ?_⟩⟩
  · intro h_zero
    have h_P0 : sys.P0 = 0 := by
      calc sys.P0 = (Z_log * Z_log) * sys.P0 := by rw [hZ_inv, one_mul]
        _ = Z_log * (Z_log * sys.P0) := by rw [mul_assoc]
        _ = 0 := by rw [h_zero, mul_zero]
    exact sys.frustration_free h_P0
  · intro h_zero
    have h_P0 : sys.P0 = 0 := by
      calc sys.P0 = (X_log * X_log) * sys.P0 := by rw [hX_inv, one_mul]
        _ = X_log * (X_log * sys.P0) := by rw [mul_assoc]
        _ = 0 := by rw [h_zero, mul_zero]
    exact sys.frustration_free h_P0
