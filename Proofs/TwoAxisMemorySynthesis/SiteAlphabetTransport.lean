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

import Proofs.TwoAxisMemorySynthesis.AutonomousHeisenbergGroundDrift
import Proofs.TwoAxisMemorySynthesis.WeldedLatticeRealization

/-!
# Unitary Site-Alphabet Transport, Check Reindexing, and Ground-Space Degeneracy

Constructs unitary conjugation maps induced by site-alphabet equivalences, proves compatibility with cylinder supports, partial traces, conditional expectations, syndrome projections, and Gibbs failure probabilities, and shows ground-space degeneracy at least 2 from anticommuting logical operators.

## References

* Part I, Section 5.4 (`subsec:safe-decoded-observables`), Definition 5.6 (`def:safe-decoded-observables`)
* Part I, Section 7.4 (`subsec:main-theorem-synthesis`), Theorem 7.5 (`thm:main`)
-/

open scoped Classical BigOperators InnerProduct ComplexConjugate
open ContinuousLinearMap WeldedHierarchy WeldedHierarchy.BDLDecoder InhomogeneousMemoryChallenge

noncomputable section

set_option maxRecDepth 200000
set_option maxHeartbeats 800000
set_option linter.unusedSectionVars false

lemma hilbertTrace_sum_finset {D L : ℕ} {Site : BoxD D L → Type}
    [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)] {α : Type*} (s : Finset α)
    (f : α → (ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site)) :
    hilbertTrace (∑ a ∈ s, f a) = ∑ a ∈ s, hilbertTrace (f a) := by
  unfold hilbertTrace; rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun ω _ => ?_)
  rw [ContinuousLinearMap.sum_apply, inner_sum, map_sum]

private lemma isStarProjection_synFactor_aux {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] {ι : Type*} {Q : ι → (H →L[ℂ] H)}
    (h_proj : ∀ i, IsStarProjection (Q i)) (σ : ι → Bool) (i : ι) :
    IsStarProjection (synFactor Q σ i) := by
  dsimp [synFactor]; split_ifs
  · exact h_proj i
  · refine ⟨?_, ?_⟩
    · rw [IsIdempotentElem]
      calc (1 - Q i) * (1 - Q i) = 1 - Q i - Q i + Q i * Q i := by noncomm_ring
        _ = 1 - Q i := by rw [(h_proj i).isIdempotentElem.eq]; abel
    · rw [isSelfAdjoint_iff, star_sub, star_one, (h_proj i).isSelfAdjoint.star_eq]

private lemma commute_Q_synFactor_aux {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {ι : Type*} {Q : ι → (H →L[ℂ] H)} (h_comm : ∀ i₁ i₂, Commute (Q i₁) (Q i₂))
    (σ : ι → Bool) (i₁ i₂ : ι) : Commute (Q i₁) (synFactor Q σ i₂) := by
  dsimp [synFactor]; split_ifs
  · exact h_comm i₁ i₂
  · exact (Commute.one_right (Q i₁)).sub_right (h_comm i₁ i₂)

private lemma commute_synFactor_listSynProj_aux {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {ι : Type*} {Q : ι → (H →L[ℂ] H)} (h_comm : ∀ i₁ i₂, Commute (Q i₁) (Q i₂))
    (σ₁ σ₂ : ι → Bool) (i : ι) (L : List ι) :
    Commute (synFactor Q σ₁ i) (listSynProj Q σ₂ L) := by
  dsimp [listSynProj]; apply Commute.list_prod_right; intro x hx
  rcases List.mem_map.mp hx with ⟨i₂, _, rfl⟩
  dsimp [synFactor]; split_ifs
  · exact h_comm i i₂
  · exact (Commute.one_right (Q i)).sub_right (h_comm i i₂)
  · exact (Commute.one_left (Q i₂)).sub_left (h_comm i i₂)
  · exact ((Commute.one_left _).sub_left (Commute.one_right _)).sub_right
      ((Commute.one_left (Q i₂)).sub_left (h_comm i i₂))

private lemma isStarProjection_listSynProj_aux {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] {ι : Type*} {Q : ι → (H →L[ℂ] H)}
    (h_proj : ∀ i, IsStarProjection (Q i)) (h_comm : ∀ i₁ i₂, Commute (Q i₁) (Q i₂))
    (σ : ι → Bool) (L : List ι) : IsStarProjection (listSynProj Q σ L) := by
  induction L with
  | nil => simp [listSynProj, IsStarProjection, IsIdempotentElem, isSelfAdjoint_iff]
  | cons i₀ L ih =>
    change IsStarProjection (synFactor Q σ i₀ * listSynProj Q σ L)
    have hP := isStarProjection_synFactor_aux h_proj σ i₀
    have hPQ := commute_synFactor_listSynProj_aux h_comm σ σ i₀ L
    refine ⟨?_, ?_⟩
    · rw [IsIdempotentElem]
      calc (synFactor Q σ i₀ * listSynProj Q σ L) * (synFactor Q σ i₀ * listSynProj Q σ L)
        _ = (synFactor Q σ i₀ * synFactor Q σ i₀) * (listSynProj Q σ L * listSynProj Q σ L) := by
          rw [mul_assoc, ← mul_assoc _ (synFactor Q σ i₀), hPQ.symm.eq]; simp only [mul_assoc]
        _ = synFactor Q σ i₀ * listSynProj Q σ L := by
          rw [hP.isIdempotentElem.eq, ih.isIdempotentElem.eq]
    · rw [isSelfAdjoint_iff, star_mul, hP.isSelfAdjoint.star_eq, ih.isSelfAdjoint.star_eq, hPQ.symm.eq]

private lemma mul_listSynProj_of_mem_aux {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
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
    · have h_c := commute_Q_synFactor_aux h_comm σ i i₀
      calc Q i * (synFactor Q σ i₀ * listSynProj Q σ L)
        _ = synFactor Q σ i₀ * (Q i * listSynProj Q σ L) := by rw [← mul_assoc, h_c.eq, mul_assoc]
        _ = if σ i then synFactor Q σ i₀ * listSynProj Q σ L else 0 := by
          rw [ih hi_tail]; split_ifs <;> simp

lemma listSynProj_false_absorb_left {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] {ι₁ ι₂ : Type*} [DecidableEq ι₂]
    {Q₁ : ι₁ → (H →L[ℂ] H)} {Q₂ : ι₂ → (H →L[ℂ] H)}
    (h_proj₂ : ∀ j, IsStarProjection (Q₂ j)) (h_comm₂ : ∀ j₁ j₂, Commute (Q₂ j₁) (Q₂ j₂))
    (L₁ : List ι₁) (L₂ : List ι₂)
    (h_cover : ∀ i ∈ L₁, Q₁ i = 0 ∨ ∃ j ∈ L₂, Q₁ i = Q₂ j) :
    listSynProj Q₁ (fun _ => false) L₁ * listSynProj Q₂ (fun _ => false) L₂ =
      listSynProj Q₂ (fun _ => false) L₂ := by
  induction L₁ with
  | nil => dsimp [listSynProj]; exact one_mul _
  | cons i₀ L_tail ih =>
    change (1 - Q₁ i₀) * listSynProj Q₁ (fun _ => false) L_tail *
        listSynProj Q₂ (fun _ => false) L₂ = _
    rw [mul_assoc, ih (fun i hi => h_cover i (List.mem_cons_of_mem _ hi))]
    rcases h_cover i₀ List.mem_cons_self with h0 | ⟨j₀, hj₀, h_eq⟩
    · rw [h0, sub_zero, one_mul]
    · rw [h_eq, sub_mul, one_mul]
      have h_abs : Q₂ j₀ * listSynProj Q₂ (fun _ => false) L₂ = 0 := by
        simpa using mul_listSynProj_of_mem_aux h_proj₂ h_comm₂ (fun _ => false) hj₀
      rw [h_abs, sub_zero]

lemma listSynProj_false_eq_of_mutual_cover {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] {ι₁ ι₂ : Type*} [DecidableEq ι₁] [DecidableEq ι₂]
    {Q₁ : ι₁ → (H →L[ℂ] H)} {Q₂ : ι₂ → (H →L[ℂ] H)}
    (h_proj₁ : ∀ i, IsStarProjection (Q₁ i)) (h_comm₁ : ∀ i₁ i₂, Commute (Q₁ i₁) (Q₁ i₂))
    (h_proj₂ : ∀ j, IsStarProjection (Q₂ j)) (h_comm₂ : ∀ j₁ j₂, Commute (Q₂ j₁) (Q₂ j₂))
    (L₁ : List ι₁) (L₂ : List ι₂)
    (h₁₂ : ∀ i ∈ L₁, Q₁ i = 0 ∨ ∃ j ∈ L₂, Q₁ i = Q₂ j)
    (h₂₁ : ∀ j ∈ L₂, Q₂ j = 0 ∨ ∃ i ∈ L₁, Q₂ j = Q₁ i) :
    listSynProj Q₁ (fun _ => false) L₁ = listSynProj Q₂ (fun _ => false) L₂ := by
  have hA := listSynProj_false_absorb_left h_proj₂ h_comm₂ L₁ L₂ h₁₂
  have hB := listSynProj_false_absorb_left h_proj₁ h_comm₁ L₂ L₁ h₂₁
  have hP₁ := (isStarProjection_listSynProj_aux h_proj₁ h_comm₁ (fun _ => false) L₁).isSelfAdjoint
  have hP₂ := (isStarProjection_listSynProj_aux h_proj₂ h_comm₂ (fun _ => false) L₂).isSelfAdjoint
  have hB_star : listSynProj Q₁ (fun _ => false) L₁ * listSynProj Q₂ (fun _ => false) L₂ =
      listSynProj Q₁ (fun _ => false) L₁ := by
    calc listSynProj Q₁ (fun _ => false) L₁ * listSynProj Q₂ (fun _ => false) L₂
      _ = star (listSynProj Q₂ (fun _ => false) L₂ * listSynProj Q₁ (fun _ => false) L₁) := by
        rw [star_mul, hP₁.star_eq, hP₂.star_eq]
      _ = star (listSynProj Q₁ (fun _ => false) L₁) := by rw [hB]
      _ = listSynProj Q₁ (fun _ => false) L₁ := hP₁.star_eq
  exact hB_star.symm.trans hA

lemma listSynProj_reindex_false {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] {ι ι' : Type*} [Fintype ι] [DecidableEq ι] [Fintype ι'] [DecidableEq ι']
    (Q : ι → (H →L[ℂ] H)) (e : ι ≃ ι')
    (h_proj : ∀ i, IsStarProjection (Q i)) (h_comm : ∀ i₁ i₂, Commute (Q i₁) (Q i₂))
    (P : ι → Prop) [DecidablePred P] :
    listSynProj (fun i' => Q (e.symm i')) (fun _ => false)
      (Finset.univ.filter (fun i' => P (e.symm i'))).toList =
    listSynProj Q (fun _ => false) (Finset.univ.filter P).toList := by
  apply listSynProj_false_eq_of_mutual_cover
  · intro i'; exact h_proj (e.symm i')
  · intro i₁' i₂'; exact h_comm (e.symm i₁') (e.symm i₂')
  · exact h_proj
  · exact h_comm
  · intro i' hi'
    have hP : P (e.symm i') := (Finset.mem_filter.mp (Finset.mem_toList.mp hi')).2
    exact Or.inr ⟨e.symm i',
      Finset.mem_toList.mpr (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hP⟩), rfl⟩
  · intro i hi
    have hP : P i := (Finset.mem_filter.mp (Finset.mem_toList.mp hi)).2
    refine Or.inr ⟨e i, ?_, by rw [e.symm_apply_apply]⟩
    rw [Finset.mem_toList, Finset.mem_filter, e.symm_apply_apply]
    exact ⟨Finset.mem_univ _, hP⟩

lemma listSynProj_reindex_univ_false {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] {ι ι' : Type*} [Fintype ι] [DecidableEq ι] [Fintype ι'] [DecidableEq ι']
    (Q : ι → (H →L[ℂ] H)) (e : ι ≃ ι')
    (h_proj : ∀ i, IsStarProjection (Q i)) (h_comm : ∀ i₁ i₂, Commute (Q i₁) (Q i₂)) :
    listSynProj (fun i' => Q (e.symm i')) (fun _ => false) (Finset.univ : Finset ι').toList =
    listSynProj Q (fun _ => false) (Finset.univ : Finset ι).toList := by
  simpa using listSynProj_reindex_false Q e h_proj h_comm (fun _ => True)

def IndexedCommutingProjectorHamiltonian.reindex {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    {ι ι' : Type} [Fintype ι] [DecidableEq ι] [Fintype ι'] [DecidableEq ι']
    (sys : IndexedCommutingProjectorHamiltonian D L Site ι) (e : ι ≃ ι') :
    IndexedCommutingProjectorHamiltonian D L Site ι' where
  checkProj i' := sys.checkProj (e.symm i')
  weight i' := sys.weight (e.symm i')
  support i' := sys.support (e.symm i')
  is_projector i' := sys.is_projector (e.symm i')
  is_supported i' := sys.is_supported (e.symm i')
  pairwise_commute i₁' i₂' := sys.pairwise_commute (e.symm i₁') (e.symm i₂')
  weight_ge_one i' := sys.weight_ge_one (e.symm i')
  frustration_free := by
    change listSynProj (fun i' => sys.checkProj (e.symm i')) (fun _ => false)
      (Finset.univ : Finset ι').toList ≠ 0
    rw [listSynProj_reindex_univ_false sys.checkProj e sys.is_projector sys.pairwise_commute]
    exact sys.frustration_free

lemma IndexedCommutingProjectorHamiltonian.reindex_H0 {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    {ι ι' : Type} [Fintype ι] [DecidableEq ι] [Fintype ι'] [DecidableEq ι']
    (sys : IndexedCommutingProjectorHamiltonian D L Site ι) (e : ι ≃ ι') :
    (sys.reindex e).H0 = sys.H0 := by
  dsimp [IndexedCommutingProjectorHamiltonian.H0, IndexedCommutingProjectorHamiltonian.reindex]
  exact e.symm.sum_comp (fun i => (sys.weight i : ℂ) • sys.checkProj i)

lemma IndexedCommutingProjectorHamiltonian.reindex_P0 {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    {ι ι' : Type} [Fintype ι] [DecidableEq ι] [Fintype ι'] [DecidableEq ι']
    (sys : IndexedCommutingProjectorHamiltonian D L Site ι) (e : ι ≃ ι') :
    (sys.reindex e).P0 = sys.P0 :=
  listSynProj_reindex_univ_false sys.checkProj e sys.is_projector sys.pairwise_commute

lemma IndexedCommutingProjectorHamiltonian.reindex_P_loc {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    {ι ι' : Type} [Fintype ι] [DecidableEq ι] [Fintype ι'] [DecidableEq ι']
    (sys : IndexedCommutingProjectorHamiltonian D L Site ι) (e : ι ≃ ι')
    (B : Finset (BoxD D L)) :
    (sys.reindex e).localGroundProj B = sys.localGroundProj B :=
  listSynProj_reindex_false sys.checkProj e sys.is_projector sys.pairwise_commute
    (fun i => sys.support i ⊆ B)

def staticCSSCheckAnchor {L q_code m_max : ℕ} :
    StaticCSSCheckIdx L q_code m_max → Box3D L
  | Sum.inl (v, _) => v
  | Sum.inr (Sum.inl (v, _)) => v
  | Sum.inr (Sum.inr (v, _)) => v

lemma staticCSSCheckAnchor_mem_support {L q_code r_0 m_max : ℕ}
    (ω : Box3D L → LocalCSSDescriptor q_code r_0 m_max)
    (j : StaticCSSCheckIdx L q_code m_max) :
    staticCSSCheckAnchor j ∈ staticCSSCheckSupport ω j := by
  have h0 : ∀ v : Box3D L, boxDist v v = 0 := by
    intro v; dsimp [boxDist, coordDist]
    exact le_antisymm (Finset.sup_le (fun _ _ => by omega)) (Nat.zero_le _)
  rcases j with ⟨v, _⟩ | ⟨v, _⟩ | ⟨v, _⟩
  · exact Finset.mem_singleton_self v
  · refine Finset.mem_filter.mpr ⟨Finset.mem_univ v, ?_⟩
    dsimp [staticCSSCheckAnchor]; rw [h0 v]; exact Nat.zero_le _
  · refine Finset.mem_filter.mpr ⟨Finset.mem_univ v, ?_⟩
    dsimp [staticCSSCheckAnchor]; rw [h0 v]; exact Nat.zero_le _

lemma commute_H0_P0_main {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (sys : IndexedCommutingProjectorHamiltonian D L Site ι) :
    Commute sys.H0 sys.P0 := by
  have h1 : sys.H0 * sys.P0 = 0 := sys.ham0_mul_proj0_eq_zero_main
  have h2 : sys.P0 * sys.H0 = 0 := by
    calc sys.P0 * sys.H0
      _ = star sys.P0 * star sys.H0 := by
        rw [sys.isStarProjection_P0.isSelfAdjoint.star_eq, sys.isSelfAdjoint_H0.star_eq]
      _ = star (sys.H0 * sys.P0) := (star_mul sys.H0 sys.P0).symm
      _ = 0 := by rw [h1]; exact @star_zero (ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site) _ _
  rw [commute_iff_eq, h1, h2]

namespace Part1TwoAxisMemorySynthesis

/-!
## 1. Ground-Space Degeneracy from Anticommuting Logical Operators

Establishes `commute_P0_of_mul_P0_eq` and `two_le_groundDegeneracy_of_anticommuting_logicals` prior to isometric site-alphabet transport (`uReindex`, `conjEuclidean`, `conjSiteOp`, `reindexHamiltonian`, and `reindexPerturbation`).
-/

/-- If `P0`, `O`, and `L_op` are self-adjoint, `Commute P0 L_op`, and `O * P0 = L_op * P0`,
    then `Commute P0 O`. -/
lemma commute_P0_of_mul_P0_eq {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [CompleteSpace E] {P0 O L_op : E →L[ℂ] E}
    (hP0 : IsSelfAdjoint P0) (hO : IsSelfAdjoint O) (hL : IsSelfAdjoint L_op)
    (h_comm : Commute P0 L_op) (h_eq : O * P0 = L_op * P0) :
    Commute P0 O := by
  have hP0_adj : P0† = P0 := ContinuousLinearMap.isSelfAdjoint_iff'.mp hP0
  have hO_adj : O† = O := ContinuousLinearMap.isSelfAdjoint_iff'.mp hO
  have hL_adj : L_op† = L_op := ContinuousLinearMap.isSelfAdjoint_iff'.mp hL
  rw [commute_iff_eq]
  calc P0 * O
    _ = P0† * O† := by rw [hP0_adj, hO_adj]
    _ = (O * P0)† := (ContinuousLinearMap.adjoint_comp O P0).symm
    _ = (L_op * P0)† := by rw [h_eq]
    _ = P0† * L_op† := ContinuousLinearMap.adjoint_comp L_op P0
    _ = P0 * L_op := by rw [hP0_adj, hL_adj]
    _ = L_op * P0 := h_comm.eq
    _ = O * P0 := h_eq.symm

/-- Any frustration-free commuting-projector Hamiltonian `sys` with involutive logical operators
    `Z_log, X_log` commuting with `H0` and `P0` and satisfying `(Z_log * X_log + X_log * Z_log) * P0 = 0`
    has ground-state degeneracy `2 ≤ sys.groundDegeneracy`. -/
theorem two_le_groundDegeneracy_of_anticommuting_logicals {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (sys : IndexedCommutingProjectorHamiltonian D L Site ι)
    (Z_log X_log : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site)
    (hZ_inv : Z_log * Z_log = 1) (hZ_H0 : Commute sys.H0 Z_log) (hZ_P0 : Commute sys.P0 Z_log)
    (hX_inv : X_log * X_log = 1) (hX_H0 : Commute sys.H0 X_log)
    (h_anti : (Z_log * X_log + X_log * Z_log) * sys.P0 = 0) :
    2 ≤ sys.groundDegeneracy := by
  have hP0_ne : sys.P0 ≠ 0 := sys.frustration_free
  have h_ex : ∃ ψ₀ : ManyBodyHilbertSpace Site, sys.P0 ψ₀ ≠ 0 := by
    by_contra h_all
    push_neg at h_all
    exact hP0_ne (ContinuousLinearMap.ext h_all)
  rcases h_ex with ⟨ψ₀, hψ₀⟩
  let v := sys.P0 ψ₀
  have hv_P0 : sys.P0 v = v := isStarProjection_apply_self_bhm sys.isStarProjection_P0 ψ₀
  have h_mem_gs : ∀ u : ManyBodyHilbertSpace Site, sys.H0 u = 0 → u ∈ sys.groundSpace :=
    fun _ hu => hu
  have hv_H0 : sys.H0 v = 0 := by
    change (sys.H0 * sys.P0) ψ₀ = 0
    rw [sys.ham0_mul_proj0_eq_zero_main, ContinuousLinearMap.zero_apply]
  have hZ_pres : ∀ u : ManyBodyHilbertSpace Site, sys.H0 u = 0 → sys.H0 (Z_log u) = 0 := by
    intro u hu
    change (sys.H0 * Z_log) u = 0
    rw [hZ_H0.eq, ContinuousLinearMap.mul_apply, hu, map_zero]
  have hX_pres : ∀ u : ManyBodyHilbertSpace Site, sys.H0 u = 0 → sys.H0 (X_log u) = 0 := by
    intro u hu
    change (sys.H0 * X_log) u = 0
    rw [hX_H0.eq, ContinuousLinearMap.mul_apply, hu, map_zero]
  have h_anti_P0 : ∀ u : ManyBodyHilbertSpace Site, sys.P0 u = u →
      Z_log (X_log u) = - X_log (Z_log u) := by
    intro u hu
    have h0 : ((Z_log * X_log + X_log * Z_log) * sys.P0) u = 0 := by
      rw [h_anti, ContinuousLinearMap.zero_apply]
    change (Z_log * X_log + X_log * Z_log) (sys.P0 u) = 0 at h0
    rw [hu, ContinuousLinearMap.add_apply, ContinuousLinearMap.mul_apply,
      ContinuousLinearMap.mul_apply] at h0
    exact eq_neg_of_add_eq_zero_left h0
  have h_pair : ∃ w_pos w_neg : ManyBodyHilbertSpace Site,
      w_pos ≠ 0 ∧ w_neg ≠ 0 ∧
      sys.H0 w_pos = 0 ∧ sys.H0 w_neg = 0 ∧
      Z_log w_pos = w_pos ∧ Z_log w_neg = -w_neg := by
    by_cases h_plus : v + Z_log v ≠ 0
    · let u₁ := v + Z_log v
      have hu₁_P0 : sys.P0 u₁ = u₁ := by
        dsimp [u₁]
        rw [map_add, hv_P0, ← ContinuousLinearMap.mul_apply, hZ_P0.eq,
          ContinuousLinearMap.mul_apply, hv_P0]
      have hu₁_Z : Z_log u₁ = u₁ := by
        calc Z_log (v + Z_log v)
          _ = Z_log v + (Z_log * Z_log) v := by rw [map_add, ContinuousLinearMap.mul_apply]
          _ = v + Z_log v := by rw [hZ_inv, ContinuousLinearMap.one_apply, add_comm]
      have hu₁_H0 : sys.H0 u₁ = 0 := by
        dsimp [u₁]; rw [map_add, hv_H0, hZ_pres v hv_H0, add_zero]
      let u₂ := X_log u₁
      have hu₂_ne : u₂ ≠ 0 := by
        intro h0
        have : X_log u₂ = 0 := by rw [h0, map_zero]
        rw [show X_log u₂ = (X_log * X_log) u₁ from rfl, hX_inv, ContinuousLinearMap.one_apply] at this
        exact h_plus this
      have hu₂_Z : Z_log u₂ = -u₂ := by
        dsimp [u₂]
        rw [h_anti_P0 u₁ hu₁_P0, hu₁_Z]
      exact ⟨u₁, u₂, h_plus, hu₂_ne, hu₁_H0, hX_pres u₁ hu₁_H0, hu₁_Z, hu₂_Z⟩
    · push_neg at h_plus
      have hv_Z : Z_log v = -v := eq_neg_of_add_eq_zero_right h_plus
      let u₂ := X_log v
      have hu₂_ne : u₂ ≠ 0 := by
        intro h0
        have : X_log u₂ = 0 := by rw [h0, map_zero]
        rw [show X_log u₂ = (X_log * X_log) v from rfl, hX_inv, ContinuousLinearMap.one_apply] at this
        exact hψ₀ this
      have hu₂_Z : Z_log u₂ = u₂ := by
        dsimp [u₂]
        rw [h_anti_P0 v hv_P0, hv_Z, map_neg, neg_neg]
      exact ⟨u₂, v, hu₂_ne, hψ₀, hX_pres v hv_H0, hv_H0, hu₂_Z, hv_Z⟩
  rcases h_pair with ⟨w_pos, w_neg, hw_pos_ne, hw_neg_ne, hw_pos_H0, hw_neg_H0, hw_pos_Z, hw_neg_Z⟩
  let e_pos : sys.groundSpace := ⟨w_pos, h_mem_gs w_pos hw_pos_H0⟩
  let e_neg : sys.groundSpace := ⟨w_neg, h_mem_gs w_neg hw_neg_H0⟩
  let f : ℂ × ℂ →ₗ[ℂ] sys.groundSpace :=
    { toFun := fun p => p.1 • e_pos + p.2 • e_neg
      map_add' := fun p q => by
        ext1; push_cast; simp [add_smul, add_add_add_comm]
      map_smul' := fun c p => by
        ext1; push_cast; simp [mul_smul, smul_add] }
  have hf_inj : Function.Injective f := by
    intro p q hpq
    have h_diff : (p.1 - q.1) • w_pos + (p.2 - q.2) • w_neg = 0 := by
      have h_sub : f (p - q) = 0 := by rw [map_sub, hpq, sub_self]
      exact congrArg Subtype.val h_sub
    have h_Z_diff : (p.1 - q.1) • w_pos - (p.2 - q.2) • w_neg = 0 := by
      have hZ0 := congrArg Z_log h_diff
      rw [map_add, map_smul, map_smul, hw_pos_Z, hw_neg_Z, smul_neg, map_zero, ← sub_eq_add_neg] at hZ0
      exact hZ0
    have h1 : ((2 : ℂ) * (p.1 - q.1)) • w_pos = 0 := by
      calc ((2 : ℂ) * (p.1 - q.1)) • w_pos
        _ = (p.1 - q.1) • w_pos + (p.1 - q.1) • w_pos := by rw [two_mul, add_smul]
        _ = ((p.1 - q.1) • w_pos + (p.2 - q.2) • w_neg) +
            ((p.1 - q.1) • w_pos - (p.2 - q.2) • w_neg) := by abel
        _ = 0 := by rw [h_diff, h_Z_diff, add_zero]
    have h2 : ((2 : ℂ) * (p.2 - q.2)) • w_neg = 0 := by
      calc ((2 : ℂ) * (p.2 - q.2)) • w_neg
        _ = (p.2 - q.2) • w_neg + (p.2 - q.2) • w_neg := by rw [two_mul, add_smul]
        _ = ((p.1 - q.1) • w_pos + (p.2 - q.2) • w_neg) -
            ((p.1 - q.1) • w_pos - (p.2 - q.2) • w_neg) := by abel
        _ = 0 := by rw [h_diff, h_Z_diff, sub_self]
    have hp1 : p.1 = q.1 := by
      rcases smul_eq_zero.mp h1 with h_sc | h_vec
      · have h_sub_zero : p.1 - q.1 = 0 :=
          (mul_eq_zero.mp h_sc).resolve_left (by norm_num)
        exact sub_eq_zero.mp h_sub_zero
      · exact False.elim (hw_pos_ne h_vec)
    have hp2 : p.2 = q.2 := by
      rcases smul_eq_zero.mp h2 with h_sc | h_vec
      · have h_sub_zero : p.2 - q.2 = 0 :=
          (mul_eq_zero.mp h_sc).resolve_left (by norm_num)
        exact sub_eq_zero.mp h_sub_zero
      · exact False.elim (hw_neg_ne h_vec)
    exact Prod.ext hp1 hp2
  have h_finrank_le := LinearMap.finrank_le_finrank_of_injective hf_inj
  rw [Module.finrank_prod, Module.finrank_self] at h_finrank_le
  exact h_finrank_le

/-! ## 2. Isometric Reindexing of `EuclideanSpace` and Many-Body Operators -/

/-- Linear reindexing map `EuclideanSpace ℂ α →ₗ[ℂ] EuclideanSpace ℂ β` along `π : α ≃ β`. -/
def euclideanReindexLinear {α β : Type*} (π : α ≃ β) :
    EuclideanSpace ℂ α →ₗ[ℂ] EuclideanSpace ℂ β where
  toFun ψ := WithLp.toLp 2 (fun b => ψ.ofLp (π.symm b))
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Continuous linear reindexing map `EuclideanSpace ℂ α →L[ℂ] EuclideanSpace ℂ β`. -/
def uReindex {α β : Type*} [Fintype α] [Fintype β] (π : α ≃ β) :
    EuclideanSpace ℂ α →L[ℂ] EuclideanSpace ℂ β :=
  LinearMap.toContinuousLinearMap (euclideanReindexLinear π)

@[simp]
lemma uReindex_ofLp {α β : Type*} [Fintype α] [Fintype β]
    (π : α ≃ β) (ψ : EuclideanSpace ℂ α) (b : β) :
    (uReindex π ψ).ofLp b = ψ.ofLp (π.symm b) := rfl

@[simp]
lemma uReindex_symm_apply {α β : Type*} [Fintype α] [Fintype β]
    (π : α ≃ β) (ψ : EuclideanSpace ℂ α) :
    uReindex π.symm (uReindex π ψ) = ψ := by
  ext a; simp [uReindex_ofLp]

@[simp]
lemma uReindex_apply_symm {α β : Type*} [Fintype α] [Fintype β]
    (π : α ≃ β) (φ : EuclideanSpace ℂ β) :
    uReindex π (uReindex π.symm φ) = φ := by
  ext b; simp [uReindex_ofLp]

lemma inner_uReindex {α β : Type*} [Fintype α] [Fintype β]
    (π : α ≃ β) (x y : EuclideanSpace ℂ α) :
    inner ℂ (uReindex π x) (uReindex π y) = inner ℂ x y := by
  rw [inner_euclideanSpace_eq_bhm, inner_euclideanSpace_eq_bhm]
  exact π.symm.sum_comp (fun a => y.ofLp a * star (x.ofLp a))

lemma norm_uReindex {α β : Type*} [Fintype α] [Fintype β]
    (π : α ≃ β) (x : EuclideanSpace ℂ α) :
    ‖uReindex π x‖ = ‖x‖ := by
  have h1 := congrArg RCLike.re (inner_uReindex π x x)
  rw [inner_self_eq_norm_sq, inner_self_eq_norm_sq] at h1
  nlinarith [norm_nonneg (uReindex π x), norm_nonneg x]

/-- Conjugation of bounded linear operators on `EuclideanSpace` along `π : α ≃ β`. -/
def conjEuclidean {α β : Type*} [Fintype α] [Fintype β] (π : α ≃ β)
    (T : EuclideanSpace ℂ α →L[ℂ] EuclideanSpace ℂ α) :
    EuclideanSpace ℂ β →L[ℂ] EuclideanSpace ℂ β :=
  (uReindex π).comp (T.comp (uReindex π.symm))

@[simp]
lemma conjEuclidean_apply {α β : Type*} [Fintype α] [Fintype β] (π : α ≃ β)
    (T : EuclideanSpace ℂ α →L[ℂ] EuclideanSpace ℂ α) (φ : EuclideanSpace ℂ β) :
    conjEuclidean π T φ = uReindex π (T (uReindex π.symm φ)) := rfl

@[simp]
lemma conjEuclidean_zero {α β : Type*} [Fintype α] [Fintype β] (π : α ≃ β) :
    conjEuclidean π (0 : EuclideanSpace ℂ α →L[ℂ] EuclideanSpace ℂ α) = 0 := by
  ext φ b; simp [conjEuclidean_apply]

@[simp]
lemma conjEuclidean_one {α β : Type*} [Fintype α] [Fintype β] (π : α ≃ β) :
    conjEuclidean π (1 : EuclideanSpace ℂ α →L[ℂ] EuclideanSpace ℂ α) = 1 := by
  ext φ b; simp [conjEuclidean_apply]

@[simp]
lemma conjEuclidean_add {α β : Type*} [Fintype α] [Fintype β] (π : α ≃ β)
    (A B : EuclideanSpace ℂ α →L[ℂ] EuclideanSpace ℂ α) :
    conjEuclidean π (A + B) = conjEuclidean π A + conjEuclidean π B := by
  ext φ b; rfl

@[simp]
lemma conjEuclidean_sub {α β : Type*} [Fintype α] [Fintype β] (π : α ≃ β)
    (A B : EuclideanSpace ℂ α →L[ℂ] EuclideanSpace ℂ α) :
    conjEuclidean π (A - B) = conjEuclidean π A - conjEuclidean π B := by
  ext φ b; rfl

@[simp]
lemma conjEuclidean_neg {α β : Type*} [Fintype α] [Fintype β] (π : α ≃ β)
    (A : EuclideanSpace ℂ α →L[ℂ] EuclideanSpace ℂ α) :
    conjEuclidean π (-A) = -conjEuclidean π A := by
  ext φ b; rfl

@[simp]
lemma conjEuclidean_smul {α β : Type*} [Fintype α] [Fintype β] (π : α ≃ β)
    (c : ℂ) (A : EuclideanSpace ℂ α →L[ℂ] EuclideanSpace ℂ α) :
    conjEuclidean π (c • A) = c • conjEuclidean π A := by
  ext φ b; rfl

@[simp]
lemma conjEuclidean_mul {α β : Type*} [Fintype α] [Fintype β] (π : α ≃ β)
    (A B : EuclideanSpace ℂ α →L[ℂ] EuclideanSpace ℂ α) :
    conjEuclidean π (A * B) = conjEuclidean π A * conjEuclidean π B := by
  ext φ : 1
  change uReindex π (A (B (uReindex π.symm φ))) =
    uReindex π (A (uReindex π.symm (uReindex π (B (uReindex π.symm φ)))))
  rw [uReindex_symm_apply]

@[simp]
lemma conjEuclidean_symm_conjEuclidean {α β : Type*} [Fintype α] [Fintype β] (π : α ≃ β)
    (A : EuclideanSpace ℂ α →L[ℂ] EuclideanSpace ℂ α) :
    conjEuclidean π.symm (conjEuclidean π A) = A := by
  ext ψ : 1
  change uReindex π.symm (uReindex π (A (uReindex π.symm (uReindex π ψ)))) = A ψ
  rw [uReindex_symm_apply, uReindex_symm_apply]

@[simp]
lemma conjEuclidean_conjEuclidean_symm {α β : Type*} [Fintype α] [Fintype β] (π : α ≃ β)
    (B : EuclideanSpace ℂ β →L[ℂ] EuclideanSpace ℂ β) :
    conjEuclidean π (conjEuclidean π.symm B) = B :=
  conjEuclidean_symm_conjEuclidean π.symm B

lemma conjEuclidean_injective {α β : Type*} [Fintype α] [Fintype β] (π : α ≃ β) :
    Function.Injective (conjEuclidean π) := by
  intro A B h
  have := congrArg (conjEuclidean π.symm) h
  simpa using this

lemma conjEuclidean_eq_zero_iff {α β : Type*} [Fintype α] [Fintype β] (π : α ≃ β)
    (A : EuclideanSpace ℂ α →L[ℂ] EuclideanSpace ℂ α) :
    conjEuclidean π A = 0 ↔ A = 0 := by
  rw [← conjEuclidean_zero π]
  exact (conjEuclidean_injective π).eq_iff

lemma conjEuclidean_eq_one_iff {α β : Type*} [Fintype α] [Fintype β] (π : α ≃ β)
    (A : EuclideanSpace ℂ α →L[ℂ] EuclideanSpace ℂ α) :
    conjEuclidean π A = 1 ↔ A = 1 := by
  rw [← conjEuclidean_one π]
  exact (conjEuclidean_injective π).eq_iff

@[simp]
lemma conjEuclidean_adjoint {α β : Type*} [Fintype α] [Fintype β]
    (π : α ≃ β) (A : EuclideanSpace ℂ α →L[ℂ] EuclideanSpace ℂ α) :
    (conjEuclidean π A)† = conjEuclidean π (A†) := by
  ext ψ : 1
  apply ext_inner_left ℂ
  intro φ
  rw [ContinuousLinearMap.adjoint_inner_right]
  change inner ℂ (uReindex π (A (uReindex π.symm φ))) ψ =
    inner ℂ φ (uReindex π ((A†) (uReindex π.symm ψ)))
  have hψ : ψ = uReindex π (uReindex π.symm ψ) := (uReindex_apply_symm π ψ).symm
  conv_lhs => rw [hψ, inner_uReindex]
  have hφ : φ = uReindex π (uReindex π.symm φ) := (uReindex_apply_symm π φ).symm
  conv_rhs => rw [hφ, inner_uReindex]
  exact (ContinuousLinearMap.adjoint_inner_right A (uReindex π.symm φ) (uReindex π.symm ψ)).symm

lemma norm_conjEuclidean_le {α β : Type*} [Fintype α] [Fintype β]
    (π : α ≃ β) (A : EuclideanSpace ℂ α →L[ℂ] EuclideanSpace ℂ α) :
    ‖conjEuclidean π A‖ ≤ ‖A‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg A)
  intro φ
  calc ‖conjEuclidean π A φ‖
    _ = ‖uReindex π (A (uReindex π.symm φ))‖ := rfl
    _ = ‖A (uReindex π.symm φ)‖ := norm_uReindex π _
    _ ≤ ‖A‖ * ‖uReindex π.symm φ‖ := A.le_opNorm _
    _ = ‖A‖ * ‖φ‖ := by rw [norm_uReindex]

@[simp]
lemma norm_conjEuclidean {α β : Type*} [Fintype α] [Fintype β]
    (π : α ≃ β) (A : EuclideanSpace ℂ α →L[ℂ] EuclideanSpace ℂ α) :
    ‖conjEuclidean π A‖ = ‖A‖ := by
  apply le_antisymm (norm_conjEuclidean_le π A)
  have h := norm_conjEuclidean_le π.symm (conjEuclidean π A)
  rwa [conjEuclidean_symm_conjEuclidean] at h

lemma conjEuclidean_isSelfAdjoint {α β : Type*} [Fintype α] [Fintype β]
    (π : α ≃ β) {A : EuclideanSpace ℂ α →L[ℂ] EuclideanSpace ℂ α} (hA : IsSelfAdjoint A) :
    IsSelfAdjoint (conjEuclidean π A) := by
  rw [ContinuousLinearMap.isSelfAdjoint_iff'] at hA ⊢
  rw [conjEuclidean_adjoint, hA]

lemma conjEuclidean_isStarProjection {α β : Type*} [Fintype α] [Fintype β]
    (π : α ≃ β) {P : EuclideanSpace ℂ α →L[ℂ] EuclideanSpace ℂ α} (hP : IsStarProjection P) :
    IsStarProjection (conjEuclidean π P) := by
  refine ⟨?_, conjEuclidean_isSelfAdjoint π hP.isSelfAdjoint⟩
  rw [IsIdempotentElem, ← conjEuclidean_mul, hP.isIdempotentElem.eq]

lemma conjEuclidean_commute_iff {α β : Type*} [Fintype α] [Fintype β]
    (π : α ≃ β) (A B : EuclideanSpace ℂ α →L[ℂ] EuclideanSpace ℂ α) :
    Commute (conjEuclidean π A) (conjEuclidean π B) ↔ Commute A B := by
  rw [commute_iff_eq, commute_iff_eq, ← conjEuclidean_mul, ← conjEuclidean_mul]
  exact (conjEuclidean_injective π).eq_iff

lemma conjEuclidean_sum {α β ι : Type*} [Fintype α] [Fintype β]
    (π : α ≃ β) (s : Finset ι) (f : ι → (EuclideanSpace ℂ α →L[ℂ] EuclideanSpace ℂ α)) :
    conjEuclidean π (∑ i ∈ s, f i) = ∑ i ∈ s, conjEuclidean π (f i) := by
  induction s using Finset.cons_induction with
  | empty => simp
  | cons a s ha ih => rw [Finset.sum_cons, Finset.sum_cons, conjEuclidean_add, ih]

lemma conjEuclidean_list_prod {α β : Type*} [Fintype α] [Fintype β]
    (π : α ≃ β) (l : List (EuclideanSpace ℂ α →L[ℂ] EuclideanSpace ℂ α)) :
    conjEuclidean π l.prod = (l.map (conjEuclidean π)).prod := by
  induction l with
  | nil => simp
  | cons hd tl ih => rw [List.prod_cons, List.map_cons, List.prod_cons, conjEuclidean_mul, ih]

/-- Transport of a `unitary` operator along `π : α ≃ β`. -/
def conjEuclideanUnitary {α β : Type*} [Fintype α] [Fintype β] (π : α ≃ β)
    (U : unitary (EuclideanSpace ℂ α →L[ℂ] EuclideanSpace ℂ α)) :
    unitary (EuclideanSpace ℂ β →L[ℂ] EuclideanSpace ℂ β) :=
  ⟨conjEuclidean π U.1, by
    rw [Unitary.mem_iff]
    have hU := Unitary.mem_iff.mp U.2
    have h_star : ∀ A : EuclideanSpace ℂ α →L[ℂ] EuclideanSpace ℂ α,
        star (conjEuclidean π A) = conjEuclidean π (star A) :=
      fun A => conjEuclidean_adjoint π A
    rw [h_star, ← conjEuclidean_mul, ← conjEuclidean_mul, hU.1, hU.2, conjEuclidean_one]
    exact ⟨rfl, rfl⟩⟩

@[simp]
lemma conjEuclideanUnitary_coe {α β : Type*} [Fintype α] [Fintype β] (π : α ≃ β)
    (U : unitary (EuclideanSpace ℂ α →L[ℂ] EuclideanSpace ℂ α)) :
    (conjEuclideanUnitary π U).1 = conjEuclidean π U.1 := rfl

/-! ## 3. Site-Alphabet Transport of `cylinderOp`, `condExp`, and Hamiltonians -/

variable {D L : ℕ}
variable {Site0 Site1 : BoxD D L → Type}
variable [∀ x, Fintype (Site0 x)] [∀ x, DecidableEq (Site0 x)]
variable [∀ x, Fintype (Site1 x)] [∀ x, DecidableEq (Site1 x)]

/-- Global configuration equivalence induced by a sitewise equivalence `e : ∀ x, Site0 x ≃ Site1 x`. -/
def cfgEquiv (e : ∀ x : BoxD D L, Site0 x ≃ Site1 x) :
    ManyBodyConfig Site0 ≃ ManyBodyConfig Site1 :=
  Equiv.piCongrRight e

/-- Local configuration equivalence on `A ⊆ BoxD D L` induced by `e`. -/
def locCfgEquiv (e : ∀ x : BoxD D L, Site0 x ≃ Site1 x) (A : Finset (BoxD D L)) :
    LocalConfig Site0 A ≃ LocalConfig Site1 A :=
  Equiv.piCongrRight (fun x : A => e x.1)

/-- Transport of a global many-body operator along `e : ∀ x, Site0 x ≃ Site1 x`. -/
def conjSiteOp (e : ∀ x : BoxD D L, Site0 x ≃ Site1 x)
    (T : ManyBodyHilbertSpace Site0 →L[ℂ] ManyBodyHilbertSpace Site0) :
    ManyBodyHilbertSpace Site1 →L[ℂ] ManyBodyHilbertSpace Site1 :=
  conjEuclidean (cfgEquiv e) T

/-- Transport of a local operator on `A ⊆ BoxD D L` along `e`. -/
def conjLocOp (e : ∀ x : BoxD D L, Site0 x ≃ Site1 x) (A : Finset (BoxD D L))
    (T : LocalHilbertSpace Site0 A →L[ℂ] LocalHilbertSpace Site0 A) :
    LocalHilbertSpace Site1 A →L[ℂ] LocalHilbertSpace Site1 A :=
  conjEuclidean (locCfgEquiv e A) T

lemma cfgEquiv_spliceConfig (e : ∀ x : BoxD D L, Site0 x ≃ Site1 x)
    (A : Finset (BoxD D L)) (α : LocalConfig Site0 A) (σ : ManyBodyConfig Site1) :
    cfgEquiv e (spliceConfig A α ((cfgEquiv e).symm σ)) =
      spliceConfig A (locCfgEquiv e A α) σ := by
  funext x
  dsimp [cfgEquiv, locCfgEquiv, spliceConfig, Equiv.piCongrRight]
  split_ifs <;> simp

lemma conjSiteOp_cylinderOp (e : ∀ x : BoxD D L, Site0 x ≃ Site1 x)
    (A : Finset (BoxD D L))
    (O_loc : LocalHilbertSpace Site0 A →L[ℂ] LocalHilbertSpace Site0 A) :
    conjSiteOp e (cylinderOp Site0 A O_loc) =
      cylinderOp Site1 A (conjLocOp e A O_loc) := by
  ext ψ σ
  change (O_loc (WithLp.toLp 2 (fun α : LocalConfig Site0 A =>
      ψ.ofLp (cfgEquiv e (spliceConfig A α ((cfgEquiv e).symm σ)))))).ofLp
        (restrictConfig A ((cfgEquiv e).symm σ)) =
    (O_loc (WithLp.toLp 2 (fun α : LocalConfig Site0 A =>
      ψ.ofLp (spliceConfig A (locCfgEquiv e A α) σ)))).ofLp
        ((locCfgEquiv e A).symm (restrictConfig A σ))
  have h_arg :
      WithLp.toLp 2 (fun α : LocalConfig Site0 A =>
        ψ.ofLp (cfgEquiv e (spliceConfig A α ((cfgEquiv e).symm σ)))) =
      WithLp.toLp 2 (fun α : LocalConfig Site0 A =>
        ψ.ofLp (spliceConfig A (locCfgEquiv e A α) σ)) := by
    ext α
    change ψ.ofLp (cfgEquiv e (spliceConfig A α ((cfgEquiv e).symm σ))) =
      ψ.ofLp (spliceConfig A (locCfgEquiv e A α) σ)
    rw [cfgEquiv_spliceConfig]
  rw [h_arg]
  rfl

lemma isSupportedOn_conjSiteOp (e : ∀ x : BoxD D L, Site0 x ≃ Site1 x)
    {A : Finset (BoxD D L)}
    {O : ManyBodyHilbertSpace Site0 →L[ℂ] ManyBodyHilbertSpace Site0}
    (hO : IsSupportedOn Site0 A O) :
    IsSupportedOn Site1 A (conjSiteOp e O) := by
  rcases hO with ⟨O_loc, rfl⟩
  exact ⟨conjLocOp e A O_loc, conjSiteOp_cylinderOp e A O_loc⟩

lemma isSupportedOn_conjSiteOp_iff (e : ∀ x : BoxD D L, Site0 x ≃ Site1 x)
    (A : Finset (BoxD D L))
    (O : ManyBodyHilbertSpace Site0 →L[ℂ] ManyBodyHilbertSpace Site0) :
    IsSupportedOn Site1 A (conjSiteOp e O) ↔ IsSupportedOn Site0 A O := by
  constructor
  · intro h1
    have h0 := isSupportedOn_conjSiteOp (fun x => (e x).symm) h1
    have h_eq : conjSiteOp (fun x => (e x).symm) (conjSiteOp e O) = O :=
      conjEuclidean_symm_conjEuclidean (cfgEquiv e) O
    rwa [h_eq] at h0
  · exact isSupportedOn_conjSiteOp e

lemma uReindex_basisVecGlobal (e : ∀ x : BoxD D L, Site0 x ≃ Site1 x)
    (σ : ManyBodyConfig Site0) :
    uReindex (cfgEquiv e) (basisVecGlobal Site0 σ) =
      basisVecGlobal Site1 (cfgEquiv e σ) := by
  ext τ
  change (if (cfgEquiv e).symm τ = σ then (1 : ℂ) else 0) =
    (if τ = cfgEquiv e σ then (1 : ℂ) else 0)
  by_cases h : τ = cfgEquiv e σ
  · subst h; simp
  · have h' : (cfgEquiv e).symm τ ≠ σ := by
      intro h0; apply h; rw [← h0, Equiv.apply_symm_apply]
    simp [h, h']

lemma hilbertTrace_conjSiteOp (e : ∀ x : BoxD D L, Site0 x ≃ Site1 x)
    (A : ManyBodyHilbertSpace Site0 →L[ℂ] ManyBodyHilbertSpace Site0) :
    hilbertTrace (conjSiteOp e A) = hilbertTrace A := by
  dsimp [hilbertTrace, conjSiteOp]
  have h_term : ∀ τ : ManyBodyConfig Site1,
      RCLike.re (inner ℂ (basisVecGlobal Site1 τ)
        (conjEuclidean (cfgEquiv e) A (basisVecGlobal Site1 τ))) =
      RCLike.re (inner ℂ (basisVecGlobal Site0 ((cfgEquiv e).symm τ))
        (A (basisVecGlobal Site0 ((cfgEquiv e).symm τ)))) := by
    intro τ
    congr 1
    have h1 : uReindex (cfgEquiv e).symm (basisVecGlobal Site1 τ) =
        basisVecGlobal Site0 ((cfgEquiv e).symm τ) :=
      uReindex_basisVecGlobal (fun x => (e x).symm) τ
    have h2 : basisVecGlobal Site1 τ =
        uReindex (cfgEquiv e) (basisVecGlobal Site0 ((cfgEquiv e).symm τ)) := by
      rw [uReindex_basisVecGlobal, Equiv.apply_symm_apply]
    change inner ℂ (basisVecGlobal Site1 τ)
      (uReindex (cfgEquiv e) (A (uReindex (cfgEquiv e).symm (basisVecGlobal Site1 τ)))) = _
    rw [h1]
    conv_lhs => rw [h2]
    exact inner_uReindex (cfgEquiv e) _ _
  refine (Finset.sum_congr rfl fun τ _ => h_term τ).trans ?_
  exact (cfgEquiv e).symm.sum_comp
    (fun σ => RCLike.re (inner ℂ (basisVecGlobal Site0 σ) (A (basisVecGlobal Site0 σ))))

lemma cfgEquiv_combineConfig (e : ∀ x : BoxD D L, Site0 x ≃ Site1 x)
    (A : Finset (BoxD D L))
    (α : LocalConfig Site0 A) (γ : LocalConfig Site0 (Finset.univ \ A)) :
    cfgEquiv e (combineConfig A α γ) =
      combineConfig A (locCfgEquiv e A α) (locCfgEquiv e (Finset.univ \ A) γ) := by
  funext x
  dsimp [cfgEquiv, locCfgEquiv, combineConfig, Equiv.piCongrRight]
  split_ifs <;> rfl

lemma partialTraceEntry_conjSiteOp (e : ∀ x : BoxD D L, Site0 x ≃ Site1 x)
    (A : Finset (BoxD D L))
    (ρ : ManyBodyHilbertSpace Site0 →L[ℂ] ManyBodyHilbertSpace Site0)
    (γ : LocalConfig Site0 (Finset.univ \ A))
    (α β : LocalConfig Site0 A) :
    partialTraceEntry Site1 A (conjSiteOp e ρ)
        (locCfgEquiv e (Finset.univ \ A) γ) (locCfgEquiv e A α) (locCfgEquiv e A β) =
      partialTraceEntry Site0 A ρ γ α β := by
  dsimp [partialTraceEntry, conjSiteOp, conjEuclidean]
  rw [← cfgEquiv_combineConfig e A β γ, ← cfgEquiv_combineConfig e A α γ]
  have h_b : uReindex (cfgEquiv e).symm (basisVecGlobal Site1 (cfgEquiv e (combineConfig A β γ))) =
      basisVecGlobal Site0 (combineConfig A β γ) := by
    rw [← uReindex_basisVecGlobal e, uReindex_symm_apply]
  rw [h_b, Equiv.symm_apply_apply]

lemma partialTrace_conjSiteOp (e : ∀ x : BoxD D L, Site0 x ≃ Site1 x)
    (A : Finset (BoxD D L))
    (ρ : ManyBodyHilbertSpace Site0 →L[ℂ] ManyBodyHilbertSpace Site0) :
    partialTrace Site1 A (conjSiteOp e ρ) =
      conjLocOp e A (partialTrace Site0 A ρ) := by
  ext ψ α1
  obtain ⟨α0, rfl⟩ := (locCfgEquiv e A).surjective α1
  change (∑ γ : LocalConfig Site1 (Finset.univ \ A),
      ∑ β : LocalConfig Site1 A,
        partialTraceEntry Site1 A (conjSiteOp e ρ) γ (locCfgEquiv e A α0) β * ψ.ofLp β) =
    (uReindex (locCfgEquiv e A)
      (partialTrace Site0 A ρ (uReindex (locCfgEquiv e A).symm ψ))).ofLp
      (locCfgEquiv e A α0)
  rw [uReindex_ofLp, Equiv.symm_apply_apply]
  change (∑ γ : LocalConfig Site1 (Finset.univ \ A),
      ∑ β : LocalConfig Site1 A,
        partialTraceEntry Site1 A (conjSiteOp e ρ) γ (locCfgEquiv e A α0) β * ψ.ofLp β) =
    ∑ γ0 : LocalConfig Site0 (Finset.univ \ A),
      ∑ β0 : LocalConfig Site0 A,
        partialTraceEntry Site0 A ρ γ0 α0 β0 * ψ.ofLp (locCfgEquiv e A β0)
  rw [← (locCfgEquiv e (Finset.univ \ A)).sum_comp]
  refine Finset.sum_congr rfl fun γ0 _ => ?_
  rw [← (locCfgEquiv e A).sum_comp]
  refine Finset.sum_congr rfl fun β0 _ => ?_
  rw [partialTraceEntry_conjSiteOp]

lemma condExp_conjSiteOp (e : ∀ x : BoxD D L, Site0 x ≃ Site1 x)
    (A : Finset (BoxD D L))
    (O : ManyBodyHilbertSpace Site0 →L[ℂ] ManyBodyHilbertSpace Site0) :
    condExp Site1 A (conjSiteOp e O) =
      conjSiteOp e (condExp Site0 A O) := by
  dsimp [condExp]
  have h_card : Fintype.card (LocalConfig Site1 (Finset.univ \ A)) =
      Fintype.card (LocalConfig Site0 (Finset.univ \ A)) :=
    Fintype.card_congr (locCfgEquiv e (Finset.univ \ A)).symm
  rw [h_card, partialTrace_conjSiteOp, conjSiteOp_cylinderOp]
  rfl

/-- Transport an `IndexedCommutingProjectorHamiltonian` along `e : ∀ x, Site0 x ≃ Site1 x`. -/
def reindexHamiltonian {ι : Type} [Fintype ι] [DecidableEq ι]
    (e : ∀ x : BoxD D L, Site0 x ≃ Site1 x)
    (sys : IndexedCommutingProjectorHamiltonian D L Site0 ι) :
    IndexedCommutingProjectorHamiltonian D L Site1 ι where
  checkProj i := conjSiteOp e (sys.checkProj i)
  weight := sys.weight
  support := sys.support
  is_projector i := conjEuclidean_isStarProjection (cfgEquiv e) (sys.is_projector i)
  is_supported i := isSupportedOn_conjSiteOp e (sys.is_supported i)
  pairwise_commute i j := (conjEuclidean_commute_iff (cfgEquiv e) _ _).mpr (sys.pairwise_commute i j)
  weight_ge_one := sys.weight_ge_one
  frustration_free := by
    have h_fn : (fun i : ι => 1 - conjSiteOp e (sys.checkProj i)) =
        (conjSiteOp e ∘ fun i : ι => 1 - sys.checkProj i) := by
      funext i; simp [conjSiteOp]
    have h_map : ((Finset.univ : Finset ι).toList.map (fun i => 1 - conjSiteOp e (sys.checkProj i))).prod =
        conjSiteOp e (((Finset.univ : Finset ι).toList.map (fun i => 1 - sys.checkProj i)).prod) := by
      rw [h_fn, ← List.map_map]
      exact (conjEuclidean_list_prod (cfgEquiv e) _).symm
    rw [h_map]
    exact mt (conjEuclidean_eq_zero_iff (cfgEquiv e) _).mp sys.frustration_free

lemma reindexHamiltonian_H0 {ι : Type} [Fintype ι] [DecidableEq ι]
    (e : ∀ x : BoxD D L, Site0 x ≃ Site1 x)
    (sys : IndexedCommutingProjectorHamiltonian D L Site0 ι) :
    (reindexHamiltonian e sys).H0 = conjSiteOp e sys.H0 := by
  dsimp [IndexedCommutingProjectorHamiltonian.H0, reindexHamiltonian, conjSiteOp]
  rw [conjEuclidean_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [conjEuclidean_smul]

lemma reindexHamiltonian_P0 {ι : Type} [Fintype ι] [DecidableEq ι]
    (e : ∀ x : BoxD D L, Site0 x ≃ Site1 x)
    (sys : IndexedCommutingProjectorHamiltonian D L Site0 ι) :
    (reindexHamiltonian e sys).P0 = conjSiteOp e sys.P0 := by
  dsimp [IndexedCommutingProjectorHamiltonian.P0, IndexedCommutingProjectorHamiltonian.groundProj,
    reindexHamiltonian]
  have h_fn : (fun i : ι => 1 - conjSiteOp e (sys.checkProj i)) =
      (conjSiteOp e ∘ fun i : ι => 1 - sys.checkProj i) := by
    funext i; simp [conjSiteOp]
  rw [h_fn, ← List.map_map]
  exact (conjEuclidean_list_prod (cfgEquiv e) _).symm

lemma reindexHamiltonian_syndromeProjector {ι : Type} [Fintype ι] [DecidableEq ι]
    (e : ∀ x : BoxD D L, Site0 x ≃ Site1 x)
    (sys : IndexedCommutingProjectorHamiltonian D L Site0 ι) (σ : ι → Bool) :
    (reindexHamiltonian e sys).syndromeProjector σ =
      conjSiteOp e (sys.syndromeProjector σ) := by
  dsimp [IndexedCommutingProjectorHamiltonian.syndromeProjector, reindexHamiltonian]
  have h_fn : (fun i : ι => if σ i then conjSiteOp e (sys.checkProj i) else 1 - conjSiteOp e (sys.checkProj i)) =
      (conjSiteOp e ∘ fun i : ι => if σ i then sys.checkProj i else 1 - sys.checkProj i) := by
    funext i
    by_cases h : σ i = true <;> simp [h, conjSiteOp]
  rw [h_fn, ← List.map_map]
  exact (conjEuclidean_list_prod (cfgEquiv e) _).symm

lemma syndromeSubsetProj_reindexHamiltonian {ι : Type} [Fintype ι] [DecidableEq ι]
    (e : ∀ x : BoxD D L, Site0 x ≃ Site1 x)
    (sys : IndexedCommutingProjectorHamiltonian D L Site0 ι) (S : Finset (ι → Bool)) :
    syndromeSubsetProj (reindexHamiltonian e sys) S =
      conjSiteOp e (syndromeSubsetProj sys S) := by
  dsimp [syndromeSubsetProj, conjSiteOp]
  rw [conjEuclidean_sum]
  refine Finset.sum_congr rfl fun σ _ => reindexHamiltonian_syndromeProjector e sys σ

lemma gibbsPartitionZ_reindexHamiltonian {ι : Type} [Fintype ι] [DecidableEq ι]
    [∀ x, Nonempty (Site0 x)] [∀ x, Nonempty (Site1 x)]
    (e : ∀ x : BoxD D L, Site0 x ≃ Site1 x)
    (sys : IndexedCommutingProjectorHamiltonian D L Site0 ι) (β : ℝ) :
    gibbsPartitionZ (opEigenvalues (reindexHamiltonian e sys).H0 (reindexHamiltonian e sys).isSelfAdjoint_H0) β =
      gibbsPartitionZ (opEigenvalues sys.H0 sys.isSelfAdjoint_H0) β := by
  rw [gibbsPartitionZ_eq_sum_syndromeProjector (reindexHamiltonian e sys) β,
    gibbsPartitionZ_eq_sum_syndromeProjector sys β]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [reindexHamiltonian_syndromeProjector, hilbertTrace_conjSiteOp]
  rfl

lemma gibbsFailureProb_reindexHamiltonian_syndromeSubsetProj {ι : Type} [Fintype ι] [DecidableEq ι]
    [∀ x, Nonempty (Site0 x)] [∀ x, Nonempty (Site1 x)]
    (e : ∀ x : BoxD D L, Site0 x ≃ Site1 x)
    (sys : IndexedCommutingProjectorHamiltonian D L Site0 ι)
    (Safe : Finset (ι → Bool)) (β : ℝ) :
    gibbsFailureProb (reindexHamiltonian e sys).H0 (reindexHamiltonian e sys).isSelfAdjoint_H0 β
        (1 - syndromeSubsetProj (reindexHamiltonian e sys) Safe) =
      gibbsFailureProb sys.H0 sys.isSelfAdjoint_H0 β
        (1 - syndromeSubsetProj sys Safe) := by
  have h1 := (syndromeSubsetProj_props (reindexHamiltonian e sys) Safe).2.2.2.2
  have h0 := (syndromeSubsetProj_props sys Safe).2.2.2.2
  dsimp [gibbsFailureProb]
  rw [h1, h0]
  dsimp [syndromeSubsetProj]
  rw [Finset.mul_sum, Finset.mul_sum, hilbertTrace_sum, hilbertTrace_sum]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [hilbertTrace_gibbsDensityOp_mul_syndromeProjector (reindexHamiltonian e sys) β σ,
    hilbertTrace_gibbsDensityOp_mul_syndromeProjector sys β σ,
    gibbsPartitionZ_reindexHamiltonian e sys β,
    reindexHamiltonian_syndromeProjector e sys σ,
    hilbertTrace_conjSiteOp]
  rfl

/-- Transport a `QuasiLocalPerturbation` along `e : ∀ x, Site0 x ≃ Site1 x`. -/
def reindexPerturbation (e : ∀ x : BoxD D L, Site0 x ≃ Site1 x)
    (V : QuasiLocalPerturbation D L Site0) :
    QuasiLocalPerturbation D L Site1 where
  term r A := conjSiteOp e (V.term r A)
  is_selfAdjoint r A := conjEuclidean_isSelfAdjoint (cfgEquiv e) (V.is_selfAdjoint r A)
  is_supported r hr A hA := isSupportedOn_conjSiteOp e (V.is_supported r hr A hA)

lemma reindexPerturbation_V_tot (e : ∀ x : BoxD D L, Site0 x ≃ Site1 x)
    (V : QuasiLocalPerturbation D L Site0) :
    (reindexPerturbation e V).totalPerturbation = conjSiteOp e V.totalPerturbation := by
  dsimp [QuasiLocalPerturbation.totalPerturbation, reindexPerturbation, conjSiteOp]
  rw [conjEuclidean_sum]
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [conjEuclidean_sum]

end Part1TwoAxisMemorySynthesis

end
