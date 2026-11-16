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

import Proofs.InhomogeneousPeierls.LocalWeylPauliExpansion
import Proofs.ConeAcyclicityRCA.SixCheckpointCleanShell
import Defs.BHMStability

/-!
# Quantum Operator TQO-1 and Linear TQO-2 from F2 Cone Acyclicity

Lifts classical F2 linear TQO on a descriptor field to full quantum operator `SatisfiesTQO1` and `SatisfiesLinearTQO2` via Weyl-Pauli expansion and stabilizer phase cancellation (`staticCSSSystem_satisfiesOperatorTQO`). Instantiates the cubic-grid commuting-projector Hamiltonian `bdlInhomogeneousSystem k` and proves `bdlInhomogeneousSystem_satisfiesOperatorTQO` with non-degenerate ground projector bounds.

## References

* Part I, Section 3.1 (`subsec:rca-trinity`), Definition 3.2 (`def:tqo`), Proposition 3.3 (`prop:trinity-equivalence`)
* Part I, Section 3.3 (`subsec:scale-matched-rca`), Theorem 3.9 (`thm:rca-welded-hierarchy`)
* Part II, Section 2 (`subsec:setup`), Definition 2.2 (`def:RCA`)
* Part II, Section 4 (`subsec:welded-hierarchy-cleaner`), Proposition 4.3 (`prop:rca-hierarchy`)
-/

noncomputable section

open scoped Classical BigOperators InnerProduct ComplexConjugate
open ContinuousLinearMap

set_option linter.constructorNameAsVariable false
set_option maxRecDepth 200000

/-! ## 1. Open-Box Enclosing Cube Inclusion & Weyl–Pauli TQO Step -/

lemma boxCube_subset_enclosingBoxCube_of_le {L r R : ℕ}
    (x0 : Box3D L) (hR : r ≤ R) :
    boxCube x0 r ⊆ enclosingBoxCube x0 r R := by
  intro y hy
  have hy_cube := (Finset.mem_filter.mp hy).2
  refine Finset.mem_filter.mpr ⟨Finset.mem_univ y, fun μ => ?_⟩
  have hμ := hy_cube μ
  dsimp
  omega

lemma boxBall_subset_enclosingBoxCube_of_shiftOpenBox_mem_boxCube {L r_0 r R : ℕ}
    (x0 v w : Box3D L) (nb : LocalNeighborhoodIdx r_0)
    (hR : r + 4 * r_0 + 2 ≤ R)
    (hw : w ∈ boxCube x0 r)
    (h_in : InOpenBox v (neighborhoodOffset r_0 nb))
    (h_sh : shiftOpenBox v (neighborhoodOffset r_0 nb) = w) :
    boxBall v r_0 ⊆ enclosingBoxCube x0 r R := by
  have hw_cube := (Finset.mem_filter.mp hw).2
  have h_vw : ∀ μ : Fin 3,
      (v μ).val ≤ (w μ).val + r_0 ∧ (w μ).val ≤ (v μ).val + r_0 := by
    intro μ
    have h_nb := (nb μ).isLt
    have h_in_μ := h_in μ
    have h_sh_μ : (shiftOpenBox v (neighborhoodOffset r_0 nb) μ).val = (w μ).val :=
      congr_arg Fin.val (congr_fun h_sh μ)
    dsimp [shiftOpenBox, shiftOpenBoxD] at h_sh_μ
    rw [dif_pos h_in_μ] at h_sh_μ
    dsimp [neighborhoodOffset] at h_in_μ h_sh_μ
    omega
  intro z hz
  have hz_ball : boxDist v z ≤ r_0 := (Finset.mem_filter.mp hz).2
  refine Finset.mem_filter.mpr ⟨Finset.mem_univ z, fun μ => ?_⟩
  have h_coord : coordDist (v μ) (z μ) ≤ r_0 := by
    dsimp [boxDist] at hz_ball
    exact le_trans
      (Finset.le_sup (f := fun i : Fin 3 => coordDist (v i) (z i)) (Finset.mem_univ μ))
      hz_ball
  have hw_μ := hw_cube μ
  have hvw_μ := h_vw μ
  dsimp [coordDist] at h_coord ⊢
  omega

private lemma mul_right_eq_of_left_mul_eq_self {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] [CompleteSpace E] {U P : E →L[ℂ] E}
    (hU : IsSelfAdjoint U) (hP : IsSelfAdjoint P) (h : U * P = P) :
    P * U = P := by
  have h_adj : star (U * P) = star P := congr_arg star h
  rwa [star_mul, hU.star_eq, hP.star_eq] at h_adj

lemma staticCSS_pauli_tqo_step {L q_code r_0 m_max L_star : ℕ}
    (ω : Box3D L → LocalCSSDescriptor q_code r_0 m_max)
    (C : ℝ) (h_valid : ValidDescriptorField ω)
    (h_f2 : SatisfiesBoxF2LinearTQO ω L_star C)
    (hC : ((4 * r_0 + 3 : ℕ) : ℝ) ≤ C)
    {r : ℕ} (hr1 : 1 ≤ r) (hrL : r ≤ L_star) (x0 : Box3D L)
    (a b : BoxSlot3D L q_code → ZMod 2)
    (ha_supp : BoxSlotChainSupportedIn a (boxCube x0 r))
    (hb_supp : BoxSlotChainSupportedIn b (boxCube x0 r)) :
    let sys := staticCSSSystem ω h_valid
    let B := enclosingBoxCube x0 r (linearExpansionRadius C r)
    ∃ c : ℂ,
      sys.localGroundProj B * (weylPauliZ a * weylPauliX b) * sys.localGroundProj B = c • sys.localGroundProj B ∧
      sys.P0 * (weylPauliZ a * weylPauliX b) * sys.P0 = c • sys.P0 := by
  intro sys B
  have hR_ge : r + 4 * r_0 + 2 ≤ linearExpansionRadius C r := by
    dsimp [linearExpansionRadius]
    have hr1_real : (1 : ℝ) ≤ (r : ℝ) := Nat.one_le_cast.mpr hr1
    have h_real : ((r + 4 * r_0 + 2 : ℕ) : ℝ) ≤ C * (r : ℝ) := by
      push_cast at hC ⊢
      nlinarith
    exact_mod_cast le_trans h_real (Nat.le_ceil (C * (r : ℝ)))
  have h_r_le_R : r ≤ linearExpansionRadius C r := by omega
  by_cases hb_act : ∀ p : BoxSlot3D L q_code, b p ≠ 0 → (ω p.1).activeSlot p.2 = true
  · by_cases ha_syn : ∀ (v : Box3D L) (idx : Fin m_max), idx.val < (ω v).numXChecks.val →
        (∑ p : BoxSlot3D L q_code, a p * descriptorCheckXChain ω v idx p) = 0
    · by_cases hb_syn : ∀ (v : Box3D L) (idx : Fin m_max), idx.val < (ω v).numZChecks.val →
          (∑ p : BoxSlot3D L q_code, b p * descriptorCheckZChain ω v idx p) = 0
      · obtain ⟨⟨c_pin, c_Z, h_pin_supp, h_Z_supp, ha_eq⟩, ⟨c_X, h_X_supp, hb_eq⟩⟩ :=
          boxF2LinearTQO_stabilizer_decomp ω L_star C h_valid h_f2 hr1 hrL x0 a b
            ha_supp hb_supp hb_act ha_syn hb_syn
        have hX_Ploc : weylPauliX b * sys.localGroundProj B = sys.localGroundProj B := by
          rw [hb_eq]
          exact weylPauliX_finset_sum_mul_eq (E := ℂ) Finset.univ c_X
            (fun p => descriptorCheckXChain ω p.1 p.2) (sys.localGroundProj B)
            (fun p _ hp => weylPauliX_descriptorCheckXChain_mul_P_loc ω h_valid p.1 p.2 B
              (h_X_supp p hp).1 (h_X_supp p hp).2)
        have hX_P0 : weylPauliX b * sys.P0 = sys.P0 := by
          rw [hb_eq]
          exact weylPauliX_finset_sum_mul_eq (E := ℂ) Finset.univ c_X
            (fun p => descriptorCheckXChain ω p.1 p.2) sys.P0
            (fun p _ hp => weylPauliX_descriptorCheckXChain_mul_P0 ω h_valid p.1 p.2
              (h_X_supp p hp).1)
        have hZ_Ploc : weylPauliZ a * sys.localGroundProj B = sys.localGroundProj B := by
          rw [ha_eq, weylPauliZ_add, mul_assoc,
            weylPauliZ_finset_sum_mul_eq (E := ℂ) Finset.univ c_Z
              (fun p => descriptorCheckZChain ω p.1 p.2) (sys.localGroundProj B)
              (fun p _ hp => weylPauliZ_descriptorCheckZChain_mul_P_loc ω h_valid p.1 p.2 B
                (h_Z_supp p hp).1 (h_Z_supp p hp).2),
            weylPauliZ_finset_sum_mul_eq (E := ℂ) Finset.univ c_pin
              (fun p => singleSlotChain p.1 p.2) (sys.localGroundProj B)
              (fun p _ hp => weylPauliZ_singleSlotChain_mul_P_loc ω h_valid p.1 p.2 B
                (h_pin_supp p hp).1 (h_pin_supp p hp).2)]
        have hZ_P0 : weylPauliZ a * sys.P0 = sys.P0 := by
          rw [ha_eq, weylPauliZ_add, mul_assoc,
            weylPauliZ_finset_sum_mul_eq (E := ℂ) Finset.univ c_Z
              (fun p => descriptorCheckZChain ω p.1 p.2) sys.P0
              (fun p _ hp => weylPauliZ_descriptorCheckZChain_mul_P0 ω h_valid p.1 p.2
                (h_Z_supp p hp).1),
            weylPauliZ_finset_sum_mul_eq (E := ℂ) Finset.univ c_pin
              (fun p => singleSlotChain p.1 p.2) sys.P0
              (fun p _ hp => weylPauliZ_singleSlotChain_mul_P0 ω h_valid p.1 p.2
                (h_pin_supp p hp).1)]
        refine ⟨1, ?_, ?_⟩
        · rw [one_smul, mul_assoc (sys.localGroundProj B), mul_assoc (weylPauliZ a), hX_Ploc, hZ_Ploc,
            (sys.isStarProjection_P_loc_bhm B).isIdempotentElem.eq]
        · rw [one_smul, mul_assoc sys.P0, mul_assoc (weylPauliZ a), hX_P0, hZ_P0,
            sys.isStarProjection_P0.isIdempotentElem.eq]
      · push_neg at hb_syn
        rcases hb_syn with ⟨v, idx, h_lt, h_syn_ne⟩
        have h_syn_one : (∑ p : BoxSlot3D L q_code, descriptorCheckZChain ω v idx p * b p) = 1 := by
          have h_comm : (∑ p : BoxSlot3D L q_code, descriptorCheckZChain ω v idx p * b p) =
              ∑ p : BoxSlot3D L q_code, b p * descriptorCheckZChain ω v idx p :=
            Finset.sum_congr rfl (fun p _ => mul_comm _ _)
          rw [h_comm]
          rcases zmod2_eq_zero_or_one (∑ p, b p * descriptorCheckZChain ω v idx p) with h0 | h1
          · exact False.elim (h_syn_ne h0)
          · exact h1
        obtain ⟨⟨w, s⟩, _, h_prod_ne⟩ := Finset.exists_ne_zero_of_sum_ne_zero h_syn_ne
        have hw_mem : w ∈ boxCube x0 r := hb_supp (w, s) (left_ne_zero_of_mul h_prod_ne)
        have h_chk_ne : descriptorCheckZChain ω v idx (w, s) ≠ 0 := right_ne_zero_of_mul h_prod_ne
        dsimp [descriptorCheckZChain] at h_chk_ne
        split_ifs at h_chk_ne with h_ex
        · rcases h_ex with ⟨_, nb, h_in, h_sh, _⟩
          have hB_sub : boxBall v r_0 ⊆ B :=
            boxBall_subset_enclosingBoxCube_of_shiftOpenBox_mem_boxCube x0 v w nb hR_ge hw_mem h_in h_sh
          have hU_Ploc := weylPauliZ_descriptorCheckZChain_mul_P_loc ω h_valid v idx B h_lt hB_sub
          have hU_P0 := weylPauliZ_descriptorCheckZChain_mul_P0 ω h_valid v idx h_lt
          have hU_sa := weylPauliZ_isSelfAdjoint (descriptorCheckZChain ω v idx)
          have h_conj := conjugation_neg_of_weylPauliZ_anticomm (descriptorCheckZChain ω v idx) a b h_syn_one
          refine ⟨(0 : ℂ), ?_, ?_⟩
          · rw [clm_zero_smul]
            exact sandwich_eq_zero_of_anticomm
              (mul_right_eq_of_left_mul_eq_self hU_sa (sys.isStarProjection_P_loc_bhm B).isSelfAdjoint hU_Ploc)
              hU_Ploc h_conj
          · rw [clm_zero_smul]
            exact sandwich_eq_zero_of_anticomm
              (mul_right_eq_of_left_mul_eq_self hU_sa sys.isStarProjection_P0.isSelfAdjoint hU_P0)
              hU_P0 h_conj
        · exact False.elim (h_chk_ne rfl)
    · push_neg at ha_syn
      rcases ha_syn with ⟨v, idx, h_lt, h_syn_ne⟩
      have h_syn_one : (∑ p : BoxSlot3D L q_code, a p * descriptorCheckXChain ω v idx p) = 1 := by
        rcases zmod2_eq_zero_or_one (∑ p, a p * descriptorCheckXChain ω v idx p) with h0 | h1
        · exact False.elim (h_syn_ne h0)
        · exact h1
      obtain ⟨⟨w, s⟩, _, h_prod_ne⟩ := Finset.exists_ne_zero_of_sum_ne_zero h_syn_ne
      have hw_mem : w ∈ boxCube x0 r := ha_supp (w, s) (left_ne_zero_of_mul h_prod_ne)
      have h_chk_ne : descriptorCheckXChain ω v idx (w, s) ≠ 0 := right_ne_zero_of_mul h_prod_ne
      dsimp [descriptorCheckXChain] at h_chk_ne
      split_ifs at h_chk_ne with h_ex
      · rcases h_ex with ⟨_, nb, h_in, h_sh, _⟩
        have hB_sub : boxBall v r_0 ⊆ B :=
          boxBall_subset_enclosingBoxCube_of_shiftOpenBox_mem_boxCube x0 v w nb hR_ge hw_mem h_in h_sh
        have hU_Ploc := weylPauliX_descriptorCheckXChain_mul_P_loc ω h_valid v idx B h_lt hB_sub
        have hU_P0 := weylPauliX_descriptorCheckXChain_mul_P0 ω h_valid v idx h_lt
        have hU_sa := weylPauliX_isSelfAdjoint (descriptorCheckXChain ω v idx)
        have h_conj := conjugation_neg_of_weylPauliX_anticomm (descriptorCheckXChain ω v idx) a b h_syn_one
        refine ⟨(0 : ℂ), ?_, ?_⟩
        · rw [clm_zero_smul]
          exact sandwich_eq_zero_of_anticomm
            (mul_right_eq_of_left_mul_eq_self hU_sa (sys.isStarProjection_P_loc_bhm B).isSelfAdjoint hU_Ploc)
            hU_Ploc h_conj
        · rw [clm_zero_smul]
          exact sandwich_eq_zero_of_anticomm
            (mul_right_eq_of_left_mul_eq_self hU_sa sys.isStarProjection_P0.isSelfAdjoint hU_P0)
            hU_P0 h_conj
      · exact False.elim (h_chk_ne rfl)
  · push_neg at hb_act
    rcases hb_act with ⟨⟨v, s⟩, hb_ne, h_not_act⟩
    have h_inact : (ω v).activeSlot s = false := Bool.eq_false_iff.mpr h_not_act
    have hvB : v ∈ B := boxCube_subset_enclosingBoxCube_of_le x0 h_r_le_R (hb_supp (v, s) hb_ne)
    have h_syn_one : (∑ p : BoxSlot3D L q_code, singleSlotChain v s p * b p) = 1 := by
      rw [Finset.sum_eq_single (v, s)]
      · dsimp [singleSlotChain]
        rw [if_pos rfl, one_mul]
        rcases zmod2_eq_zero_or_one (b (v, s)) with h0 | h1
        · exact False.elim (hb_ne h0)
        · exact h1
      · intro p _ hne
        dsimp [singleSlotChain]
        rw [if_neg hne, zero_mul]
      · intro h_abs
        exact False.elim (h_abs (Finset.mem_univ (v, s)))
    have hU_Ploc := weylPauliZ_singleSlotChain_mul_P_loc ω h_valid v s B h_inact hvB
    have hU_P0 := weylPauliZ_singleSlotChain_mul_P0 ω h_valid v s h_inact
    have hU_sa := weylPauliZ_isSelfAdjoint (singleSlotChain v s)
    have h_conj := conjugation_neg_of_weylPauliZ_anticomm (singleSlotChain v s) a b h_syn_one
    refine ⟨(0 : ℂ), ?_, ?_⟩
    · rw [clm_zero_smul]
      exact sandwich_eq_zero_of_anticomm
        (mul_right_eq_of_left_mul_eq_self hU_sa (sys.isStarProjection_P_loc_bhm B).isSelfAdjoint hU_Ploc)
        hU_Ploc h_conj
    · rw [clm_zero_smul]
      exact sandwich_eq_zero_of_anticomm
        (mul_right_eq_of_left_mul_eq_self hU_sa sys.isStarProjection_P0.isSelfAdjoint hU_P0)
        hU_P0 h_conj

/-! ## 2. Operator TQO-1, Linear TQO-2, and Sector-Filtered Linear TQO-2 for `staticCSSSystem` -/

lemma staticCSS_operator_sandwich_eq {L q_code r_0 m_max L_star : ℕ}
    (ω : Box3D L → LocalCSSDescriptor q_code r_0 m_max)
    (C : ℝ) (h_valid : ValidDescriptorField ω)
    (h_f2 : SatisfiesBoxF2LinearTQO ω L_star C)
    (hC : ((4 * r_0 + 3 : ℕ) : ℝ) ≤ C)
    {r : ℕ} (hr1 : 1 ≤ r) (hrL : r ≤ L_star) (x0 : Box3D L)
    (O_A : ManyBodyHilbertSpace (UniformSite3D L (CodeSlotConfig q_code)) →L[ℂ]
      ManyBodyHilbertSpace (UniformSite3D L (CodeSlotConfig q_code)))
    (h_supp : IsSupportedOn (UniformSite3D L (CodeSlotConfig q_code)) (boxCube x0 r) O_A) :
    let sys := staticCSSSystem ω h_valid
    let B := enclosingBoxCube x0 r (linearExpansionRadius C r)
    ∃ c : ℂ,
      sys.localGroundProj B * O_A * sys.localGroundProj B = c • sys.localGroundProj B ∧
      sys.P0 * O_A * sys.P0 = c • sys.P0 := by
  intro sys B
  obtain ⟨ι, hι, w, a_fam, b_fam, ha_fam, hb_fam, hO_eq⟩ :=
    exists_weylPauli_expansion_of_isSupportedOn (boxCube x0 r) h_supp
  letI : Fintype ι := hι
  have h_term : ∀ i : ι,
      ∃ c_i : ℂ,
        sys.localGroundProj B * (weylPauliZ (a_fam i) * weylPauliX (b_fam i)) * sys.localGroundProj B = c_i • sys.localGroundProj B ∧
        sys.P0 * (weylPauliZ (a_fam i) * weylPauliX (b_fam i)) * sys.P0 = c_i • sys.P0 :=
    fun i => staticCSS_pauli_tqo_step ω C h_valid h_f2 hC hr1 hrL x0 (a_fam i) (b_fam i)
      (ha_fam i) (hb_fam i)
  let c_of : ι → ℂ := fun i => Classical.choose (h_term i)
  have hc_spec : ∀ i : ι,
      sys.localGroundProj B * (weylPauliZ (a_fam i) * weylPauliX (b_fam i)) * sys.localGroundProj B = c_of i • sys.localGroundProj B ∧
      sys.P0 * (weylPauliZ (a_fam i) * weylPauliX (b_fam i)) * sys.P0 = c_of i • sys.P0 :=
    fun i => Classical.choose_spec (h_term i)
  refine ⟨∑ i : ι, w i * c_of i, ?_, ?_⟩
  · rw [hO_eq, Finset.mul_sum, Finset.sum_mul, clm_sum_smul]
    exact Finset.sum_congr rfl (fun i _ =>
      clm_sandwich_smul (sys.localGroundProj B) (weylPauliZ (a_fam i) * weylPauliX (b_fam i))
        (w i) (c_of i) (hc_spec i).1)
  · rw [hO_eq, Finset.mul_sum, Finset.sum_mul, clm_sum_smul]
    exact Finset.sum_congr rfl (fun i _ =>
      clm_sandwich_smul sys.P0 (weylPauliZ (a_fam i) * weylPauliX (b_fam i))
        (w i) (c_of i) (hc_spec i).2)

private lemma sum_partialTraceEntry_of_sandwich {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    (A : Finset (BoxD D L))
    (Q : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site)
    (hQ : IsStarProjection Q)
    (α β : LocalConfig Site A) (c : ℂ)
    (hc : Q * cylinderOp Site A (localUnitOp A α β) * Q = c • Q) :
    (∑ γ : LocalConfig Site (Finset.univ \ A), partialTraceEntry Site A Q γ α β) =
      c * complexTrace Q := by
  calc ∑ γ : LocalConfig Site (Finset.univ \ A), partialTraceEntry Site A Q γ α β
    _ = complexTrace (cylinderOp Site A (localUnitOp A α β) * Q) :=
      sum_partialTraceEntry_eq_complexTrace A Q α β
    _ = complexTrace (cylinderOp Site A (localUnitOp A α β) * (Q * Q)) := by
      rw [hQ.isIdempotentElem.eq]
    _ = complexTrace (Q * (cylinderOp Site A (localUnitOp A α β) * Q)) := by
      rw [← mul_assoc, complexTrace_mul_comm]
    _ = complexTrace (Q * cylinderOp Site A (localUnitOp A α β) * Q) := by
      rw [mul_assoc]
    _ = complexTrace (c • Q) := by rw [hc]
    _ = c * complexTrace Q := complexTrace_smul c Q

private lemma clm_eq_zero_of_star_mul_self_eq_zero {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] [CompleteSpace E] {M : E →L[ℂ] E}
    (h : star M * M = 0) : M = 0 := by
  have h_norm : ‖star M * M‖ = 0 := by rw [h, norm_zero]
  have h_cstar : ‖star M * M‖ = ‖M‖ * ‖M‖ := CStarRing.norm_star_mul_self
  exact norm_eq_zero.mp (mul_self_eq_zero.mp (h_cstar.symm.trans h_norm))

theorem staticCSSSystem_satisfiesOperatorTQO {L q_code r_0 m_max L_star : ℕ}
    (ω : Box3D L → LocalCSSDescriptor q_code r_0 m_max)
    (C : ℝ) (h_valid : ValidDescriptorField ω)
    (h_f2 : SatisfiesBoxF2LinearTQO ω L_star C)
    (hC : ((4 * r_0 + 3 : ℕ) : ℝ) ≤ C) :
    let sys := staticCSSSystem ω h_valid
    SatisfiesTQO1 sys L_star ∧
    SatisfiesLinearTQO2 sys L_star C ∧
    SatisfiesSectorFilteredLinearTQO2 sys 1 L_star C := by
  intro sys
  have h_tqo1 : SatisfiesTQO1 sys L_star := by
    intro r hr1 hrL x0 _A O_A h_supp
    obtain ⟨c, _, hc_P0⟩ := staticCSS_operator_sandwich_eq ω C h_valid h_f2 hC hr1 hrL x0 O_A h_supp
    exact ⟨c, hc_P0⟩
  have h_tqo2 : SatisfiesLinearTQO2 sys L_star C := by
    intro r hr1 hrL x0
    let A := boxCube x0 r
    let B := enclosingBoxCube x0 r (linearExpansionRadius C r)
    have hP0_proj : IsStarProjection sys.P0 := sys.isStarProjection_P0
    have hPloc_proj : IsStarProjection (sys.localGroundProj B) := sys.isStarProjection_P_loc_bhm B
    have hPloc_ne : sys.localGroundProj B ≠ 0 := by
      intro h0
      have h_abs := (sys.localProj_mul_proj0_eq_proj0 B).1
      rw [h0, zero_mul] at h_abs
      exact sys.frustration_free h_abs.symm
    have hz0_ne : complexTrace sys.P0 ≠ 0 := by
      rw [complexTrace_of_isStarProjection hP0_proj]
      exact Complex.ofReal_ne_zero.mpr
        (ne_of_gt (lt_of_lt_of_le zero_lt_one
          (one_le_hilbertTrace_of_isStarProjection_ne_zero hP0_proj sys.frustration_free)))
    have hzB_ne : complexTrace (sys.localGroundProj B) ≠ 0 := by
      rw [complexTrace_of_isStarProjection hPloc_proj]
      exact Complex.ofReal_ne_zero.mpr
        (ne_of_gt (lt_of_lt_of_le zero_lt_one
          (one_le_hilbertTrace_of_isStarProjection_ne_zero hPloc_proj hPloc_ne)))
    refine ⟨?_, ?_⟩
    · have h_entry_scale : ∀ α β : LocalConfig (UniformSite3D L (CodeSlotConfig q_code)) A,
          complexTrace (sys.localGroundProj B) *
            (∑ γ, partialTraceEntry (UniformSite3D L (CodeSlotConfig q_code)) A sys.P0 γ α β) =
          complexTrace sys.P0 *
            (∑ γ, partialTraceEntry (UniformSite3D L (CodeSlotConfig q_code)) A (sys.localGroundProj B) γ α β) := by
        intro α β
        obtain ⟨c, hc_Ploc, hc_P0⟩ :=
          staticCSS_operator_sandwich_eq ω C h_valid h_f2 hC hr1 hrL x0
            (cylinderOp (UniformSite3D L (CodeSlotConfig q_code)) A (localUnitOp A α β))
            ⟨localUnitOp A α β, rfl⟩
        rw [sum_partialTraceEntry_of_sandwich A sys.P0 hP0_proj α β c hc_P0,
            sum_partialTraceEntry_of_sandwich A (sys.localGroundProj B) hPloc_proj α β c hc_Ploc]
        ring
      have h_smul_pt : ∀ ψ_A : LocalHilbertSpace (UniformSite3D L (CodeSlotConfig q_code)) A,
          complexTrace (sys.localGroundProj B) •
            partialTrace (UniformSite3D L (CodeSlotConfig q_code)) A sys.P0 ψ_A =
          complexTrace sys.P0 •
            partialTrace (UniformSite3D L (CodeSlotConfig q_code)) A (sys.localGroundProj B) ψ_A := by
        intro ψ_A
        ext α
        change complexTrace (sys.localGroundProj B) *
            (∑ γ, ∑ β, partialTraceEntry _ A sys.P0 γ α β * ψ_A.ofLp β) =
          complexTrace sys.P0 *
            (∑ γ, ∑ β, partialTraceEntry _ A (sys.localGroundProj B) γ α β * ψ_A.ofLp β)
        rw [Finset.sum_comm, Finset.mul_sum, Finset.sum_comm (s := Finset.univ), Finset.mul_sum]
        refine Finset.sum_congr rfl (fun β _ => ?_)
        rw [← Finset.sum_mul, ← Finset.sum_mul, ← mul_assoc, h_entry_scale α β, mul_assoc]
      ext ψ_A
      simp only [LinearMap.mem_ker, ContinuousLinearMap.coe_coe]
      constructor
      · intro h0
        have h_eq := h_smul_pt ψ_A
        rw [h0, smul_zero] at h_eq
        exact (smul_eq_zero.mp h_eq.symm).resolve_left hz0_ne
      · intro h0
        have h_eq := h_smul_pt ψ_A
        rw [h0, smul_zero] at h_eq
        exact (smul_eq_zero.mp h_eq).resolve_left hzB_ne
    · intro O_A h_supp
      constructor
      · intro h_P0_zero
        have h_supp_sq : IsSupportedOn (UniformSite3D L (CodeSlotConfig q_code)) A (star O_A * O_A) :=
          isSupportedOn_mul A (isSupportedOn_adjoint A h_supp) h_supp
        obtain ⟨c, hc_Ploc, hc_P0⟩ :=
          staticCSS_operator_sandwich_eq ω C h_valid h_f2 hC hr1 hrL x0 (star O_A * O_A) h_supp_sq
        have h_P0_sa : star sys.P0 = sys.P0 := hP0_proj.isSelfAdjoint.star_eq
        have h_Ploc_sa : star (sys.localGroundProj B) = sys.localGroundProj B := hPloc_proj.isSelfAdjoint.star_eq
        have h_P0_sq_zero : sys.P0 * (star O_A * O_A) * sys.P0 = 0 := by
          calc sys.P0 * (star O_A * O_A) * sys.P0
            _ = (star sys.P0 * star O_A) * (O_A * sys.P0) := by
              rw [h_P0_sa]; simp only [mul_assoc]
            _ = star (O_A * sys.P0) * (O_A * sys.P0) := by rw [← star_mul]
            _ = 0 := by rw [h_P0_zero, mul_zero]
        have hc_P0' : c • sys.P0 = 0 := hc_P0.symm.trans h_P0_sq_zero
        have hc_zero : c = 0 := (smul_eq_zero.mp hc_P0').resolve_right sys.frustration_free
        have h_Ploc_sq_zero : star (O_A * sys.localGroundProj B) * (O_A * sys.localGroundProj B) = 0 := by
          calc star (O_A * sys.localGroundProj B) * (O_A * sys.localGroundProj B)
            _ = (star (sys.localGroundProj B) * star O_A) * (O_A * sys.localGroundProj B) := by rw [star_mul]
            _ = sys.localGroundProj B * (star O_A * O_A) * sys.localGroundProj B := by
              rw [h_Ploc_sa]; simp only [mul_assoc]
            _ = c • sys.localGroundProj B := hc_Ploc
            _ = 0 := by rw [hc_zero, clm_zero_smul]
        exact clm_eq_zero_of_star_mul_self_eq_zero h_Ploc_sq_zero
      · intro h_Ploc_zero
        rw [← (sys.localProj_mul_proj0_eq_proj0 B).1, ← mul_assoc, h_Ploc_zero, zero_mul]
  have h_sec : SatisfiesSectorFilteredLinearTQO2 sys 1 L_star C := by
    refine ⟨⟨IsIdempotentElem.one, IsSelfAdjoint.one _⟩,
      fun i => Commute.one_right _, mul_one sys.P0, h_tqo1, ?_⟩
    intro r hr1 hrL x0 _A _B O_A h_supp
    rw [mul_one]
    exact (h_tqo2 r hr1 hrL x0).2 O_A h_supp
  exact ⟨h_tqo1, h_tqo2, h_sec⟩

/-! ## 3. Level-$k$ Inhomogeneous BDL System `bdlInhomogeneousSystem k` & Bare Logicals -/

def bdlInhomogeneousSystem (k : ℕ) :
    IndexedCommutingProjectorHamiltonian 3 (bdlBoxSide k)
      (UniformSite3D (bdlBoxSide k) (CodeSlotConfig qCodeBDL))
      (StaticCSSCheckIdx (bdlBoxSide k) qCodeBDL mMaxBDL) :=
  staticCSSSystem (bdlLocalDescriptor k) (bdlLocalDescriptor_validDescriptorField k)

lemma bdlInhomogeneousSystem_P0_ne_zero_and_ne_one (k : ℕ) :
    (bdlInhomogeneousSystem k).P0 ≠ 0 ∧ (bdlInhomogeneousSystem k).P0 ≠ 1 := by
  refine ⟨(bdlInhomogeneousSystem k).frustration_free, ?_⟩
  intro h_one
  let v0 : Box3D (bdlBoxSide k) := fun _ => ⟨0, bdlBoxSide_pos k⟩
  let s0 : Fin qCodeBDL := ⟨0, q_code_bdl_pos⟩
  have h_fib_empty : bdlQubitFiber k v0 = ∅ := by
    rw [Finset.eq_empty_iff_forall_notMem]
    intro q hq
    have hq_v0 : bdlGridVertexQ k q = v0 := (Finset.mem_filter.mp hq).2
    have hq0 : (bdlGridVertexQ k q 0).val = 0 := congr_arg Fin.val (congr_fun hq_v0 0)
    have hL := bdlCoordBound_add_1000_le_half_L k
    have hb := (hasBounded3DCoords_bdlWeldedBundled k).1 q
    have h_snap := ((snapPointToOpenBox_bounds hL hb 0).2).2
    have h_abs : -bdlCoordBound (k + 1) ≤ (bdlWeldedCode k).posQ q 0 := (abs_le.mp (hb 0)).1
    have h_val_cast : ((snapPointToOpenBox (bdlBoxSide k) ((bdlWeldedBundled k).code.posQ q) 0).val : ℝ) = 0 := by
      exact_mod_cast hq0
    rw [h_val_cast] at h_snap
    change (bdlWeldedCode k).posQ q 0 + (bdlBoxSide k : ℝ) / 2 < 0 + 1 at h_snap
    linarith
  have h_inact : (bdlLocalDescriptor k v0).activeSlot s0 = false := by
    dsimp [bdlLocalDescriptor, bdlLocalDescriptorOfPlacement]
    change decide (0 < (bdlQubitFiber k v0).card) = false
    rw [h_fib_empty, Finset.card_empty]
    decide
  have h_zero := (bdlInhomogeneousSystem k).checkProj_mul_P_loc_eq_zero
    (Sum.inl (v0, s0)) Finset.univ (Finset.subset_univ _)
  have h_P0_zero : (bdlInhomogeneousSystem k).checkProj (Sum.inl (v0, s0)) *
      (bdlInhomogeneousSystem k).P0 = 0 := by
    rw [← ((bdlInhomogeneousSystem k).localProj_mul_proj0_eq_proj0 Finset.univ).1, ← mul_assoc, h_zero, zero_mul]
  rw [h_one, mul_one] at h_P0_zero
  dsimp [bdlInhomogeneousSystem, staticCSSSystem, staticCSSCheckProj] at h_P0_zero
  rw [if_pos h_inact] at h_P0_zero
  let σ_true : ManyBodyConfig (UniformSite3D (bdlBoxSide k) (CodeSlotConfig qCodeBDL)) :=
    fun _ _ => true
  have h_eval : (weylCheckProjZ (singleSlotChain v0 s0)
      (basisVecGlobal _ σ_true)).ofLp σ_true = 1 := by
    change (2 : ℂ)⁻¹ * ((basisVecGlobal _ σ_true).ofLp σ_true -
      pauliPhase (singleSlotChain v0 s0) (codeConfigBits σ_true) *
        (basisVecGlobal _ σ_true).ofLp σ_true) = 1
    have h_ket : (basisVecGlobal (UniformSite3D (bdlBoxSide k) (CodeSlotConfig qCodeBDL)) σ_true).ofLp σ_true = 1 := by
      dsimp [basisVecGlobal]; rw [if_pos rfl]
    have h_phase : pauliPhase (singleSlotChain v0 s0) (codeConfigBits σ_true) = -1 := by
      unfold pauliPhase
      have h_sum : (∑ p : BoxSlot3D (bdlBoxSide k) qCodeBDL,
          singleSlotChain v0 s0 p * codeConfigBits σ_true p) = 1 := by
        rw [Finset.sum_eq_single (v0, s0)]
        · dsimp [singleSlotChain, codeConfigBits, σ_true]; decide
        · intro p _ hne; dsimp [singleSlotChain]; rw [if_neg hne, zero_mul]
        · intro h_abs; exact False.elim (h_abs (Finset.mem_univ _))
      rw [h_sum]
      have h10 : (1 : ZMod 2) ≠ 0 := by decide
      rw [if_neg h10]
    rw [h_ket, h_phase]
    ring
  rw [h_P0_zero] at h_eval
  exact zero_ne_one h_eval

lemma bdlInhomogeneousSystem_satisfiesOperatorTQO (k : ℕ) :
    SatisfiesTQO1 (bdlInhomogeneousSystem k) (bdlLinearTQORadius k) ∧
    SatisfiesLinearTQO2 (bdlInhomogeneousSystem k) (bdlLinearTQORadius k) (collarConstRCABDL : ℝ) ∧
    SatisfiesSectorFilteredLinearTQO2 (bdlInhomogeneousSystem k) 1 (bdlLinearTQORadius k) (collarConstRCABDL : ℝ) := by
  apply staticCSSSystem_satisfiesOperatorTQO (bdlLocalDescriptor k) (collarConstRCABDL : ℝ)
    (bdlLocalDescriptor_validDescriptorField k) (bdlLocalDescriptor_satisfiesBoxF2LinearTQO k)
  exact_mod_cast (by dsimp [collarConstRCABDL, r0BDL, bdlLambda]; omega : 4 * r0BDL + 3 ≤ collarConstRCABDL)

def bdlPushChain (k : ℕ) (c : BDLWeldedQubit k → ZMod 2) :
    BoxSlot3D (bdlBoxSide k) qCodeBDL → ZMod 2 :=
  fun p => ∑ q : BDLWeldedQubit k, if bdlQubitSiteSlot k q = p then c q else 0

@[simp]
lemma bdlPushChain_apply_bdlQubitSiteSlot (k : ℕ) (c : BDLWeldedQubit k → ZMod 2)
    (q : BDLWeldedQubit k) :
    bdlPushChain k c (bdlQubitSiteSlot k q) = c q := by
  dsimp [bdlPushChain]
  rw [Finset.sum_eq_single q]
  · rw [if_pos rfl]
  · intro q' _ hne
    rw [if_neg (fun h => hne (bdlQubitSiteSlot_injective k h))]
  · intro h_abs; exact False.elim (h_abs (Finset.mem_univ q))

lemma bdlPushChain_eq_zero_of_not_mem_image (k : ℕ) (c : BDLWeldedQubit k → ZMod 2)
    (p : BoxSlot3D (bdlBoxSide k) qCodeBDL)
    (hp : p ∉ Finset.univ.image (bdlQubitSiteSlot k)) :
    bdlPushChain k c p = 0 := by
  dsimp [bdlPushChain]
  apply Finset.sum_eq_zero
  intro q _
  rw [if_neg (fun h => hp (Finset.mem_image.mpr ⟨q, Finset.mem_univ q, h⟩))]
