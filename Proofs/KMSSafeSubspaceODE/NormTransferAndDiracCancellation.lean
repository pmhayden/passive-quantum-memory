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

import Proofs.KMSSafeSubspaceODE.LocalProjectorAndSupportAlgebra

open scoped Classical InnerProduct ComplexConjugate BigOperators
open Filter Topology Asymptotics ContinuousLinearMap

noncomputable section

/-!
# TQO Local Sandwich Transfer, Bare Syndrome Projectors, and Unitary Sandwich Cancellation

Proves local-to-global ground-projector sandwich identities under topological quantum order (`exists_local_sandwich_of_tqo`), establishes star-projection and check-absorption properties for `bareSyndromeProjector` (`one_sub_syndromeFactor_mul_bareSyndromeProjector`, `bareSyndromeProjector_mul_syndromeFactor`, `check_mul_bareSyndromeProjector`), and proves unitary sandwich cancellation (`unitary_dirac_sandwich_cancel`).

## References

* Part I, Section 3.1 (`subsec:rca-trinity`), Definition 3.2 (`def:tqo`), Proposition 3.3 (`prop:trinity-equivalence`)
* Part I, Section 7.1 (`subsec:single-cube-telescoping`), Lemma 7.1 (`lem:norm-transfer`)
* Part II, Section 3.2 (`subsec:rca1-pinching`), Proposition 3.4 (`prop:pauli-diag-off`)
* Bravyi–Hastings (2011), Corollary 1
-/

namespace KMSPinchedGibbs

/-! ## 1. Open-Box Collar Inclusions and BH11 Corollary 1 -/

lemma self_le_linearExpansionRadius {C : ℝ} (hC : C ≥ 1) (r : ℕ) :
    r ≤ linearExpansionRadius C r := by
  have hr_nonneg : (0 : ℝ) ≤ (r : ℝ) := Nat.cast_nonneg r
  have h1 : (r : ℝ) ≤ C * (r : ℝ) := by nlinarith
  have h2 : (r : ℝ) ≤ (linearExpansionRadius C r : ℝ) :=
    le_trans h1 (Nat.le_ceil (C * (r : ℝ)))
  exact_mod_cast h2

lemma linearExpansionRadius_le_mul (C : ℝ) (hC : C ≥ 1) {r : ℕ} (hr : 1 ≤ r) :
    (linearExpansionRadius C r : ℝ) ≤ (C + 1) * (r : ℝ) := by
  dsimp [linearExpansionRadius]
  have hCr_nonneg : 0 ≤ C * (r : ℝ) := mul_nonneg (by linarith) (Nat.cast_nonneg r)
  have h_ceil : (Nat.ceil (C * (r : ℝ)) : ℝ) < C * (r : ℝ) + 1 :=
    Nat.ceil_lt_add_one hCr_nonneg
  have hr_ge_one : (1 : ℝ) ≤ (r : ℝ) := Nat.one_le_cast.mpr hr
  linarith

lemma tqo1_scalar_abs_le_norm {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    {P O : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site}
    {c : ℂ} (hP_proj : IsStarProjection P) (hP_ne : P ≠ 0) (hc : P * O * P = c • P) :
    ‖c‖ ≤ ‖O‖ ∧ (IsSelfAdjoint O → c.im = 0) := by
  have h_exists_vec : ∃ ψ : ManyBodyHilbertSpace Site, P ψ ≠ 0 := by
    by_contra h_all; push_neg at h_all; exact hP_ne (ContinuousLinearMap.ext h_all)
  rcases h_exists_vec with ⟨ψ₀, hψ₀⟩
  let ϕ := P ψ₀
  have hϕ_pos : 0 < ‖ϕ‖ := norm_pos_iff.mpr hψ₀
  have hPϕ : P ϕ = ϕ := by
    change (P * P) ψ₀ = P ψ₀; rw [hP_proj.isIdempotentElem.eq]
  have hP_adj : P† = P := ContinuousLinearMap.isSelfAdjoint_iff'.mp hP_proj.isSelfAdjoint
  have h_inner_eq : inner ℂ ϕ (O ϕ) = c * ((‖ϕ‖ ^ 2 : ℝ) : ℂ) := by
    calc inner ℂ ϕ (O ϕ)
      _ = inner ℂ (P ϕ) (O (P ϕ)) := by rw [hPϕ]
      _ = inner ℂ ϕ ((P * O * P) ϕ) := by
        change inner ℂ (P ϕ) (O (P ϕ)) = inner ℂ ϕ (P (O (P ϕ)))
        rw [← ContinuousLinearMap.adjoint_inner_left P, hP_adj]
      _ = inner ℂ ϕ ((c • P) ϕ) := by rw [hc]
      _ = c * ((‖ϕ‖ ^ 2 : ℝ) : ℂ) := by
        rw [ContinuousLinearMap.smul_apply, hPϕ, inner_smul_right, inner_self_eq_norm_sq_to_K]
        norm_cast
  constructor
  · have h_norm_inner : ‖inner ℂ ϕ (O ϕ)‖ ≤ ‖O‖ * ‖ϕ‖ ^ 2 := by
      calc ‖inner ℂ ϕ (O ϕ)‖
        _ ≤ ‖ϕ‖ * ‖O ϕ‖ := norm_inner_le_norm ϕ (O ϕ)
        _ ≤ ‖ϕ‖ * (‖O‖ * ‖ϕ‖) := mul_le_mul_of_nonneg_left (O.le_opNorm ϕ) (norm_nonneg ϕ)
        _ = ‖O‖ * ‖ϕ‖ ^ 2 := by ring
    rw [h_inner_eq, norm_mul, Complex.norm_real, Real.norm_of_nonneg (sq_nonneg ‖ϕ‖)] at h_norm_inner
    exact le_of_mul_le_mul_right h_norm_inner (sq_pos_of_pos hϕ_pos)
  · intro hO_sa
    have hO_adj : O† = O := ContinuousLinearMap.isSelfAdjoint_iff'.mp hO_sa
    have h_inner_real : (inner ℂ ϕ (O ϕ)).im = 0 := by
      have h_symm : inner ℂ (O ϕ) ϕ = inner ℂ ϕ (O ϕ) := by
        rw [← ContinuousLinearMap.adjoint_inner_right O ϕ ϕ, hO_adj]
      exact Complex.conj_eq_iff_im.mp (by rw [inner_conj_symm, h_symm])
    rw [h_inner_eq, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, mul_zero, zero_add] at h_inner_real
    exact (mul_eq_zero.mp h_inner_real).resolve_right (ne_of_gt (sq_pos_of_pos hϕ_pos))

lemma eq_zero_of_mul_eq_zero_of_isSelfAdjoint {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] [CompleteSpace E]
    {P O : E →L[ℂ] E} (hP : IsSelfAdjoint P) (hO : IsSelfAdjoint O) (c : ℝ)
    (h : (O - (c : ℂ) • (1 : E →L[ℂ] E)) * P = 0) :
    P * (O - (c : ℂ) • (1 : E →L[ℂ] E)) = 0 := by
  have h1 : IsSelfAdjoint ((c : ℂ) • (1 : E →L[ℂ] E)) := by
    rw [IsSelfAdjoint, star_smul, star_one, RCLike.star_def, Complex.conj_ofReal]
  have hM : IsSelfAdjoint (O - (c : ℂ) • (1 : E →L[ℂ] E)) := hO.sub h1
  calc P * (O - (c : ℂ) • (1 : E →L[ℂ] E))
    _ = star P * star (O - (c : ℂ) • (1 : E →L[ℂ] E)) := by rw [hP.star_eq, hM.star_eq]
    _ = star ((O - (c : ℂ) • (1 : E →L[ℂ] E)) * P) := (star_mul _ P).symm
    _ = 0 := by rw [h, star_zero]

lemma mul_smul_one_mul {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (P : E →L[ℂ] E) (c : ℂ) : P * (c • (1 : E →L[ℂ] E)) * P = c • (P * P) := by
  ext ψ; simp

lemma exists_local_sandwich_of_tqo {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    (sys : CommutingProjectorHamiltonian D L Site)
    {L_star : ℕ} {C : ℝ}
    (hTQO1 : sys.SatisfiesTQO1 L_star) (hTQO2 : sys.SatisfiesLinearTQO2 L_star C)
    {r : ℕ} (hr1 : 1 ≤ r) (hrL : r ≤ L_star) (x0 : BoxD D L)
    (O : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site)
    (hO_sa : IsSelfAdjoint O) (hO_supp : IsSupportedOn Site (boxCube x0 r) O)
    (hO_comm : Commute O sys.P) :
    ∃ c : ℝ,
      |c| ≤ ‖O‖ ∧
      ‖O - (c : ℂ) • (1 : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site)‖ ≤ 2 * ‖O‖ ∧
      O = (c : ℂ) • (1 : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site) +
        (1 - sys.localGroundProj (enclosingBoxCube x0 r (linearExpansionRadius C r))) *
          (O - (c : ℂ) • (1 : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site)) *
          (1 - sys.localGroundProj (enclosingBoxCube x0 r (linearExpansionRadius C r))) := by
  rcases hTQO1 r hr1 hrL x0 O hO_supp with ⟨c_C, hc_C⟩
  have hP_idem : sys.P * sys.P = sys.P := sys.isStarProjection_P.isIdempotentElem.eq
  have hOP : O * sys.P = c_C • sys.P := by
    calc O * sys.P = O * (sys.P * sys.P) := by rw [hP_idem]
      _ = (sys.P * O) * sys.P := by rw [← mul_assoc, hO_comm.eq]
      _ = c_C • sys.P := hc_C
  rcases tqo1_scalar_abs_le_norm sys.isStarProjection_P sys.frustration_free hc_C with
    ⟨hc_C_norm, hc_C_im⟩
  let c : ℝ := c_C.re
  have hc_eq : (c : ℂ) = c_C := Complex.ext rfl (hc_C_im hO_sa).symm
  have hc_norm : |c| ≤ ‖O‖ := by
    have h1 : ‖(c : ℂ)‖ = ‖c_C‖ := by rw [hc_eq]
    rw [Complex.norm_real, Real.norm_eq_abs] at h1; linarith
  let M := O - (c : ℂ) • (1 : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site)
  have hM_norm : ‖M‖ ≤ 2 * ‖O‖ := by
    calc ‖M‖ ≤ ‖O‖ + ‖(c : ℂ) • (1 : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site)‖ :=
          norm_sub_le O _
      _ = ‖O‖ + |c| * ‖(1 : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site)‖ := by
          rw [norm_smul, Complex.norm_real, Real.norm_eq_abs]
      _ ≤ ‖O‖ + |c| * 1 := by gcongr; exact ContinuousLinearMap.norm_id_le
      _ ≤ ‖O‖ + ‖O‖ * 1 := by gcongr
      _ = 2 * ‖O‖ := by ring
  have hMP : M * sys.P = 0 := by
    ext ψ : 1; change (O - (c : ℂ) • 1) (sys.P ψ) = 0
    rw [ContinuousLinearMap.sub_apply, ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.one_apply, ← ContinuousLinearMap.mul_apply, hOP,
      ContinuousLinearMap.smul_apply, hc_eq, sub_self]
  let B := enclosingBoxCube x0 r (linearExpansionRadius C r)
  have hMP_loc : M * sys.localGroundProj B = 0 :=
    ((hTQO2 r hr1 hrL x0).2 M (isSupportedOn_sub_smul_one hO_supp (c : ℂ))).mp hMP
  have hP_locM : sys.localGroundProj B * M = 0 :=
    eq_zero_of_mul_eq_zero_of_isSelfAdjoint (sys.isStarProjection_P_loc B).isSelfAdjoint hO_sa c hMP_loc
  have h_sandwich : (1 - sys.localGroundProj B) * M * (1 - sys.localGroundProj B) = M := by
    rw [sub_mul, one_mul, hP_locM, sub_zero, mul_sub, mul_one, hMP_loc, sub_zero]
  refine ⟨c, hc_norm, hM_norm, ?_⟩
  rw [h_sandwich]; dsimp [M]; abel

lemma _root_.CommutingProjectorHamiltonian.commute_collar_sandwich_P {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    (sys : CommutingProjectorHamiltonian D L Site) {A0 B0 : Finset (BoxD D L)}
    {M : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site}
    (hCollar : IsOneCollarOf A0 B0) (hM_supp : IsSupportedOn Site A0 M) :
    Commute (sys.localGroundProj B0 * M * sys.localGroundProj B0) sys.P := by
  dsimp [CommutingProjectorHamiltonian.P, globalGroundProjector, localGroundProjector]
  apply Commute.list_prod_right
  intro p hp
  rcases List.mem_map.mp hp with ⟨K, hK_mem, rfl⟩
  have hK_cube : K ∈ boxCubes D L 2 := (Finset.mem_filter.mp (Finset.mem_toList.mp hK_mem)).1
  apply commute_one_sub_right
  by_cases hDisj : Disjoint K A0
  · have h_comm_M : Commute M (sys.Q K) :=
      commute_of_isSupportedOn_disjoint hDisj.symm hM_supp (sys.is_supported K hK_cube)
    have h_comm_PB0 : Commute (sys.localGroundProj B0) (sys.Q K) := sys.commute_P_loc_Q B0 K hK_cube
    exact (h_comm_PB0.mul_left h_comm_M).mul_left h_comm_PB0
  · have hKB0 : K ⊆ B0 := hCollar.2 K hK_cube hDisj
    rw [commute_iff_eq]
    calc (sys.localGroundProj B0 * M * sys.localGroundProj B0) * sys.Q K
      _ = sys.localGroundProj B0 * M * (sys.localGroundProj B0 * sys.Q K) := by rw [mul_assoc]
      _ = 0 := by rw [sys.localGroundProj_mul_check_eq_zero K B0 hK_cube hKB0, mul_zero]
      _ = (sys.Q K * sys.localGroundProj B0) * M * sys.localGroundProj B0 := by
        rw [sys.check_mul_localGroundProj_eq_zero K B0 hK_cube hKB0, zero_mul, zero_mul]
      _ = sys.Q K * (sys.localGroundProj B0 * M * sys.localGroundProj B0) := by simp only [mul_assoc]

lemma isSelfAdjoint_collar_mul_adjoint {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    (sys : CommutingProjectorHamiltonian D L Site) (B0 : Finset (BoxD D L))
    (S : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site) :
    IsSelfAdjoint (sys.localGroundProj B0 * (S * S†) * sys.localGroundProj B0) := by
  rw [IsSelfAdjoint]
  have hB0_sa : star (sys.localGroundProj B0) = sys.localGroundProj B0 :=
    (sys.isStarProjection_P_loc B0).isSelfAdjoint.star_eq
  change star (sys.localGroundProj B0 * (S * star S) * sys.localGroundProj B0) =
    sys.localGroundProj B0 * (S * star S) * sys.localGroundProj B0
  rw [star_mul, star_mul, star_mul, star_star, hB0_sa]; simp only [mul_assoc]

/-! ## 2. Part I: Dressed Syndrome Projectors -/

lemma isStarProjection_unitary_conj {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] [CompleteSpace E]
    (U : unitary (E →L[ℂ] E)) {P : E →L[ℂ] E} (hP : IsStarProjection P) :
    IsStarProjection (U.1 * P * U.1†) := by
  have hU_star_self : U.1† * U.1 = 1 := Unitary.coe_star_mul_self U
  have hP_idem : P * P = P := hP.isIdempotentElem.eq
  have hP_sa : star P = P := hP.isSelfAdjoint.star_eq
  refine ⟨?_, ?_⟩
  · rw [IsIdempotentElem]
    calc (U.1 * P * U.1†) * (U.1 * P * U.1†)
      _ = U.1 * P * (U.1† * U.1) * P * U.1† := by simp only [mul_assoc]
      _ = U.1 * (P * P) * U.1† := by rw [hU_star_self, mul_one]; simp only [mul_assoc]
      _ = U.1 * P * U.1† := by rw [hP_idem]
  · rw [IsSelfAdjoint]
    change star (U.1 * P * star U.1) = U.1 * P * star U.1
    rw [star_mul, star_mul, star_star, hP_sa, mul_assoc]

lemma commute_unitary_conj {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] [CompleteSpace E]
    (U : unitary (E →L[ℂ] E)) {A B : E →L[ℂ] E} (hAB : Commute A B) :
    Commute (U.1 * A * U.1†) (U.1 * B * U.1†) := by
  have hU_star_self : U.1† * U.1 = 1 := Unitary.coe_star_mul_self U
  rw [commute_iff_eq]
  calc (U.1 * A * U.1†) * (U.1 * B * U.1†)
    _ = U.1 * A * (U.1† * U.1) * B * U.1† := by simp only [mul_assoc]
    _ = U.1 * (A * B) * U.1† := by rw [hU_star_self, mul_one]; simp only [mul_assoc]
    _ = U.1 * (B * A) * U.1† := by rw [hAB.eq]
    _ = U.1 * B * (U.1† * U.1) * A * U.1† := by rw [hU_star_self, mul_one]; simp only [mul_assoc]
    _ = (U.1 * B * U.1†) * (U.1 * A * U.1†) := by simp only [mul_assoc]

lemma isStarProjection_syndromeFactor {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    (sys : CommutingProjectorHamiltonian D L Site)
    {K : Finset (BoxD D L)} (hK : K ∈ boxCubes D L 2) (b : Bool) :
    IsStarProjection (if b then sys.Q K else 1 - sys.Q K) := by
  cases b
  · simp only [Bool.false_eq_true, ↓reduceIte]; exact (sys.is_projector K hK).one_sub
  · simp only [↓reduceIte]; exact sys.is_projector K hK

lemma commute_syndromeFactor {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    (sys : CommutingProjectorHamiltonian D L Site)
    {K₁ K₂ : Finset (BoxD D L)} (hK₁ : K₁ ∈ boxCubes D L 2) (hK₂ : K₂ ∈ boxCubes D L 2)
    (b₁ b₂ : Bool) :
    Commute (if b₁ then sys.Q K₁ else 1 - sys.Q K₁) (if b₂ then sys.Q K₂ else 1 - sys.Q K₂) := by
  have hcomm := sys.pairwise_commute K₁ hK₁ K₂ hK₂
  cases b₁ <;> cases b₂ <;> simp only [Bool.false_eq_true, ↓reduceIte]
  · exact commute_one_sub_right (commute_one_sub_left hcomm)
  · exact commute_one_sub_left hcomm
  · exact commute_one_sub_right hcomm
  · exact hcomm

lemma commute_syndromeFactor_bareSyndromeProjector {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    (sys : CommutingProjectorHamiltonian D L Site) (σ : SyndromeConfig D L)
    {K : Finset (BoxD D L)} (hK : K ∈ boxCubes D L 2) (b : Bool) :
    Commute (if b then sys.Q K else 1 - sys.Q K) (bareSyndromeProjector sys σ) := by
  dsimp [bareSyndromeProjector]
  apply Commute.list_prod_right
  intro q hq
  rcases List.mem_map.mp hq with ⟨K', hK'_mem, rfl⟩
  exact commute_syndromeFactor sys hK (Finset.mem_toList.mp hK'_mem) b (σ K')

lemma one_sub_syndromeFactor_mul_bareSyndromeProjector {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    (sys : CommutingProjectorHamiltonian D L Site) (σ : SyndromeConfig D L)
    {K : Finset (BoxD D L)} (hK : K ∈ boxCubes D L 2) :
    (1 - (if σ K then sys.Q K else 1 - sys.Q K)) * bareSyndromeProjector sys σ = 0 := by
  dsimp [bareSyndromeProjector]
  apply one_sub_mul_list_prod_eq_zero _ (if σ K then sys.Q K else 1 - sys.Q K)
  · exact List.mem_map_of_mem (Finset.mem_toList.mpr hK)
  · exact (isStarProjection_syndromeFactor sys hK (σ K)).isIdempotentElem
  · intro q hq
    rcases List.mem_map.mp hq with ⟨K', hK'_mem, rfl⟩
    exact commute_syndromeFactor sys hK (Finset.mem_toList.mp hK'_mem) (σ K) (σ K')

lemma bareSyndromeProjector_mul_syndromeFactor {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    (sys : CommutingProjectorHamiltonian D L Site) (σ : SyndromeConfig D L)
    {K : Finset (BoxD D L)} (hK : K ∈ boxCubes D L 2) :
    bareSyndromeProjector sys σ * (if σ K then sys.Q K else 1 - sys.Q K) =
      bareSyndromeProjector sys σ := by
  rw [← (commute_syndromeFactor_bareSyndromeProjector sys σ hK (σ K)).eq]
  have h_zero := one_sub_syndromeFactor_mul_bareSyndromeProjector sys σ hK
  rw [sub_mul, one_mul, sub_eq_zero] at h_zero
  exact h_zero.symm

lemma bareSyndromeProjector_mul_eq_zero_of_ne_at_cube {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    (sys : CommutingProjectorHamiltonian D L Site)
    {σ₁ σ₂ : SyndromeConfig D L} {K : Finset (BoxD D L)}
    (hK : K ∈ boxCubes D L 2) (h_ne : σ₁ K ≠ σ₂ K) :
    bareSyndromeProjector sys σ₁ * bareSyndromeProjector sys σ₂ = 0 := by
  have h_factor_eq :
      (if σ₁ K then sys.Q K else 1 - sys.Q K) =
        1 - (if σ₂ K then sys.Q K else 1 - sys.Q K) := by
    cases h1 : σ₁ K <;> cases h2 : σ₂ K
    · exfalso; exact h_ne (h1.trans h2.symm)
    · simp
    · simp [sub_sub_cancel]
    · exfalso; exact h_ne (h1.trans h2.symm)
  calc bareSyndromeProjector sys σ₁ * bareSyndromeProjector sys σ₂
    _ = (bareSyndromeProjector sys σ₁ * (if σ₁ K then sys.Q K else 1 - sys.Q K)) *
          bareSyndromeProjector sys σ₂ := by
      rw [bareSyndromeProjector_mul_syndromeFactor sys σ₁ hK]
    _ = bareSyndromeProjector sys σ₁ *
          ((1 - (if σ₂ K then sys.Q K else 1 - sys.Q K)) * bareSyndromeProjector sys σ₂) := by
      rw [mul_assoc, h_factor_eq]
    _ = 0 := by
      rw [one_sub_syndromeFactor_mul_bareSyndromeProjector sys σ₂ hK, mul_zero]

lemma check_mul_bareSyndromeProjector {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    (sys : CommutingProjectorHamiltonian D L Site) (σ : SyndromeConfig D L)
    {K : Finset (BoxD D L)} (hK : K ∈ boxCubes D L 2) :
    sys.Q K * bareSyndromeProjector sys σ =
      if σ K = true then bareSyndromeProjector sys σ else 0 := by
  have h_zero := one_sub_syndromeFactor_mul_bareSyndromeProjector sys σ hK
  cases hσK : σ K
  · simp only [hσK, Bool.false_eq_true, ↓reduceIte, sub_sub_cancel] at h_zero ⊢
    exact h_zero
  · simp only [hσK, ↓reduceIte] at h_zero ⊢
    rw [sub_mul, one_mul, sub_eq_zero] at h_zero
    exact h_zero.symm

/-! ## 3. Part II: Dirac String Cancellation Outside the Syndrome Collar -/

lemma linearExpansionRadius_add_one_le {C : ℝ} (hC : 1 ≤ C) (r : ℕ) :
    linearExpansionRadius C r + 1 ≤ linearExpansionRadius C (r + 1) := by
  dsimp [linearExpansionRadius]
  have h_pos : 1 ≤ Nat.ceil (C * ((r + 1 : ℕ) : ℝ)) :=
    le_trans (by omega : 1 ≤ r + 1) (self_le_linearExpansionRadius hC (r + 1))
  have h_ceil_r : Nat.ceil (C * (r : ℝ)) ≤ Nat.ceil (C * ((r + 1 : ℕ) : ℝ)) - 1 := by
    rw [Nat.ceil_le, Nat.cast_sub h_pos, Nat.cast_one]
    have h_ceil : C * ((r + 1 : ℕ) : ℝ) ≤ (Nat.ceil (C * ((r + 1 : ℕ) : ℝ)) : ℝ) :=
      Nat.le_ceil _
    have h_cast : C * ((r + 1 : ℕ) : ℝ) = C * (r : ℝ) + C := by push_cast; ring
    linarith
  omega

lemma singleCubeSupportC_pred_subset {D L : ℕ} {C : ℝ} (hC : 1 ≤ C) (u : BoxD D L)
    {k : ℕ} (hk : 2 ≤ k) :
    singleCubeSupportC C u (k - 1) ⊆ singleCubeSupportC C u k := by
  intro x hx
  dsimp [singleCubeSupportC, bhmElementaryCubeSide, enclosingBoxCube, boxCube] at hx ⊢
  rw [Finset.mem_filter] at hx ⊢
  refine ⟨Finset.mem_univ x, fun i => ?_⟩
  have hxi := hx.2 i
  have hR₁_ge : k - 1 + 2 ≤ linearExpansionRadius C (k - 1 + 2) :=
    self_le_linearExpansionRadius hC (k - 1 + 2)
  have hR_step : linearExpansionRadius C (k - 1 + 2) + 1 ≤ linearExpansionRadius C (k + 2) := by
    have hk_eq : k + 2 = (k - 1 + 2) + 1 := by omega
    rw [hk_eq]
    exact linearExpansionRadius_add_one_le hC (k - 1 + 2)
  omega

lemma unitary_dirac_sandwich_cancel {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] [CompleteSpace E]
    (P_σ P_ext D_uk : E →L[ℂ] E)
    (E_K S_uk E_out : unitary (E →L[ℂ] E)) (s_uk : ℝ)
    (hP_ext_sa : IsSelfAdjoint P_ext)
    (hE_split : E_K.1 = S_uk.1 * E_out.1)
    (hs_sq : s_uk ^ 2 = 1)
    (hS_left : S_uk.1 * P_ext = (s_uk : ℂ) • P_ext)
    (hE_out_conj : E_out.1† * P_ext * E_out.1 = P_σ)
    (h_comm_E : D_uk * E_out.1 = E_out.1 * D_uk) :
    E_K.1† * P_ext * D_uk * P_ext * E_K.1 = P_σ * D_uk * P_σ := by
  have hE_adj : E_K.1† = E_out.1† * S_uk.1† := by
    change star E_K.1 = star E_out.1 * star S_uk.1
    rw [hE_split, star_mul]
  have hs_complex_sq : (s_uk : ℂ) * (s_uk : ℂ) = 1 := by
    have h1 : ((s_uk ^ 2 : ℝ) : ℂ) = (1 : ℂ) := by rw [hs_sq, Complex.ofReal_one]
    simpa [sq] using h1
  have hS_unitary : S_uk.1† * S_uk.1 = 1 := Unitary.coe_star_mul_self S_uk
  have hE_out_unitary : E_out.1 * E_out.1† = 1 := Unitary.coe_mul_star_self E_out
  have hS_adj_left : S_uk.1† * P_ext = (s_uk : ℂ) • P_ext := by
    calc S_uk.1† * P_ext
      _ = ((s_uk : ℂ) * (s_uk : ℂ)) • (S_uk.1† * P_ext) := by rw [hs_complex_sq, one_smul]
      _ = (s_uk : ℂ) • (S_uk.1† * ((s_uk : ℂ) • P_ext)) := by rw [clm_mul_smul, ← smul_smul]
      _ = (s_uk : ℂ) • (S_uk.1† * (S_uk.1 * P_ext)) := by rw [← hS_left]
      _ = (s_uk : ℂ) • ((S_uk.1† * S_uk.1) * P_ext) := by rw [mul_assoc]
      _ = (s_uk : ℂ) • P_ext := by rw [hS_unitary, one_mul]
  have h_Pext_S : P_ext * S_uk.1 = (s_uk : ℂ) • P_ext := by
    have hP_sa : star P_ext = P_ext := hP_ext_sa.star_eq
    calc P_ext * S_uk.1
      _ = star (S_uk.1† * P_ext) := by
        change P_ext * S_uk.1 = star (star S_uk.1 * P_ext)
        rw [star_mul, star_star, hP_sa]
      _ = star ((s_uk : ℂ) • P_ext) := by rw [hS_adj_left]
      _ = (s_uk : ℂ) • P_ext := by rw [star_smul, hP_sa, RCLike.star_def, Complex.conj_ofReal]
  have h_left_factor : E_K.1† * P_ext = (s_uk : ℂ) • (E_out.1† * P_ext) := by
    rw [hE_adj, mul_assoc, hS_adj_left, clm_mul_smul]
  have h_right_factor : P_ext * E_K.1 = (s_uk : ℂ) • (P_ext * E_out.1) := by
    rw [hE_split, ← mul_assoc, h_Pext_S, clm_smul_mul]
  have h_PE : P_ext * E_out.1 = E_out.1 * P_σ := by
    calc P_ext * E_out.1
      _ = (E_out.1 * E_out.1†) * P_ext * E_out.1 := by
        rw [hE_out_unitary, one_mul]
      _ = E_out.1 * (E_out.1† * P_ext * E_out.1) := by simp only [mul_assoc]
      _ = E_out.1 * P_σ := by rw [hE_out_conj]
  calc E_K.1† * P_ext * D_uk * P_ext * E_K.1
    _ = (E_K.1† * P_ext) * D_uk * (P_ext * E_K.1) := by simp only [mul_assoc]
    _ = ((s_uk : ℂ) • (E_out.1† * P_ext)) * D_uk * ((s_uk : ℂ) • (P_ext * E_out.1)) := by
      rw [h_left_factor, h_right_factor]
    _ = ((s_uk : ℂ) * (s_uk : ℂ)) • ((E_out.1† * P_ext) * D_uk * (P_ext * E_out.1)) := by
      rw [clm_smul_mul, clm_smul_mul, clm_mul_smul, smul_smul]
    _ = (E_out.1† * P_ext) * D_uk * (P_ext * E_out.1) := by rw [hs_complex_sq, one_smul]
    _ = (E_out.1† * P_ext) * (D_uk * (E_out.1 * P_σ)) := by rw [h_PE, mul_assoc]
    _ = (E_out.1† * P_ext) * (E_out.1 * D_uk * P_σ) := by rw [← mul_assoc D_uk, h_comm_E]
    _ = (E_out.1† * P_ext * E_out.1) * D_uk * P_σ := by simp only [mul_assoc]
    _ = P_σ * D_uk * P_σ := by rw [hE_out_conj]

end KMSPinchedGibbs

end
