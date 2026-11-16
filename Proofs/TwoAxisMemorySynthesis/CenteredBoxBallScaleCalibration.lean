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

import Proofs.TwoAxisMemorySynthesis.BootstrappedQACMemoryReduction

/-!
# Centered Box-Ball Scale Cutoff Calibration and Superpolynomial Splitting Envelope

Calibrates the multiscale telescoping cutoff radius `bdlScaleCutoffK` inside the macroscopic safe-subspace protection radius and constructs the explicit superpolynomially decaying ground-band splitting envelope `bdlExactSplittingEnvelope`.

## References

* Part I, Section 7.1 (`subsec:single-cube-telescoping`), Proposition 7.2 (`prop:single-cube-telescoping`)
* Part I, Section 7.2 (`subsec:gap-bootstrap`), Theorem 7.3 (`thm:gap-bootstrap`)
* Part I, Section 7.3 (`subsec:zero-temp-dressed-memory`), Theorem 7.4 (`thm:zero-temp-dressed-memory`)
-/

open scoped Classical InnerProduct ComplexConjugate BigOperators
open Filter Topology Asymptotics ContinuousLinearMap KMSPinchedGibbs PerturbedThermalBarrier
open WeldedHierarchy WeldedHierarchy.BDLDecoder InhomogeneousMemoryChallenge

noncomputable section

set_option maxRecDepth 200000
set_option maxHeartbeats 800000

private lemma boxBall_subset_shifted_boxCube {D L : ℕ} (v : BoxD D L) (r : ℕ) :
    boxBall v r ⊆
      boxCube (fun i => ⟨(v i).val - r, Nat.sub_lt_of_lt (v i).isLt⟩) (2 * r + 1) := by
  intro y hy
  simp only [boxBall, boxCube, Finset.mem_filter, Finset.mem_univ, true_and] at hy ⊢
  intro i
  have hi : coordDist (v i) (y i) ≤ boxDist v y :=
    Finset.le_sup (f := fun j => coordDist (v j) (y j)) (Finset.mem_univ i)
  have hi_le : coordDist (v i) (y i) ≤ r := le_trans hi hy
  dsimp [coordDist] at hi_le
  omega

/-- Any region contained in `boxBall v r` is contained in a cube in `boxCubes D L (2 * r + 1)`. -/
theorem exists_mem_boxCubes_of_subset_boxBall {D L r : ℕ}
    {S : Finset (BoxD D L)} {v : BoxD D L} (hS : S ⊆ boxBall v r) :
    ∃ A ∈ boxCubes D L (2 * r + 1), S ⊆ A :=
  ⟨boxCube (fun i => ⟨(v i).val - r, Nat.sub_lt_of_lt (v i).isLt⟩) (2 * r + 1),
    Finset.mem_image.mpr ⟨_, Finset.mem_univ _, rfl⟩,
    hS.trans (boxBall_subset_shifted_boxCube v r)⟩

/-- Unconditional check-support cube coverage at scale `2 * r_0 + 1` for any
    `Inhomogeneous3DMemoryRealization`. -/
theorem check_cov_of_inhomogeneous3DMemoryRealization
    {L q_code r_0 m_max : ℕ} [NeZero L]
    {c_star C β_c c_F η c_mem : ℝ}
    (mem : Inhomogeneous3DMemoryRealization L q_code r_0 m_max c_star C β_c c_F η c_mem) :
    ∀ idx : StaticCSSCheckIdx L q_code m_max,
      ∃ A ∈ boxCubes 3 L (2 * r_0 + 1), mem.sys.support idx ⊆ A := by
  intro idx
  rw [(mem.h_sys_checks idx).2.1]
  rcases idx with ⟨v, _⟩ | (⟨v, _⟩ | ⟨v, _⟩)
  · refine exists_mem_boxCubes_of_subset_boxBall (v := v) ?_
    dsimp [staticCSSCheckSupport]
    rw [Finset.singleton_subset_iff]
    simp [boxBall, boxDist, coordDist_self]
  · exact exists_mem_boxCubes_of_subset_boxBall Finset.Subset.rfl
  · exact exists_mem_boxCubes_of_subset_boxBall Finset.Subset.rfl

/-! ## 1. Centered `boxBall` Conditional Expectation Safe-Subspace Immunity & Distance Lower Bound -/

/-- Every point `y ∈ Finset.univ \ boxBall v r_LR` has `r_LR + 1 ≤ boxDist v y`, so whenever
    `Finset.univ \ boxBall v r_LR` is nonempty, `r_LR + 1 ≤ regionDist {v} (Finset.univ \ boxBall v r_LR)`. -/
theorem regionDist_singleton_compl_boxBall_ge {D L : ℕ}
    (v : BoxD D L) (r_LR : ℕ)
    (h_ne : (Finset.univ \ boxBall v r_LR).Nonempty) :
    r_LR + 1 ≤ regionDist ({v} : Finset (BoxD D L)) (Finset.univ \ boxBall v r_LR) := by
  have hv_ne : ({v} : Finset (BoxD D L)).Nonempty := Finset.singleton_nonempty v
  rw [regionDist, dif_pos ⟨hv_ne, h_ne⟩]
  apply Finset.le_inf'
  intro p hp
  rcases Finset.mem_product.mp hp with ⟨hx, hy⟩
  rw [Finset.mem_singleton] at hx
  have hy_not : p.2 ∉ boxBall v r_LR := (Finset.mem_sdiff.mp hy).2
  simp only [boxBall, Finset.mem_filter, Finset.mem_univ, true_and, not_le] at hy_not
  rw [hx]
  exact hy_not

/-- Any operator `Y` supported on `boxBall v r_LR` with `2 * r_LR + 1 ≤ R_fw`
    has zero bare pinched commutator with `O_dec` on `Pi_safe`. -/
theorem pi_safe_commutator_eq_zero_of_isSupportedOn_boxBall {D L R_fw : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    (Pi_safe O_dec : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site)
    (h_fw : ∀ (W : QuasiLocalPerturbation D L Site),
      ∀ r ∈ Finset.Icc 1 R_fw, ∀ A ∈ boxCubes D L r,
        Pi_safe * (W.term r A * O_dec - O_dec * W.term r A) * Pi_safe = 0)
    (v : BoxD D L) {r_LR : ℕ} (hr_LR : 2 * r_LR + 1 ≤ R_fw)
    {Y : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site}
    (hY_supp : IsSupportedOn Site (boxBall v r_LR) Y) :
    Pi_safe * (Y * O_dec - O_dec * Y) * Pi_safe = 0 := by
  rcases exists_mem_boxCubes_of_subset_boxBall (v := v) (r := r_LR)
      (Finset.Subset.refl (boxBall v r_LR)) with ⟨A₀, hA₀, h_sub⟩
  have hr₀ : 2 * r_LR + 1 ∈ Finset.Icc 1 R_fw :=
    Finset.mem_Icc.mpr ⟨by omega, hr_LR⟩
  exact pi_safe_commutator_eq_zero_of_isSupportedOn_cube Pi_safe O_dec h_fw hr₀ hA₀
    (_root_.isSupportedOn_mono h_sub hY_supp)

/-- Centered `boxBall` conditional expectation `condExp Site (boxBall v r_LR) X` has zero bare
    pinched commutator with `O_dec` on `Pi_safe` whenever `2 * r_LR + 1 ≤ R_fw`. -/
theorem pi_safe_commutator_condExp_boxBall_eq_zero {D L R_fw : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    (Pi_safe O_dec : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site)
    (h_fw : ∀ (W : QuasiLocalPerturbation D L Site),
      ∀ r ∈ Finset.Icc 1 R_fw, ∀ A ∈ boxCubes D L r,
        Pi_safe * (W.term r A * O_dec - O_dec * W.term r A) * Pi_safe = 0)
    (v : BoxD D L) {r_LR : ℕ} (hr_LR : 2 * r_LR + 1 ≤ R_fw)
    (X : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site) :
    Pi_safe * (condExp Site (boxBall v r_LR) X * O_dec -
      O_dec * condExp Site (boxBall v r_LR) X) * Pi_safe = 0 :=
  pi_safe_commutator_eq_zero_of_isSupportedOn_boxBall Pi_safe O_dec h_fw v hr_LR
    (isSupportedOn_condExp Site (boxBall v r_LR) X)

/-- 1-site dressed pinched commutator pair bound from centered `boxBall v r_LR` conditional
    expectation tail bounds (`2 * r_LR + 1 ≤ R_fw`). -/
theorem one_site_dressed_pinched_commutator_pair_sq_le_of_condExp_boxBall_tail {D L R_fw : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    (U_dress : unitary (ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site))
    (Pi_safe O_dec_Z O_dec_X : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site)
    (hPi : IsStarProjection Pi_safe)
    (hOZ_norm : ‖O_dec_Z‖ ≤ 1) (hOX_norm : ‖O_dec_X‖ ≤ 1)
    (h_fw : ∀ (W : QuasiLocalPerturbation D L Site),
      ∀ r ∈ Finset.Icc 1 R_fw, ∀ A ∈ boxCubes D L r,
        Pi_safe * (W.term r A * O_dec_Z - O_dec_Z * W.term r A) * Pi_safe = 0 ∧
        Pi_safe * (W.term r A * O_dec_X - O_dec_X * W.term r A) * Pi_safe = 0)
    {r_LR : ℕ} (hr_LR : 2 * r_LR + 1 ≤ R_fw)
    {ε_LR δ_split : ℝ} (hε_LR_nn : 0 ≤ ε_LR) (h_LR_split : 4 * ε_LR ^ 2 ≤ δ_split)
    (h_1site_tail : ∀ (v : BoxD D L)
      (A_v : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site),
      IsSupportedOn Site {v} A_v →
      ‖U_dress.1† * A_v * U_dress.1 -
        condExp Site (boxBall v r_LR) (U_dress.1† * A_v * U_dress.1)‖ ≤ ε_LR * ‖A_v‖) :
    ∀ (v : BoxD D L)
      (A_v : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site),
      IsSupportedOn Site {v} A_v →
      ‖(U_dress.1 * Pi_safe * (U_dress.1†)) *
          (A_v * (U_dress.1 * O_dec_Z * (U_dress.1†)) -
            (U_dress.1 * O_dec_Z * (U_dress.1†)) * A_v) *
          (U_dress.1 * Pi_safe * (U_dress.1†))‖ ^ 2 ≤ ‖A_v‖ ^ 2 * δ_split ∧
      ‖(U_dress.1 * Pi_safe * (U_dress.1†)) *
          (A_v * (U_dress.1 * O_dec_X * (U_dress.1†)) -
            (U_dress.1 * O_dec_X * (U_dress.1†)) * A_v) *
          (U_dress.1 * Pi_safe * (U_dress.1†))‖ ^ 2 ≤ ‖A_v‖ ^ 2 * δ_split := by
  intro v A_v hA_v
  refine ⟨sq_norm_dressed_pinched_commutator_le_of_tail_bhm U_dress Pi_safe O_dec_Z A_v
      (condExp Site (boxBall v r_LR) (U_dress.1† * A_v * U_dress.1))
      hPi hOZ_norm hε_LR_nn
      (pi_safe_commutator_condExp_boxBall_eq_zero Pi_safe O_dec_Z
        (fun W r hr A hA => (h_fw W r hr A hA).1) v hr_LR _)
      (h_1site_tail v A_v hA_v) h_LR_split,
    sq_norm_dressed_pinched_commutator_le_of_tail_bhm U_dress Pi_safe O_dec_X A_v
      (condExp Site (boxBall v r_LR) (U_dress.1† * A_v * U_dress.1))
      hPi hOX_norm hε_LR_nn
      (pi_safe_commutator_condExp_boxBall_eq_zero Pi_safe O_dec_X
        (fun W r hr A hA => (h_fw W r hr A hA).2) v hr_LR _)
      (h_1site_tail v A_v hA_v) h_LR_split⟩

/-! ## 2. Explicit Scale Calibration (`bdlScaleCutoffK k := bdlLambda ^ (k - 4)`) -/

/-- At hierarchy level `k`, the telescoping & Lieb–Robinson radius cutoff is $\Lambda^{k-4}$. -/
def bdlScaleCutoffK (k : ℕ) : ℕ := bdlLambda ^ (k - 4)

lemma one_lt_bdlLambda : 1 < bdlLambda := by decide

lemma one_le_bdlScaleCutoffK (k : ℕ) : 1 ≤ bdlScaleCutoffK k :=
  Nat.one_le_pow (k - 4) bdlLambda bdlLambda_pos

lemma two_mul_bdlScaleCutoffK_add_one_le_bdlLambda_pow {k : ℕ} (hk : 4 ≤ k) :
    2 * bdlScaleCutoffK k + 1 ≤ bdlLambda ^ k := by
  dsimp [bdlScaleCutoffK]
  have h1 : 1 ≤ bdlLambda ^ (k - 4) := Nat.one_le_pow (k - 4) bdlLambda bdlLambda_pos
  have h3 : 3 ≤ bdlLambda := by decide
  have h_pow : bdlLambda ^ (k - 4) * bdlLambda ≤ bdlLambda ^ k := by
    rw [← pow_succ]
    exact Nat.pow_le_pow_right bdlLambda_pos (by omega)
  calc 2 * bdlLambda ^ (k - 4) + 1
    _ ≤ 2 * bdlLambda ^ (k - 4) + bdlLambda ^ (k - 4) := by omega
    _ = bdlLambda ^ (k - 4) * 3 := by ring
    _ ≤ bdlLambda ^ (k - 4) * bdlLambda := Nat.mul_le_mul_left _ h3
    _ ≤ bdlLambda ^ k := h_pow

lemma bdlScaleCutoffK_mem_Icc_safe_radius {k : ℕ} (hk : 4 ≤ k) :
    bdlScaleCutoffK k ∈ Finset.Icc 1 (bdlLambda ^ k) := by
  have h1 := one_le_bdlScaleCutoffK k
  have h2 := two_mul_bdlScaleCutoffK_add_one_le_bdlLambda_pow hk
  exact Finset.mem_Icc.mpr ⟨h1, by omega⟩

lemma bdlLambda_pow_k_le_bdlBoxSide (k : ℕ) :
    bdlLambda ^ k ≤ bdlBoxSide k := by
  dsimp [bdlBoxSide, bBDL, bdlHierarchySteps]
  exact Nat.pow_le_pow_right bdlLambda_pos (by omega)

lemma c_star_BDL_mul_bdlBoxSide_eq_natCast (k : ℕ) :
    cStarBDL * (bdlBoxSide k : ℝ) = ((bdlLambda ^ (2 * k) : ℕ) : ℝ) := by
  dsimp [cStarBDL, bdlBoxSide, bBDL, bdlHierarchySteps]
  have h_pos : (0 : ℝ) < (bdlLambda : ℝ) ^ 4 :=
    pow_pos (Nat.cast_pos.mpr bdlLambda_pos) 4
  have h_ne : ((bdlLambda : ℝ) ^ 4) ≠ 0 := ne_of_gt h_pos
  push_cast
  rw [pow_add, one_div_mul_eq_div, mul_div_cancel_right₀ _ h_ne]

lemma floor_c_star_BDL_mul_bdlBoxSide_eq (k : ℕ) :
    Nat.floor (cStarBDL * (bdlBoxSide k : ℝ)) = bdlLambda ^ (2 * k) := by
  rw [c_star_BDL_mul_bdlBoxSide_eq_natCast, Nat.floor_natCast]

lemma bdlScaleCutoffK_add_two_le_L_star {k : ℕ} (hk : 4 ≤ k) :
    bdlScaleCutoffK k + 2 ≤ Nat.floor (cStarBDL * (bdlBoxSide k : ℝ)) := by
  rw [floor_c_star_BDL_mul_bdlBoxSide_eq]
  have h_pow : bdlLambda ^ (k - 4) * bdlLambda ≤ bdlLambda ^ (2 * k) := by
    rw [← pow_succ]
    exact Nat.pow_le_pow_right bdlLambda_pos (by omega)
  have h1 : 1 ≤ bdlLambda ^ (k - 4) := Nat.one_le_pow (k - 4) bdlLambda bdlLambda_pos
  have h3 : 3 ≤ bdlLambda := by decide
  have h_mul : bdlLambda ^ (k - 4) + 2 ≤ bdlLambda ^ (k - 4) * bdlLambda := by
    calc bdlLambda ^ (k - 4) + 2
      _ ≤ bdlLambda ^ (k - 4) + 2 * bdlLambda ^ (k - 4) := by omega
      _ = bdlLambda ^ (k - 4) * 3 := by ring
      _ ≤ bdlLambda ^ (k - 4) * bdlLambda := Nat.mul_le_mul_left _ h3
  exact le_trans h_mul h_pow

lemma collar_const_rca_bdl_mul_three_le_bdlLambda_pow_four :
    collarConstRCABDL * 3 ≤ bdlLambda ^ 4 := by
  decide

lemma linearExpansionRadius_collar_const_bdl_scaleCutoffK_le_safe_radius {k : ℕ} (hk : 4 ≤ k) :
    linearExpansionRadius (collarConstRCABDL : ℝ) (bdlScaleCutoffK k + bhmElementaryCubeSide) ≤
      bdlLambda ^ k := by
  dsimp [linearExpansionRadius, bhmElementaryCubeSide, bdlScaleCutoffK]
  have h_cast : (collarConstRCABDL : ℝ) * ((bdlLambda ^ (k - 4) + 2 : ℕ) : ℝ) =
      ((collarConstRCABDL * (bdlLambda ^ (k - 4) + 2) : ℕ) : ℝ) := by push_cast; ring
  rw [h_cast, Nat.ceil_natCast]
  have hk_eq : k = (k - 4) + 4 := (Nat.sub_add_cancel hk).symm
  rw [hk_eq, pow_add]
  have h1 : 1 ≤ bdlLambda ^ (k - 4) := Nat.one_le_pow (k - 4) bdlLambda bdlLambda_pos
  have h_le3 : bdlLambda ^ (k - 4) + 2 ≤ 3 * bdlLambda ^ (k - 4) := by omega
  have h_C : collarConstRCABDL * 3 ≤ bdlLambda ^ 4 := collar_const_rca_bdl_mul_three_le_bdlLambda_pow_four
  calc collarConstRCABDL * (bdlLambda ^ (k - 4) + 2)
    _ ≤ collarConstRCABDL * (3 * bdlLambda ^ (k - 4)) := Nat.mul_le_mul_left collarConstRCABDL h_le3
    _ = bdlLambda ^ (k - 4) * (collarConstRCABDL * 3) := by ring
    _ ≤ bdlLambda ^ (k - 4) * bdlLambda ^ 4 := Nat.mul_le_mul_left _ h_C

lemma bdlBoxSide_le_bdlScaleCutoffK_pow_six {k : ℕ} (hk : 7 ≤ k) :
    bdlBoxSide k ≤ (bdlScaleCutoffK k) ^ 6 := by
  dsimp [bdlBoxSide, bBDL, bdlHierarchySteps, bdlScaleCutoffK]
  rw [← pow_mul]
  exact Nat.pow_le_pow_right bdlLambda_pos (by omega)

lemma bdlBoxSide_injective : Function.Injective bdlBoxSide := by
  intro k₁ k₂ h_eq
  dsimp [bdlBoxSide, bBDL, bdlHierarchySteps] at h_eq
  have h_exp := (Nat.pow_right_injective one_lt_bdlLambda) h_eq
  omega

/-! ## 3. Exact Scalewise Splitting Envelope & `IsSuperpolynomialDecay` -/

/-- Exact scalewise splitting envelope supported on BDL box sides `L = bdlBoxSide k` ($k \ge 7$). -/
def bdlExactSplittingEnvelope (J_0 : ℝ) (g_tail g_LR : ℕ → ℝ) (L : ℕ) : ℝ :=
  if h : ∃ k : ℕ, 7 ≤ k ∧ bdlBoxSide k = L then
    let k := Classical.choose h
    max (4 * (J_0 * g_LR (bdlScaleCutoffK k)) ^ 2)
        (2 * ((L : ℝ) ^ 3 * (5 * (J_0 * g_tail (bdlScaleCutoffK k)))))
  else 0

lemma bdlExactSplittingEnvelope_eq_of_bdlBoxSide (J_0 : ℝ) (g_tail g_LR : ℕ → ℝ)
    {k : ℕ} (hk : 7 ≤ k) :
    bdlExactSplittingEnvelope J_0 g_tail g_LR (bdlBoxSide k) =
      max (4 * (J_0 * g_LR (bdlScaleCutoffK k)) ^ 2)
          (2 * (((bdlBoxSide k : ℝ) ^ 3) * (5 * (J_0 * g_tail (bdlScaleCutoffK k))))) := by
  have hex : ∃ m : ℕ, 7 ≤ m ∧ bdlBoxSide m = bdlBoxSide k := ⟨k, hk, rfl⟩
  have h_choose : Classical.choose hex = k :=
    bdlBoxSide_injective (Classical.choose_spec hex).2
  unfold bdlExactSplittingEnvelope
  rw [dif_pos hex, h_choose]

lemma bdlExactSplittingEnvelope_nonneg {J_0 : ℝ} {g_tail g_LR : ℕ → ℝ}
    (_hJ0 : 0 ≤ J_0) (_hg_tail : ∀ r, 0 ≤ g_tail r) (_hg_LR : ∀ r, 0 ≤ g_LR r) (L : ℕ) :
    0 ≤ bdlExactSplittingEnvelope J_0 g_tail g_LR L := by
  unfold bdlExactSplittingEnvelope
  split_ifs with h
  · exact le_trans (by positivity) (le_max_left _ _)
  · exact le_rfl

lemma four_mul_sq_J0_g_LR_le_bdlExactSplittingEnvelope (J_0 : ℝ) (g_tail g_LR : ℕ → ℝ)
    {k : ℕ} (hk : 7 ≤ k) :
    4 * (J_0 * g_LR (bdlScaleCutoffK k)) ^ 2 ≤
      bdlExactSplittingEnvelope J_0 g_tail g_LR (bdlBoxSide k) := by
  rw [bdlExactSplittingEnvelope_eq_of_bdlBoxSide J_0 g_tail g_LR hk]
  exact le_max_left _ _

lemma two_mul_vol_five_J0_g_tail_le_bdlExactSplittingEnvelope (J_0 : ℝ) (g_tail g_LR : ℕ → ℝ)
    {k : ℕ} (hk : 7 ≤ k) :
    2 * (((bdlBoxSide k : ℝ) ^ 3) * (5 * (J_0 * g_tail (bdlScaleCutoffK k)))) ≤
      bdlExactSplittingEnvelope J_0 g_tail g_LR (bdlBoxSide k) := by
  rw [bdlExactSplittingEnvelope_eq_of_bdlBoxSide J_0 g_tail g_LR hk]
  exact le_max_right _ _

/-- If `g_tail` and `g_LR` have superpolynomial decay and `0 ≤ J_0`, then
    `bdlExactSplittingEnvelope J_0 g_tail g_LR` has superpolynomial decay in `L`. -/
theorem isSuperpolynomialDecay_bdlExactSplittingEnvelope
    {J_0 : ℝ} (hJ0 : 0 ≤ J_0)
    {g_tail g_LR : ℕ → ℝ}
    (hg_tail : IsSuperpolynomialDecay g_tail)
    (hg_LR : IsSuperpolynomialDecay g_LR) :
    IsSuperpolynomialDecay (bdlExactSplittingEnvelope J_0 g_tail g_LR) := by
  refine ⟨bdlExactSplittingEnvelope_nonneg hJ0 hg_tail.1 hg_LR.1, ?_⟩
  intro n
  have h_t1 : Tendsto (fun K : ℕ => 4 * J_0 ^ 2 * ((K : ℝ) ^ (3 * n) * g_LR K) ^ 2)
      atTop (𝓝 0) := by
    have h_sq : Tendsto (fun K : ℕ => ((K : ℝ) ^ (3 * n) * g_LR K) ^ 2) atTop (𝓝 0) := by
      simpa using (hg_LR.2 (3 * n)).pow 2
    simpa [mul_zero] using h_sq.const_mul (4 * J_0 ^ 2)
  have h_t2 : Tendsto (fun K : ℕ => 10 * J_0 * ((K : ℝ) ^ (6 * n + 18) * g_tail K))
      atTop (𝓝 0) := by
    simpa [mul_zero] using (hg_tail.2 (6 * n + 18)).const_mul (10 * J_0)
  rw [Metric.tendsto_atTop]
  intro ε hε
  rcases Filter.eventually_atTop.mp
      ((h_t1.eventually (Iio_mem_nhds hε)).and (h_t2.eventually (Iio_mem_nhds hε)))
    with ⟨K₀, hK₀⟩
  refine ⟨K₀ ^ 6, fun L hL => ?_⟩
  have h_val_nn : 0 ≤ (L : ℝ) ^ n * bdlExactSplittingEnvelope J_0 g_tail g_LR L :=
    mul_nonneg (pow_nonneg (Nat.cast_nonneg L) n)
      (bdlExactSplittingEnvelope_nonneg hJ0 hg_tail.1 hg_LR.1 L)
  rw [Real.dist_eq, sub_zero, abs_of_nonneg h_val_nn]
  unfold bdlExactSplittingEnvelope
  split_ifs with hex
  · rcases Classical.choose_spec hex with ⟨hk7, hL_eq⟩
    set k := Classical.choose hex
    let K := bdlScaleCutoffK k
    have hL_nat : L ≤ K ^ 6 := by
      rw [← hL_eq]
      exact bdlBoxSide_le_bdlScaleCutoffK_pow_six hk7
    have hK₀_le_K : K₀ ≤ K := by
      by_contra h_lt
      have h_pow : K ^ 6 < K₀ ^ 6 :=
        Nat.pow_lt_pow_left (not_le.mp h_lt) (by decide : 6 ≠ 0)
      omega
    rcases hK₀ K hK₀_le_K with ⟨hK_t1, hK_t2⟩
    have hL_le_K6 : (L : ℝ) ≤ (K : ℝ) ^ 6 := by exact_mod_cast hL_nat
    have hL_nn : (0 : ℝ) ≤ (L : ℝ) := Nat.cast_nonneg L
    have hLn_le : (L : ℝ) ^ n ≤ (K : ℝ) ^ (6 * n) := by
      rw [pow_mul]
      exact pow_le_pow_left₀ hL_nn hL_le_K6 n
    have hL_np3_le : (L : ℝ) ^ (n + 3) ≤ (K : ℝ) ^ (6 * n + 18) := by
      have h_eq : 6 * n + 18 = 6 * (n + 3) := by ring
      rw [h_eq, pow_mul]
      exact pow_le_pow_left₀ hL_nn hL_le_K6 (n + 3)
    rw [mul_max_of_nonneg _ _ (pow_nonneg hL_nn n), max_lt_iff]
    refine ⟨?_, ?_⟩
    · calc (L : ℝ) ^ n * (4 * (J_0 * g_LR K) ^ 2)
        _ ≤ (K : ℝ) ^ (6 * n) * (4 * (J_0 * g_LR K) ^ 2) :=
          mul_le_mul_of_nonneg_right hLn_le (by positivity)
        _ = 4 * J_0 ^ 2 * ((K : ℝ) ^ (3 * n) * g_LR K) ^ 2 := by
          have h_pow : (K : ℝ) ^ (6 * n) = ((K : ℝ) ^ (3 * n)) ^ 2 := by
            rw [← pow_mul]; ring_nf
          rw [h_pow]; ring
        _ < ε := hK_t1
    · calc (L : ℝ) ^ n * (2 * ((L : ℝ) ^ 3 * (5 * (J_0 * g_tail K))))
        _ = 10 * J_0 * ((L : ℝ) ^ (n + 3) * g_tail K) := by
          rw [pow_add]; ring
        _ ≤ 10 * J_0 * ((K : ℝ) ^ (6 * n + 18) * g_tail K) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          exact mul_le_mul_of_nonneg_right hL_np3_le (hg_tail.1 K)
        _ < ε := hK_t2
  · rw [mul_zero]
    exact hε

end
