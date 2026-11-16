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

import Proofs.HastingsKomaLightCone.InterpolatedS1AndSuperpolyEnvelope

open scoped Classical InnerProduct ComplexConjugate BigOperators
open Filter Topology Asymptotics ContinuousLinearMap KMSPinchedGibbs PerturbedThermalBarrier
open WeldedHierarchy WeldedHierarchy.BDLDecoder InhomogeneousMemoryChallenge

noncomputable section

set_option maxRecDepth 200000
set_option maxHeartbeats 800000

/-!
# Centered Box-Ball Enclosing Cubes and Single-Ball TQO-1 Telescoping

Defines centered $\ell_\infty$-ball enclosing cubes `singleBallSupportC`, extracts local TQO-1 ground-state scalars `tqo1SiteBallCondExpScalar` for ball conditional expectations, and constructs the multi-scale ball approximations `indexedSingleBallApproxM` and annular shell differences `indexedSingleBallDiffD`. Proves exact safe-subspace commutator vanishing for all ball shell terms up to the protection cutoff and derives the chromatic subgrid Cauchy–Schwarz quadratic form bound against `H0`.

## References

* Part I, Section 5.4 (`subsec:safe-decoded-observables`), Proposition 5.7 (`prop:safe-subspace-immunity`)
* Part I, Section 7.1 (`subsec:single-cube-telescoping`), Lemma 7.1 (`lem:norm-transfer`)
* Part I, Section 7.1 (`subsec:single-cube-telescoping`), Proposition 7.2 (`prop:single-cube-telescoping`)
* Part II, Section 5.2 (`subsec:low-temp-crossover`), Proposition 5.2 (`prop:bhm-relative-form-bound`)
* Bravyi and Hastings (2011), Commun. Math. Phys. 307, 609–627
-/

/-! ## 1. Centered-Ball Support Cube Geometry & Overlap Multiplicity -/

/-- Corner anchor `u - r` on `BoxD D L` so that `boxBall u r ⊆ boxCube (shiftCorner u r) (2 * r + 1)`. -/
def shiftCorner {D L : ℕ} (v : BoxD D L) (r : ℕ) : BoxD D L :=
  fun i => ⟨(v i).val - r, Nat.sub_lt_of_lt (v i).isLt⟩

/-- Enclosing cube for `boxBall u k` under linear radius expansion `C`:
    `singleCubeSupportC C (shiftCorner u k) (2 * k + 1)`. -/
def singleBallSupportC {D L : ℕ} (C : ℝ) (u : BoxD D L) (k : ℕ) : Finset (BoxD D L) :=
  singleCubeSupportC C (shiftCorner u k) (2 * k + 1)

lemma singleBallSupportC_mem_BoxCubes {D L : ℕ} (C : ℝ) (u : BoxD D L) (k : ℕ) :
    singleBallSupportC C u k ∈
      boxCubes D L (linearExpansionRadius C ((2 * k + 1) + bhmElementaryCubeSide)) :=
  singleCubeSupportC_mem_BoxCubes C (shiftCorner u k) (2 * k + 1)

lemma boxBall_subset_singleBallSupportC {D L : ℕ} {C : ℝ} (hC : 1 ≤ C) (u : BoxD D L) (k : ℕ) :
    boxBall u k ⊆ singleBallSupportC C u k := by
  have h1 : boxBall u k ⊆ boxCube (shiftCorner u k) (2 * k + 1) := boxBall_subset_boxCube u k
  have h2 : boxCube (shiftCorner u k) (2 * k + 1) ⊆
      boxCube (shiftDownOne (shiftCorner u k)) ((2 * k + 1) + bhmElementaryCubeSide) :=
    (isOneCollarOf_boxCube_shiftDownOne (shiftCorner u k) (2 * k + 1)).1
  have h3 : (2 * k + 1) + bhmElementaryCubeSide ≤
      linearExpansionRadius C ((2 * k + 1) + bhmElementaryCubeSide) :=
    self_le_linearExpansionRadius_bhm hC ((2 * k + 1) + bhmElementaryCubeSide)
  exact Finset.Subset.trans h1 (Finset.Subset.trans h2
    (boxCube_subset_enclosingBoxCube (shiftDownOne (shiftCorner u k)) h3))

lemma linearExpansionRadius_add_two_le {C : ℝ} (hC : 1 ≤ C) (r : ℕ) :
    linearExpansionRadius C r + 2 ≤ linearExpansionRadius C (r + 2) := by
  have h1 := _root_.linearExpansionRadius_add_one_le hC r
  have h2 := _root_.linearExpansionRadius_add_one_le hC (r + 1)
  have h_eq : r + 1 + 1 = r + 2 := rfl
  rw [h_eq] at h2
  omega

theorem singleBallSupportC_pred_subset {D L : ℕ} {C : ℝ} (hC : 1 ≤ C) (u : BoxD D L)
    {k : ℕ} (hk2 : 2 ≤ k) :
    singleBallSupportC C u (k - 1) ⊆ singleBallSupportC C u k := by
  intro y hy
  simp only [singleBallSupportC, singleCubeSupportC, enclosingBoxCube, mem_boxCube] at hy ⊢
  intro i
  let r1 := (2 * (k - 1) + 1) + bhmElementaryCubeSide
  let r2 := (2 * k + 1) + bhmElementaryCubeSide
  have hr : r2 = r1 + 2 := by dsimp [r1, r2, bhmElementaryCubeSide]; omega
  let R1 := linearExpansionRadius C r1
  let R2 := linearExpansionRadius C r2
  have hR : R1 + 2 ≤ R2 := by
    dsimp [R1, R2]; rw [hr]; exact linearExpansionRadius_add_two_le hC r1
  have hi : ((shiftDownOne (shiftCorner u (k - 1)) i).val - (R1 - r1) / 2 ≤ (y i).val) ∧
      ((y i).val < (shiftDownOne (shiftCorner u (k - 1)) i).val - (R1 - r1) / 2 + R1) := hy i
  change ((shiftDownOne (shiftCorner u k) i).val - (R2 - r2) / 2 ≤ (y i).val) ∧
    ((y i).val < (shiftDownOne (shiftCorner u k) i).val - (R2 - r2) / 2 + R2)
  dsimp [shiftDownOne, shiftCorner, r1, r2, bhmElementaryCubeSide] at hi ⊢
  omega

lemma linearExpansionRadius_two_mul_add_one_le_three_mul {C : ℝ} (hC : 0 ≤ C) (k : ℕ) :
    linearExpansionRadius C ((2 * k + 1) + bhmElementaryCubeSide) ≤
      linearExpansionRadius (3 * C) (k + bhmElementaryCubeSide) := by
  dsimp [linearExpansionRadius, bhmElementaryCubeSide]
  apply Nat.ceil_mono; push_cast; nlinarith

lemma card_univ_filter_mem_singleBallSupportC_le_pow {D L : ℕ} [NeZero D] [NeZero L]
    {C : ℝ} (hC : 1 ≤ C) (k : ℕ) (y0 : BoxD D L) :
    let R_k := linearExpansionRadius (3 * C) (k + bhmElementaryCubeSide)
    (Finset.univ.filter (fun u : BoxD D L => y0 ∈ singleBallSupportC C u k)).card ≤
      (2 * (R_k + 1)) ^ D := by
  intro R_k
  let r0 := (2 * k + 1) + bhmElementaryCubeSide
  let R0 := linearExpansionRadius C r0
  let d : ℕ := (R0 - r0) / 2
  have hr0_le : r0 ≤ R0 := self_le_linearExpansionRadius_bhm hC r0
  have hR0_le : R0 ≤ R_k := linearExpansionRadius_two_mul_add_one_le_three_mul (by linarith) k
  have hL_pos : 0 < L := NeZero.pos L
  let M : ℕ := 2 * (R_k + 1)
  let g : (Fin D → Fin M) → BoxD D L := fun m i =>
    ⟨min (L - 1) ((y0 i).val + d + k + 1 - (m i).val),
      Nat.lt_of_le_of_lt (Nat.min_le_left _ _) (Nat.sub_lt hL_pos zero_lt_one)⟩
  have h_sub : Finset.univ.filter (fun u : BoxD D L => y0 ∈ singleBallSupportC C u k) ⊆
      Finset.univ.image g := by
    intro u hu
    have hy0 : y0 ∈ singleBallSupportC C u k := (Finset.mem_filter.mp hu).2
    simp only [singleBallSupportC, singleCubeSupportC, enclosingBoxCube, mem_boxCube,
      shiftDownOne, shiftCorner] at hy0
    have hm_lt : ∀ i : Fin D, (y0 i).val + d + k + 1 - (u i).val < M := by
      intro i
      have hi : ((u i).val - k - 1) - d ≤ (y0 i).val ∧
          (y0 i).val < ((u i).val - k - 1) - d + R0 := hy0 i
      dsimp [M, d, r0, bhmElementaryCubeSide] at hi hr0_le ⊢; omega
    refine Finset.mem_image.mpr ⟨fun i => ⟨(y0 i).val + d + k + 1 - (u i).val, hm_lt i⟩,
      Finset.mem_univ _, ?_⟩
    funext i; apply Fin.ext
    have hi : ((u i).val - k - 1) - d ≤ (y0 i).val ∧
        (y0 i).val < ((u i).val - k - 1) - d + R0 := hy0 i
    have hu_lt : (u i).val < L := (u i).isLt
    change min (L - 1) ((y0 i).val + d + k + 1 - ((y0 i).val + d + k + 1 - (u i).val)) = (u i).val
    omega
  calc (Finset.univ.filter (fun u : BoxD D L => y0 ∈ singleBallSupportC C u k)).card
    _ ≤ (Finset.univ.image g).card := Finset.card_le_card h_sub
    _ ≤ (Finset.univ : Finset (Fin D → Fin M)).card := Finset.card_image_le
    _ = M ^ D := by rw [Finset.card_univ, Fintype.card_fun, Fintype.card_fin, Fintype.card_fin]

/-! ## 2. Centered-Ball TQO-1 Scalar & Multi-Scale Difference Operators -/

def tqo1SiteBallCondExpScalar {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (sys : IndexedCommutingProjectorHamiltonian D L Site ι) (K : ℕ) (u : BoxD D L)
    (X : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site) : ℝ :=
  if h : ∃ c : ℂ, sys.P0 * condExp Site (boxBall u K) X * sys.P0 = c • sys.P0 then
    h.choose.re
  else 0

theorem tqo1SiteBallCondExpScalar_spec {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (sys : IndexedCommutingProjectorHamiltonian D L Site ι)
    {L_star K : ℕ} (hTQO1 : SatisfiesTQO1 sys L_star) (hKL : 2 * K + 1 ≤ L_star) (u : BoxD D L)
    {X : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site} (hX_sa : IsSelfAdjoint X) :
    let c_u := tqo1SiteBallCondExpScalar sys K u X
    sys.P0 * condExp Site (boxBall u K) X * sys.P0 = (c_u : ℂ) • sys.P0 ∧
    |c_u| ≤ ‖condExp Site (boxBall u K) X‖ := by
  intro c_u
  have h_supp : IsSupportedOn Site (boxCube (shiftCorner u K) (2 * K + 1))
      (condExp Site (boxBall u K) X) :=
    _root_.isSupportedOn_mono (boxBall_subset_boxCube u K) (isSupportedOn_condExp Site (boxBall u K) X)
  have h_ex : ∃ c : ℂ, sys.P0 * condExp Site (boxBall u K) X * sys.P0 = c • sys.P0 :=
    hTQO1 (2 * K + 1) (by omega) hKL (shiftCorner u K) (condExp Site (boxBall u K) X) h_supp
  have hc_def : c_u = h_ex.choose.re := by dsimp [c_u, tqo1SiteBallCondExpScalar]; rw [dif_pos h_ex]
  have hc_spec := h_ex.choose_spec
  have hO_sa : IsSelfAdjoint (condExp Site (boxBall u K) X) :=
    isSelfAdjoint_condExp_bhm (boxBall u K) hX_sa
  rcases tqo1_scalar_abs_le_norm_bhm sys.isStarProjection_P0 sys.frustration_free hc_spec with
    ⟨hc_norm, hc_im_fn⟩
  have hc_eq : (c_u : ℂ) = h_ex.choose := Complex.ext hc_def (hc_im_fn hO_sa).symm
  refine ⟨hc_spec.trans (by rw [← hc_eq]), ?_⟩
  have h_abs : ‖(c_u : ℂ)‖ = ‖h_ex.choose‖ := by rw [hc_eq]
  rw [Complex.norm_real, Real.norm_eq_abs] at h_abs; linarith

theorem norm_centeredSiteOp_tqo1SiteBallCondExpScalar_le_two_mul_norm {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    [∀ x, Nonempty (Site x)] {ι : Type} [Fintype ι] [DecidableEq ι]
    (sys : IndexedCommutingProjectorHamiltonian D L Site ι)
    {L_star K : ℕ} (hTQO1 : SatisfiesTQO1 sys L_star) (hKL : 2 * K + 1 ≤ L_star) (u : BoxD D L)
    {X : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site} (hX_sa : IsSelfAdjoint X) :
    ‖centeredSiteOp X (tqo1SiteBallCondExpScalar sys K u X)‖ ≤ 2 * ‖X‖ := by
  let c_u := tqo1SiteBallCondExpScalar sys K u X
  have hc_le : |c_u| ≤ ‖X‖ :=
    le_trans (tqo1SiteBallCondExpScalar_spec sys hTQO1 hKL u hX_sa).2 (norm_condExp_le (boxBall u K) X)
  have h1_le : ‖(c_u : ℂ) • (1 : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site)‖ ≤ ‖X‖ := by
    rw [norm_smul, Complex.norm_real, Real.norm_eq_abs]
    exact le_trans (mul_le_of_le_one_right (abs_nonneg c_u) ContinuousLinearMap.norm_id_le) hc_le
  dsimp [centeredSiteOp]
  linarith [norm_sub_le X ((c_u : ℂ) • (1 : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site))]

theorem norm_P0_mul_centeredSiteOp_boxBall_le {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (sys : IndexedCommutingProjectorHamiltonian D L Site ι) (K : ℕ) (u : BoxD D L)
    {X : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site} {c ε_K : ℝ}
    (hX_comm : Commute X sys.P0)
    (hc_P0 : sys.P0 * condExp Site (boxBall u K) X * sys.P0 = (c : ℂ) • sys.P0)
    (h_tail_K : ‖X - condExp Site (boxBall u K) X‖ ≤ ε_K) :
    ‖sys.P0 * centeredSiteOp X c‖ ≤ ε_K := by
  have hP0_idem : sys.P0 * sys.P0 = sys.P0 := sys.isStarProjection_P0.isIdempotentElem.eq
  have hP0_norm : ‖sys.P0‖ ≤ 1 := isStarProjection_norm_le_one_bhm sys.isStarProjection_P0
  have hP0_X_P0 : (sys.P0 * sys.P0) * X = sys.P0 * X * sys.P0 := by
    calc (sys.P0 * sys.P0) * X
      _ = sys.P0 * (sys.P0 * X) := mul_assoc _ _ _
      _ = sys.P0 * (X * sys.P0) := by rw [hX_comm.eq]
      _ = sys.P0 * X * sys.P0 := (mul_assoc _ _ _).symm
  have h_eq : sys.P0 * centeredSiteOp X c =
      sys.P0 * (X - condExp Site (boxBall u K) X) * sys.P0 := by
    dsimp [centeredSiteOp]
    calc sys.P0 * (X - (c : ℂ) • 1)
      _ = sys.P0 * X - sys.P0 * ((c : ℂ) • 1) := mul_sub sys.P0 X _
      _ = (sys.P0 * sys.P0) * X - (c : ℂ) • sys.P0 := by
        rw [hP0_idem, mul_smul_comm, mul_one]
      _ = sys.P0 * X * sys.P0 - sys.P0 * condExp Site (boxBall u K) X * sys.P0 := by
        rw [hP0_X_P0, hc_P0]
      _ = sys.P0 * (X - condExp Site (boxBall u K) X) * sys.P0 := by
        rw [mul_sub, sub_mul]
  rw [h_eq]
  exact le_trans (norm_sandwich_le_of_norm_le_one hP0_norm hP0_norm) h_tail_K

private lemma ring_P0_centered_decomp {R : Type*} [Ring R] (P X C S : R)
    (hS : P * S = P * C * P) :
    P * (X - S) = P * (X - C) * P + P * X * (1 - P) := by
  rw [mul_sub P X S, hS, mul_sub P X C, sub_mul, mul_sub (P * X) 1 P, mul_one, sub_add_sub_cancel']

theorem norm_P0_mul_centeredSiteOp_boxBall_le_of_offDiag {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (sys : IndexedCommutingProjectorHamiltonian D L Site ι) (K : ℕ) (u : BoxD D L)
    {X : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site} {c ε_K : ℝ}
    (hc_P0 : sys.P0 * condExp Site (boxBall u K) X * sys.P0 = (c : ℂ) • sys.P0)
    (h_tail_off_K : ‖X - condExp Site (boxBall u K) X‖ + ‖sys.P0 * X * (1 - sys.P0)‖ ≤ ε_K) :
    ‖sys.P0 * centeredSiteOp X c‖ ≤ ε_K := by
  have hP0_norm : ‖sys.P0‖ ≤ 1 := isStarProjection_norm_le_one_bhm sys.isStarProjection_P0
  have hS : sys.P0 * ((c : ℂ) • (1 : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site)) =
      sys.P0 * condExp Site (boxBall u K) X * sys.P0 :=
    (mul_smul_comm (c : ℂ) sys.P0 1).trans (by rw [mul_one sys.P0]; exact hc_P0.symm)
  have h_eq : sys.P0 * centeredSiteOp X c =
      sys.P0 * (X - condExp Site (boxBall u K) X) * sys.P0 + sys.P0 * X * (1 - sys.P0) := by
    dsimp only [centeredSiteOp]
    exact ring_P0_centered_decomp sys.P0 X (condExp Site (boxBall u K) X) ((c : ℂ) • 1) hS
  have h1 : ‖sys.P0 * (X - condExp Site (boxBall u K) X) * sys.P0 + sys.P0 * X * (1 - sys.P0)‖ ≤
      ‖sys.P0 * (X - condExp Site (boxBall u K) X) * sys.P0‖ + ‖sys.P0 * X * (1 - sys.P0)‖ :=
    norm_add_le _ _
  have h2 : ‖sys.P0 * (X - condExp Site (boxBall u K) X) * sys.P0‖ ≤
      ‖X - condExp Site (boxBall u K) X‖ :=
    norm_sandwich_le_of_norm_le_one hP0_norm hP0_norm
  rw [h_eq]
  linarith

def indexedLocalBallTelescopingApprox {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (sys : IndexedCommutingProjectorHamiltonian D L Site ι) (C : ℝ) (u : BoxD D L) (k : ℕ)
    (X_u' : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site) :
    ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site :=
  let C_k := singleBallSupportC C u k
  (1 - sys.localGroundProj C_k) * condExp Site (boxBall u k) X_u' * (1 - sys.localGroundProj C_k)

def indexedSingleBallApproxM {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (sys : IndexedCommutingProjectorHamiltonian D L Site ι) (C : ℝ) (u : BoxD D L) (k : ℕ)
    (X_u' : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site) :
    ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site :=
  if k = 0 then 0 else indexedLocalBallTelescopingApprox sys C u k X_u'

def indexedSingleBallDiffD {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (sys : IndexedCommutingProjectorHamiltonian D L Site ι) (C : ℝ) (u : BoxD D L) (k : ℕ)
    (X_u' : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site) :
    ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site :=
  indexedSingleBallApproxM sys C u k X_u' - indexedSingleBallApproxM sys C u (k - 1) X_u'

@[simp]
lemma indexedSingleBallApproxM_zero {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (sys : IndexedCommutingProjectorHamiltonian D L Site ι) (C : ℝ) (u : BoxD D L)
    (X_u' : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site) :
    indexedSingleBallApproxM sys C u 0 X_u' = 0 := rfl

lemma indexedSingleBallApproxM_of_pos {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (sys : IndexedCommutingProjectorHamiltonian D L Site ι) (C : ℝ) (u : BoxD D L)
    {k : ℕ} (hk : 1 ≤ k) (X_u' : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site) :
    indexedSingleBallApproxM sys C u k X_u' = indexedLocalBallTelescopingApprox sys C u k X_u' :=
  if_neg (by omega)

theorem sum_indexedSingleBallDiffD_eq {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (sys : IndexedCommutingProjectorHamiltonian D L Site ι) (C : ℝ) (u : BoxD D L) (K : ℕ)
    (X_u' : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site) :
    (∑ k ∈ Finset.Icc 1 K, indexedSingleBallDiffD sys C u k X_u') =
      indexedSingleBallApproxM sys C u K X_u' ∧
    X_u' = (∑ k ∈ Finset.Icc 1 K, indexedSingleBallDiffD sys C u k X_u') +
      (X_u' - indexedSingleBallApproxM sys C u K X_u') := by
  have h_sum : (∑ k ∈ Finset.Icc 1 K, indexedSingleBallDiffD sys C u k X_u') =
      indexedSingleBallApproxM sys C u K X_u' := by
    induction K with
    | zero => simp [indexedSingleBallApproxM_zero]
    | succ m ih =>
      rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ m + 1), ih]; dsimp [indexedSingleBallDiffD]; abel
  exact ⟨h_sum, by rw [h_sum, add_sub_cancel]⟩

theorem isSupportedOn_indexedSingleBallApproxM {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (sys : IndexedCommutingProjectorHamiltonian D L Site ι) {C : ℝ} (hC : 1 ≤ C) (u : BoxD D L)
    {k : ℕ} (hk1 : 1 ≤ k) (X_u' : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site) :
    IsSupportedOn Site (singleBallSupportC C u k) (indexedSingleBallApproxM sys C u k X_u') := by
  let C_k := singleBallSupportC C u k
  rw [indexedSingleBallApproxM_of_pos sys C u hk1 X_u']
  have hO_supp : IsSupportedOn Site (boxBall u k) (condExp Site (boxBall u k) X_u') := ⟨_, rfl⟩
  have h1PC_supp : IsSupportedOn Site C_k (1 - sys.localGroundProj C_k) :=
    _root_.isSupportedOn_sub C_k (_root_.isSupportedOn_one C_k) (sys.isSupportedOn_P_loc C_k)
  exact _root_.isSupportedOn_mul C_k
    (_root_.isSupportedOn_mul C_k h1PC_supp
      (_root_.isSupportedOn_mono (boxBall_subset_singleBallSupportC hC u k) hO_supp))
    h1PC_supp

theorem pi_safe_commutator_indexedSingleBallApproxM_eq_zero {D L R_fw : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (sys : IndexedCommutingProjectorHamiltonian D L Site ι)
    (Pi_safe O_dec : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site)
    (h_fw : ∀ (W : QuasiLocalPerturbation D L Site),
      ∀ r ∈ Finset.Icc 1 R_fw, ∀ A ∈ boxCubes D L r,
        Pi_safe * (W.term r A * O_dec - O_dec * W.term r A) * Pi_safe = 0)
    {C : ℝ} (hC : 1 ≤ C) (u : BoxD D L) (k : ℕ)
    (hk_fw : linearExpansionRadius C ((2 * k + 1) + bhmElementaryCubeSide) ≤ R_fw)
    (X_u' : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site) :
    Pi_safe * (indexedSingleBallApproxM sys C u k X_u' * O_dec -
      O_dec * indexedSingleBallApproxM sys C u k X_u') * Pi_safe = 0 := by
  rcases Nat.eq_zero_or_pos k with rfl | hk_pos
  · simp [indexedSingleBallApproxM_zero]
  · have hr_mem : linearExpansionRadius C ((2 * k + 1) + bhmElementaryCubeSide) ∈ Finset.Icc 1 R_fw :=
      Finset.mem_Icc.mpr ⟨one_le_linearExpansionRadius_add_elementary hC (2 * k + 1), hk_fw⟩
    exact pi_safe_commutator_eq_zero_of_isSupportedOn_cube Pi_safe O_dec h_fw hr_mem
      (singleBallSupportC_mem_BoxCubes C u k)
      (isSupportedOn_indexedSingleBallApproxM sys hC u hk_pos X_u')

theorem pi_safe_commutator_indexedSingleBallDiffD_eq_zero {D L R_fw : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (sys : IndexedCommutingProjectorHamiltonian D L Site ι)
    (Pi_safe O_dec : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site)
    (h_fw : ∀ (W : QuasiLocalPerturbation D L Site),
      ∀ r ∈ Finset.Icc 1 R_fw, ∀ A ∈ boxCubes D L r,
        Pi_safe * (W.term r A * O_dec - O_dec * W.term r A) * Pi_safe = 0)
    {C : ℝ} (hC : 1 ≤ C) (u : BoxD D L) (k : ℕ)
    (hk_fw : linearExpansionRadius C ((2 * k + 1) + bhmElementaryCubeSide) ≤ R_fw)
    (X_u' : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site) :
    Pi_safe * (indexedSingleBallDiffD sys C u k X_u' * O_dec -
      O_dec * indexedSingleBallDiffD sys C u k X_u') * Pi_safe = 0 := by
  unfold indexedSingleBallDiffD
  have hk_prev_fw : linearExpansionRadius C ((2 * (k - 1) + 1) + bhmElementaryCubeSide) ≤ R_fw :=
    le_trans (linearExpansionRadius_mono (by linarith) (by omega)) hk_fw
  exact pi_safe_commutator_sub_eq_zero Pi_safe O_dec
    (indexedSingleBallApproxM sys C u k X_u') (indexedSingleBallApproxM sys C u (k - 1) X_u')
    (pi_safe_commutator_indexedSingleBallApproxM_eq_zero sys Pi_safe O_dec h_fw hC u k hk_fw X_u')
    (pi_safe_commutator_indexedSingleBallApproxM_eq_zero sys Pi_safe O_dec h_fw hC u (k - 1)
      hk_prev_fw X_u')

theorem indexedSingleBallDiffD_isSelfAdjoint_and_mul_P_loc_eq_zero {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (sys : IndexedCommutingProjectorHamiltonian D L Site ι)
    {C : ℝ} (hC : 1 ≤ C) (u : BoxD D L) {k : ℕ} (hk1 : 1 ≤ k)
    {X : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site} (hX_sa : IsSelfAdjoint X) :
    let C_k := singleBallSupportC C u k
    let D_k := indexedSingleBallDiffD sys C u k X
    IsSelfAdjoint D_k ∧ D_k * sys.localGroundProj C_k = 0 := by
  intro C_k D_k
  have hM_sa : ∀ m : ℕ, IsSelfAdjoint (indexedSingleBallApproxM sys C u m X) := by
    intro m
    rcases Nat.eq_zero_or_pos m with rfl | hm_pos
    · rw [indexedSingleBallApproxM_zero, ContinuousLinearMap.isSelfAdjoint_iff', map_zero]
    · rw [indexedSingleBallApproxM_of_pos sys C u hm_pos X, isSelfAdjoint_iff]
      dsimp [indexedLocalBallTelescopingApprox]
      have h1 := (sys.isStarProjection_P_loc_bhm (singleBallSupportC C u m)).one_sub.isSelfAdjoint.star_eq
      have hO := (isSelfAdjoint_condExp_bhm (boxBall u m) hX_sa).star_eq
      rw [star_mul, star_mul, h1, hO, mul_assoc]
  have hD_sa : IsSelfAdjoint D_k := by
    rw [ContinuousLinearMap.isSelfAdjoint_iff']; dsimp [D_k, indexedSingleBallDiffD]
    rw [map_sub, ContinuousLinearMap.isSelfAdjoint_iff'.mp (hM_sa k),
      ContinuousLinearMap.isSelfAdjoint_iff'.mp (hM_sa (k - 1))]
  have hMk_P : indexedSingleBallApproxM sys C u k X * sys.localGroundProj C_k = 0 := by
    rw [indexedSingleBallApproxM_of_pos sys C u hk1 X]; dsimp [indexedLocalBallTelescopingApprox]
    have h1 : (1 - sys.localGroundProj C_k) * sys.localGroundProj C_k = 0 := by
      rw [sub_mul, one_mul, (sys.isStarProjection_P_loc_bhm C_k).isIdempotentElem.eq, sub_self]
    rw [mul_assoc, h1, mul_zero]
  have hMprev_P : indexedSingleBallApproxM sys C u (k - 1) X * sys.localGroundProj C_k = 0 := by
    rcases le_or_gt 2 k with hk2 | hk_lt2
    · rw [indexedSingleBallApproxM_of_pos sys C u (by omega : 1 ≤ k - 1) X]
      dsimp [indexedLocalBallTelescopingApprox]
      have hSub : singleBallSupportC C u (k - 1) ⊆ C_k := singleBallSupportC_pred_subset hC u hk2
      have h1 : (1 - sys.localGroundProj (singleBallSupportC C u (k - 1))) * sys.localGroundProj C_k = 0 := by
        rw [sub_mul, one_mul, (sys.localProj_mul_localProj_of_subset_bhm hSub).1, sub_self]
      rw [mul_assoc, h1, mul_zero]
    · rw [(by omega : k - 1 = 0), indexedSingleBallApproxM_zero, zero_mul]
  exact ⟨hD_sa, by dsimp [D_k, indexedSingleBallDiffD]; rw [sub_mul, hMk_P, hMprev_P, sub_self]⟩

lemma norm_indexedSingleBallDiffD_le_of_approx_bounds {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (sys : IndexedCommutingProjectorHamiltonian D L Site ι) (C : ℝ) (u : BoxD D L) (k : ℕ)
    (X : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site) {δ_k δ_prev : ℝ}
    (hk : ‖X - indexedSingleBallApproxM sys C u k X‖ ≤ δ_k)
    (hprev : ‖X - indexedSingleBallApproxM sys C u (k - 1) X‖ ≤ δ_prev) :
    ‖indexedSingleBallDiffD sys C u k X‖ ≤ δ_k + δ_prev := by
  have h_eq : indexedSingleBallDiffD sys C u k X =
      (X - indexedSingleBallApproxM sys C u (k - 1) X) -
      (X - indexedSingleBallApproxM sys C u k X) := by dsimp [indexedSingleBallDiffD]; abel
  rw [h_eq]
  linarith [norm_sub_le (X - indexedSingleBallApproxM sys C u (k - 1) X)
    (X - indexedSingleBallApproxM sys C u k X)]

/-! ## 3. Centered-Ball Relative Form Bound and Coherent Safe-Subspace Immunity -/

lemma sum_univ_singleBallSupportC_le_pow_mul_re_inner_H0 {D L : ℕ} [NeZero D] [NeZero L]
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (sys : IndexedCommutingProjectorHamiltonian D L Site ι) (h_weight : ∀ i : ι, 1 ≤ sys.weight i)
    {C : ℝ} (hC : 1 ≤ C) (k : ℕ) (ψ : ManyBodyHilbertSpace Site) :
    let R_k := linearExpansionRadius (3 * C) (k + bhmElementaryCubeSide)
    ∑ u : BoxD D L,
      ∑ i ∈ Finset.univ.filter (fun i : ι => sys.support i ⊆ singleBallSupportC C u k),
        ‖sys.checkProj i ψ‖ ^ 2 ≤
      (((2 * (R_k + 1) : ℕ) : ℝ) ^ D) * RCLike.re (inner ℂ ψ (sys.H0 ψ)) := by
  intro R_k
  have h_swap :
      ∑ u : BoxD D L,
        ∑ i ∈ Finset.univ.filter (fun i : ι => sys.support i ⊆ singleBallSupportC C u k),
          ‖sys.checkProj i ψ‖ ^ 2 =
      ∑ i : ι,
        ((Finset.univ.filter (fun u : BoxD D L => sys.support i ⊆ singleBallSupportC C u k)).card : ℝ) *
          ‖sys.checkProj i ψ‖ ^ 2 := by
    simp_rw [Finset.sum_filter]; rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
  rw [h_swap]
  have h_each : ∀ i : ι,
      ((Finset.univ.filter (fun u : BoxD D L => sys.support i ⊆ singleBallSupportC C u k)).card : ℝ) *
        ‖sys.checkProj i ψ‖ ^ 2 ≤
      (((2 * (R_k + 1) : ℕ) : ℝ) ^ D) * ‖sys.checkProj i ψ‖ ^ 2 := by
    intro i
    by_cases h_ne : (sys.support i).Nonempty
    · let y0 := h_ne.choose
      have hy0_mem : y0 ∈ sys.support i := h_ne.choose_spec
      have h_sub : Finset.univ.filter (fun u : BoxD D L => sys.support i ⊆ singleBallSupportC C u k) ⊆
          Finset.univ.filter (fun u : BoxD D L => y0 ∈ singleBallSupportC C u k) := fun u hu =>
        Finset.mem_filter.mpr ⟨Finset.mem_univ u, (Finset.mem_filter.mp hu).2 hy0_mem⟩
      have h_card := le_trans (Finset.card_le_card h_sub)
        (card_univ_filter_mem_singleBallSupportC_le_pow hC k y0)
      exact mul_le_mul_of_nonneg_right (by exact_mod_cast h_card) (sq_nonneg _)
    · have hQ_zero : sys.checkProj i = 0 :=
        sys.checkProj_eq_zero_of_support_empty (Finset.not_nonempty_iff_eq_empty.mp h_ne)
      rw [hQ_zero, ContinuousLinearMap.zero_apply, norm_zero, sq, mul_zero, mul_zero, mul_zero]
  calc ∑ i : ι,
        ((Finset.univ.filter (fun u : BoxD D L => sys.support i ⊆ singleBallSupportC C u k)).card : ℝ) *
          ‖sys.checkProj i ψ‖ ^ 2
    _ ≤ ∑ i : ι, (((2 * (R_k + 1) : ℕ) : ℝ) ^ D) * ‖sys.checkProj i ψ‖ ^ 2 :=
      Finset.sum_le_sum (fun i _ => h_each i)
    _ = (((2 * (R_k + 1) : ℕ) : ℝ) ^ D) * ∑ i : ι, ‖sys.checkProj i ψ‖ ^ 2 := by rw [← Finset.mul_sum]
    _ ≤ (((2 * (R_k + 1) : ℕ) : ℝ) ^ D) * RCLike.re (inner ℂ ψ (sys.H0 ψ)) :=
      mul_le_mul_of_nonneg_left (sys.sum_norm_checkProj_sq_le_re_inner_H0 h_weight ψ)
        (pow_nonneg (Nat.cast_nonneg _) D)

theorem abs_re_inner_sum_indexedSingleBallDiffD_le_re_inner_H0 {D L : ℕ} [NeZero D] [NeZero L]
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (sys : IndexedCommutingProjectorHamiltonian D L Site ι) (h_weight : ∀ i : ι, 1 ≤ sys.weight i)
    {C : ℝ} (hC : 1 ≤ C) {k : ℕ} (hk1 : 1 ≤ k)
    (X_hat : BoxD D L → (ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site))
    {δ_k : ℝ} (hδ_nn : 0 ≤ δ_k) (hX_sa : ∀ u : BoxD D L, IsSelfAdjoint (X_hat u))
    (hD_norm : ∀ u : BoxD D L, ‖indexedSingleBallDiffD sys C u k (X_hat u)‖ ≤ δ_k)
    (ψ : ManyBodyHilbertSpace Site) :
    let R_k := linearExpansionRadius (3 * C) (k + bhmElementaryCubeSide)
    |RCLike.re (inner ℂ ψ ((∑ u : BoxD D L, indexedSingleBallDiffD sys C u k (X_hat u)) ψ))| ≤
      (δ_k * (((2 * (R_k + 1) : ℕ) : ℝ) ^ D)) * RCLike.re (inner ℂ ψ (sys.H0 ψ)) := by
  intro R_k
  rw [re_inner_sum_apply]
  calc |∑ u : BoxD D L, RCLike.re (inner ℂ ψ (indexedSingleBallDiffD sys C u k (X_hat u) ψ))|
    _ ≤ ∑ u : BoxD D L, |RCLike.re (inner ℂ ψ (indexedSingleBallDiffD sys C u k (X_hat u) ψ))| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ u : BoxD D L,
        δ_k * ∑ i ∈ Finset.univ.filter (fun i : ι => sys.support i ⊆ singleBallSupportC C u k),
          ‖sys.checkProj i ψ‖ ^ 2 := by
      refine Finset.sum_le_sum (fun u _ => ?_)
      rcases indexedSingleBallDiffD_isSelfAdjoint_and_mul_P_loc_eq_zero sys hC u hk1 (hX_sa u) with
        ⟨hD_sa, hD_P⟩
      exact le_trans (abs_re_inner_le_of_mul_P_loc_eq_zero sys (singleBallSupportC C u k) hD_sa hD_P ψ)
        (mul_le_mul_of_nonneg_right (hD_norm u) (Finset.sum_nonneg (fun _ _ => sq_nonneg _)))
    _ = δ_k * ∑ u : BoxD D L,
          ∑ i ∈ Finset.univ.filter (fun i : ι => sys.support i ⊆ singleBallSupportC C u k),
            ‖sys.checkProj i ψ‖ ^ 2 := by rw [← Finset.mul_sum]
    _ ≤ δ_k * ((((2 * (R_k + 1) : ℕ) : ℝ) ^ D) * RCLike.re (inner ℂ ψ (sys.H0 ψ))) :=
      mul_le_mul_of_nonneg_left
        (sum_univ_singleBallSupportC_le_pow_mul_re_inner_H0 sys h_weight hC k ψ) hδ_nn
    _ = (δ_k * (((2 * (R_k + 1) : ℕ) : ℝ) ^ D)) * RCLike.re (inner ℂ ψ (sys.H0 ψ)) := by ring

theorem conj_sub_H0_sub_shift_eq_centered_telescoping_of_siteFamily_boxBall {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (sys : IndexedCommutingProjectorHamiltonian D L Site ι) (V : QuasiLocalPerturbation D L Site)
    (U : unitary (ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site))
    (X_u : BoxD D L → (ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site))
    (h_sum_X : (∑ u : BoxD D L, X_u u) = U.1† * (sys.H0 + V.totalPerturbation) * U.1 - sys.H0)
    (C : ℝ) (K : ℕ) (c_u : BoxD D L → ℝ) :
    let X_hat := fun u : BoxD D L => centeredSiteOp (X_u u) (c_u u)
    let c_shift : ℝ := ∑ u : BoxD D L, c_u u
    U.1† * (sys.H0 + V.totalPerturbation) * U.1 - sys.H0 - (c_shift : ℂ) • 1 =
      (∑ u : BoxD D L, ∑ k ∈ Finset.Icc 1 K, indexedSingleBallDiffD sys C u k (X_hat u)) +
      (∑ u : BoxD D L, (X_hat u - indexedSingleBallApproxM sys C u K (X_hat u))) := by
  intro X_hat c_shift
  have h_sum_c : (∑ u : BoxD D L,
      (c_u u : ℂ) • (1 : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site)) =
      (c_shift : ℂ) • 1 := by dsimp [c_shift]; rw [← Finset.sum_smul, Complex.ofReal_sum]
  have h_sum_hat : (∑ u : BoxD D L, X_hat u) =
      U.1† * (sys.H0 + V.totalPerturbation) * U.1 - sys.H0 - (c_shift : ℂ) • 1 := by
    dsimp [X_hat, centeredSiteOp]; rw [Finset.sum_sub_distrib, h_sum_X, h_sum_c]
  rw [← h_sum_hat, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl (fun u _ => (sum_indexedSingleBallDiffD_eq sys C u K (X_hat u)).2)

end
