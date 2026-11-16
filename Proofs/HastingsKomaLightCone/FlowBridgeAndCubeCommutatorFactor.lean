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

import Proofs.KatoHastingsFlow.AnchoredCheckDriftAndTailProfiles
import Proofs.TwoAxisMemorySynthesis.CenteredBoxBallScaleCalibration

open scoped Classical InnerProduct ComplexConjugate BigOperators
open Filter Topology Asymptotics ContinuousLinearMap KMSPinchedGibbs PerturbedThermalBarrier
open WeldedHierarchy WeldedHierarchy.BDLDecoder InhomogeneousMemoryChallenge

noncomputable section

set_option maxRecDepth 200000
set_option maxHeartbeats 800000

/-!
# Uniform Cube Commutator Factors and Full-Scale Flow Decay Bridges

Establishes definitional bridges between `sitePerturbationOp` and `anchoredSitePerturbationOp` (`sitePerturbationOp_eq_anchoredSitePerturbationOp`, `siteCheckOp_eq_anchoredSiteCheckOp`), along with system-size-independent bounds on `uniformCubeCommutatorFactor` (`uniformCubeCommutatorFactor_le_tsum`) and site check weights (`bdlInhomogeneousSiteWeightBound`, `bdlInhomogeneousCommutatorBound`, `bdlInhomogeneousBaseNormM0WithGenDecay`, `bdlInhomogeneousBaseNormM0`). Combines conditional expectation decay bounds across all spatial scales along `IsKatoHastingsFlowSystem`.

## References

* Part I, Section 6.1 (`subsec:dsuper-banach`), Definition 6.1 (`def:banach-quasilocal`), Equation (64) (`eq:site-anchored-decomp`)
* Part I, Section 6.3 (`subsec:qac-block-diag`), Equation (78) (`eq:Xu-norm-and-tail`)
-/

/-! ## 1. Definitional Bridges Between Site Perturbation and Anchored Site Operators -/

lemma anchorOfCube_eq_qacAnchorOfCube {D L : ℕ} [NeZero L] :
    (@anchorOfCube D L _) = (@qacAnchorOfCube D L _) := rfl

lemma sitePerturbationOp_eq_anchoredSitePerturbationOp {D L : ℕ} [NeZero L]
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    (V : QuasiLocalPerturbation D L Site) (u : BoxD D L) :
    sitePerturbationOp V u = anchoredSitePerturbationOp anchorOfCube V u := rfl

lemma siteCheckOp_eq_anchoredSiteCheckOp {D L : ℕ} [NeZero L]
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (sys : IndexedCommutingProjectorHamiltonian D L Site ι) (u : BoxD D L) :
    sys.siteCheckOp u = anchoredSiteCheckOp anchorOfRegion sys u := rfl

/-! ## 2. $L$-Independent Bounds on `boxCube`, `boxBall`, and `uniformCubeCommutatorFactor` -/

/-- Every open-box cube `boxCube x0 r` on `BoxD D L` has cardinality at most `r ^ D`. -/
lemma card_boxCube_le_pow {D L : ℕ} [NeZero D] [NeZero L] (x0 : BoxD D L) (r : ℕ) :
    (boxCube x0 r).card ≤ r ^ D := by
  by_cases hr : r = 0
  · subst hr
    have h_empty : boxCube x0 0 = ∅ := by
      ext y
      simp only [Finset.notMem_empty, iff_false]
      intro hy
      rw [mem_boxCube] at hy
      have hi0 := hy ⟨0, NeZero.pos D⟩; omega
    rw [h_empty, Finset.card_empty]; exact Nat.zero_le _
  · have hL_pos : 0 < L := NeZero.pos L
    let g : (Fin D → Fin r) → BoxD D L := fun m i =>
      ⟨min (L - 1) ((x0 i).val + (m i).val),
        Nat.lt_of_le_of_lt (Nat.min_le_left _ _) (Nat.sub_lt hL_pos zero_lt_one)⟩
    have h_sub : boxCube x0 r ⊆ Finset.univ.image g := by
      intro y hy
      rw [mem_boxCube] at hy
      let m : Fin D → Fin r := fun i => ⟨(y i).val - (x0 i).val, by have := hy i; omega⟩
      rw [Finset.mem_image]
      refine ⟨m, Finset.mem_univ m, ?_⟩
      funext i; apply Fin.ext
      have hi := hy i
      have hy_lt : (y i).val < L := (y i).isLt
      change min (L - 1) ((x0 i).val + ((y i).val - (x0 i).val)) = (y i).val
      omega
    calc (boxCube x0 r).card
      _ ≤ (Finset.univ.image g).card := Finset.card_le_card h_sub
      _ ≤ (Finset.univ : Finset (Fin D → Fin r)).card := Finset.card_image_le
      _ = r ^ D := by rw [Finset.card_univ, Fintype.card_fun, Fintype.card_fin, Fintype.card_fin]

/-- Every $\ell_\infty$-ball `boxBall u r` on `BoxD D L` has cardinality at most `(2 * r + 1) ^ D`. -/
lemma card_boxBall_le_pow {D L : ℕ} [NeZero D] [NeZero L] (u : BoxD D L) (r : ℕ) :
    (boxBall u r).card ≤ (2 * r + 1) ^ D :=
  le_trans (Finset.card_le_card (boxBall_subset_boxCube u r))
    (card_boxCube_le_pow _ (2 * r + 1))

/-- For any `u : BoxD D L` and `q, r_c : ℕ`, at most `(q + r_c) ^ D` cubes `A ∈ BoxCubes D L q`
    intersect `boxCube u r_c`. -/
lemma card_filter_not_disjoint_boxCube_le_pow {D L : ℕ} [NeZero D] [NeZero L]
    (u : BoxD D L) (q r_c : ℕ) :
    ((boxCubes D L q).filter (fun A => ¬ Disjoint A (boxCube u r_c))).card ≤
      (q + r_c) ^ D := by
  have hL_pos : 0 < L := NeZero.pos L
  let M : ℕ := q + r_c
  let g : (Fin D → Fin M) → Finset (BoxD D L) := fun k =>
    boxCube (fun i => ⟨min (L - 1) ((u i).val + r_c - 1 - (k i).val),
      Nat.lt_of_le_of_lt (Nat.min_le_left _ _) (Nat.sub_lt hL_pos zero_lt_one)⟩) q
  have h_sub :
      (boxCubes D L q).filter (fun A => ¬ Disjoint A (boxCube u r_c)) ⊆
        Finset.univ.image g := by
    intro A hA
    rcases Finset.mem_filter.mp hA with ⟨hA_mem, h_nd⟩
    rcases Finset.not_disjoint_iff.mp h_nd with ⟨y, hyA, hyu⟩
    let xA := anchorOfCube q A
    have hA_eq : boxCube xA q = A := boxCube_anchorOfCube hA_mem
    rw [← hA_eq, mem_boxCube] at hyA
    rw [mem_boxCube] at hyu
    have hk_lt : ∀ i : Fin D, (u i).val + r_c - 1 - (xA i).val < M := by
      intro i; have := hyA i; have := hyu i; dsimp [M]; omega
    let k : Fin D → Fin M := fun i => ⟨(u i).val + r_c - 1 - (xA i).val, hk_lt i⟩
    have h_anchor : (fun i : Fin D => (⟨min (L - 1) ((u i).val + r_c - 1 - (k i).val),
        Nat.lt_of_le_of_lt (Nat.min_le_left _ _) (Nat.sub_lt hL_pos zero_lt_one)⟩ : Fin L)) = xA := by
      funext i; apply Fin.ext
      have := hyA i; have := hyu i; have := (xA i).isLt
      change min (L - 1) ((u i).val + r_c - 1 - ((u i).val + r_c - 1 - (xA i).val)) = (xA i).val
      omega
    rw [Finset.mem_image]
    refine ⟨k, Finset.mem_univ k, ?_⟩
    dsimp [g]; rw [h_anchor, hA_eq]
  calc ((boxCubes D L q).filter (fun A => ¬ Disjoint A (boxCube u r_c))).card
    _ ≤ (Finset.univ.image g).card := Finset.card_le_card h_sub
    _ ≤ (Finset.univ : Finset (Fin D → Fin M)).card := Finset.card_image_le
    _ = M ^ D := by rw [Finset.card_univ, Fintype.card_fun, Fintype.card_fin, Fintype.card_fin]

/-- $L$-independent upper bound on `uniformCubeCommutatorFactor D L r_c f` for any
    `IsSuperpolynomialDecay f`. -/
theorem uniformCubeCommutatorFactor_le_tsum {D L r_c : ℕ} [NeZero D] [NeZero L]
    {f : ℕ → ℝ} (hf : IsSuperpolynomialDecay f) :
    uniformCubeCommutatorFactor D L r_c f ≤
      ((r_c + 1 : ℝ) ^ D) * ∑' q : ℕ, (q : ℝ) ^ D * f q := by
  dsimp [uniformCubeCommutatorFactor]
  have h_sum_each : ∀ q ∈ Finset.Icc 1 L,
      ((Finset.univ.sup (fun u : BoxD D L =>
        ((boxCubes D L q).filter (fun A => ¬ Disjoint A (boxCube u r_c))).card) : ℕ) : ℝ) * f q ≤
      ((r_c + 1 : ℝ) ^ D) * ((q : ℝ) ^ D * f q) := by
    intro q hq
    have hq1 : 1 ≤ q := (Finset.mem_Icc.mp hq).1
    have h_sup : Finset.univ.sup (fun u : BoxD D L =>
        ((boxCubes D L q).filter (fun A => ¬ Disjoint A (boxCube u r_c))).card) ≤ (q + r_c) ^ D :=
      Finset.sup_le fun u _ => card_filter_not_disjoint_boxCube_le_pow u q r_c
    have h_qr : q + r_c ≤ (r_c + 1) * q := by nlinarith
    have h_pow : (q + r_c) ^ D ≤ ((r_c + 1) * q) ^ D := Nat.pow_le_pow_left h_qr D
    have h_cast : ((Finset.univ.sup (fun u : BoxD D L =>
        ((boxCubes D L q).filter (fun A => ¬ Disjoint A (boxCube u r_c))).card) : ℕ) : ℝ) ≤
        ((r_c + 1 : ℝ) ^ D) * (q : ℝ) ^ D := by
      have h_le : Finset.univ.sup (fun u : BoxD D L =>
          ((boxCubes D L q).filter (fun A => ¬ Disjoint A (boxCube u r_c))).card) ≤
          (r_c + 1) ^ D * q ^ D := by
        rw [← Nat.mul_pow]; exact le_trans h_sup h_pow
      exact_mod_cast h_le
    calc ((Finset.univ.sup (fun u : BoxD D L =>
          ((boxCubes D L q).filter (fun A => ¬ Disjoint A (boxCube u r_c))).card) : ℕ) : ℝ) * f q
      _ ≤ (((r_c + 1 : ℝ) ^ D) * (q : ℝ) ^ D) * f q :=
        mul_le_mul_of_nonneg_right h_cast (hf.1 q)
      _ = ((r_c + 1 : ℝ) ^ D) * ((q : ℝ) ^ D * f q) := by ring
  calc ∑ q ∈ Finset.Icc 1 L,
        ((Finset.univ.sup (fun u : BoxD D L =>
          ((boxCubes D L q).filter (fun A => ¬ Disjoint A (boxCube u r_c))).card) : ℕ) : ℝ) * f q
    _ ≤ ∑ q ∈ Finset.Icc 1 L, ((r_c + 1 : ℝ) ^ D) * ((q : ℝ) ^ D * f q) :=
      Finset.sum_le_sum h_sum_each
    _ = ((r_c + 1 : ℝ) ^ D) * ∑ q ∈ Finset.Icc 1 L, (q : ℝ) ^ D * f q := by
      rw [← Finset.mul_sum]
    _ ≤ ((r_c + 1 : ℝ) ^ D) * ∑' q : ℕ, (q : ℝ) ^ D * f q := by
      refine mul_le_mul_of_nonneg_left ?_ (by positivity)
      exact (summable_pow_mul_of_isSuperpolynomialDecay hf D).sum_le_tsum (Finset.Icc 1 L)
        (fun q _ => mul_nonneg (by positivity) (hf.1 q))

lemma uniformCubeCommutatorFactor_two_mul {D L r_c : ℕ} (f : ℕ → ℝ) :
    uniformCubeCommutatorFactor D L r_c (fun r => 2 * f r) =
      2 * uniformCubeCommutatorFactor D L r_c f := by
  dsimp [uniformCubeCommutatorFactor]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun q _ => by ring

/-! ## 3. Check-Weight Sum and Zero-Mode Base Norm Bounds -/

/-- Anchor site of a `StaticCSSCheckIdx L q_code m_max`. -/
def staticCSSCheckSite {L q_code m_max : ℕ} : StaticCSSCheckIdx L q_code m_max → Box3D L
  | Sum.inl (v, _) => v
  | Sum.inr (Sum.inl (v, _)) => v
  | Sum.inr (Sum.inr (v, _)) => v

/-- Local check-slot tag of a `StaticCSSCheckIdx L q_code m_max`. -/
def staticCSSCheckSlot {L q_code m_max : ℕ} :
    StaticCSSCheckIdx L q_code m_max → Fin q_code ⊕ Fin m_max ⊕ Fin m_max
  | Sum.inl (_, a) => Sum.inl a
  | Sum.inr (Sum.inl (_, b)) => Sum.inr (Sum.inl b)
  | Sum.inr (Sum.inr (_, c)) => Sum.inr (Sum.inr c)

/-- Reconstructs a `StaticCSSCheckIdx L q_code m_max` from its site and slot tag. -/
def mkStaticCSSCheckIdx {L q_code m_max : ℕ} :
    Box3D L × (Fin q_code ⊕ Fin m_max ⊕ Fin m_max) → StaticCSSCheckIdx L q_code m_max
  | (v, Sum.inl a) => Sum.inl (v, a)
  | (v, Sum.inr (Sum.inl b)) => Sum.inr (Sum.inl (v, b))
  | (v, Sum.inr (Sum.inr c)) => Sum.inr (Sum.inr (v, c))

lemma mkStaticCSSCheckIdx_site_slot {L q_code m_max : ℕ} (idx : StaticCSSCheckIdx L q_code m_max) :
    mkStaticCSSCheckIdx (staticCSSCheckSite idx, staticCSSCheckSlot idx) = idx := by
  rcases idx with ⟨v, a⟩ | ⟨v, b⟩ | ⟨v, c⟩ <;> rfl

lemma staticCSSCheckSite_mem_and_subset_boxBall {L q_code r_0 m_max : ℕ}
    (D_field : Box3D L → LocalCSSDescriptor q_code r_0 m_max)
    (idx : StaticCSSCheckIdx L q_code m_max) :
    staticCSSCheckSite idx ∈ staticCSSCheckSupport D_field idx ∧
    staticCSSCheckSupport D_field idx ⊆ boxBall (staticCSSCheckSite idx) r_0 := by
  rcases idx with ⟨v, a⟩ | ⟨v, b⟩ | ⟨v, c⟩
  · exact ⟨Finset.mem_singleton_self v,
      Finset.singleton_subset_iff.mpr (mem_boxBall_self v r_0)⟩
  · exact ⟨mem_boxBall_self v r_0, Finset.Subset.refl _⟩
  · exact ⟨mem_boxBall_self v r_0, Finset.Subset.refl _⟩

lemma anchorOfRegion_mem_of_nonempty {D L : ℕ} [NeZero L] {A : Finset (BoxD D L)}
    (hA : A.Nonempty) : anchorOfRegion A ∈ A := by
  dsimp [anchorOfRegion]
  rw [dif_pos hA]
  exact hA.choose_spec

/-- $L$-independent upper bound on the check-weight sum at any anchor site `u` for BDL inhomogeneous
    systems: `bdlInhomogeneousSiteWeightBound := ((2 * r_0_BDL + 1) ^ 3 * (q_code_BDL + 2 * m_max_BDL) : ℝ)`. -/
def bdlInhomogeneousSiteWeightBound : ℝ :=
  (((2 * r0BDL + 1) ^ 3 * (qCodeBDL + 2 * mMaxBDL) : ℕ) : ℝ)

lemma bdlInhomogeneousSiteWeightBound_nonneg : 0 ≤ bdlInhomogeneousSiteWeightBound := by
  dsimp [bdlInhomogeneousSiteWeightBound]; positivity

/-- For any `Inhomogeneous3DMemoryRealization`, the total weight of checks anchored at `u` via
    `anchorOfRegion` is bounded by `bdlInhomogeneousSiteWeightBound` (independent of $L$ and $k$). -/
theorem sum_weight_anchorOfRegion_inhomogeneous_le {L : ℕ} [NeZero L]
    {c_star C β_c c_F η c_mem : ℝ}
    (mem : Inhomogeneous3DMemoryRealization L qCodeBDL r0BDL mMaxBDL c_star C β_c c_F η c_mem)
    (u : Box3D L) :
    (∑ i ∈ Finset.univ.filter (fun i : StaticCSSCheckIdx L qCodeBDL mMaxBDL =>
        anchorOfRegion (mem.sys.support i) = u),
      mem.sys.weight i) ≤ bdlInhomogeneousSiteWeightBound := by
  haveI : NeZero 3 := ⟨by decide⟩
  let S_u := Finset.univ.filter (fun i : StaticCSSCheckIdx L qCodeBDL mMaxBDL =>
    anchorOfRegion (mem.sys.support i) = u)
  let P_ball : Finset (Box3D L × (Fin qCodeBDL ⊕ Fin mMaxBDL ⊕ Fin mMaxBDL)) :=
    (boxBall u r0BDL) ×ˢ Finset.univ
  have h_sub : S_u ⊆ P_ball.image mkStaticCSSCheckIdx := by
    intro idx hidx
    have h_anc : anchorOfRegion (mem.sys.support idx) = u := (Finset.mem_filter.mp hidx).2
    have h_supp_eq : mem.sys.support idx = staticCSSCheckSupport mem.D_field idx :=
      (mem.h_sys_checks idx).2.1
    rcases staticCSSCheckSite_mem_and_subset_boxBall mem.D_field idx with ⟨h_mem, h_sub_ball⟩
    have h_ne : (mem.sys.support idx).Nonempty := ⟨staticCSSCheckSite idx, h_supp_eq ▸ h_mem⟩
    have hu_mem : u ∈ boxBall (staticCSSCheckSite idx) r0BDL := by
      rw [← h_anc]
      exact h_sub_ball (h_supp_eq ▸ anchorOfRegion_mem_of_nonempty h_ne)
    have h_site_mem : staticCSSCheckSite idx ∈ boxBall u r0BDL := by
      simp only [boxBall, Finset.mem_filter, Finset.mem_univ, true_and] at hu_mem ⊢
      rwa [boxDist_comm]
    rw [Finset.mem_image]
    refine ⟨(staticCSSCheckSite idx, staticCSSCheckSlot idx), ?_, mkStaticCSSCheckIdx_site_slot idx⟩
    exact Finset.mem_product.mpr ⟨h_site_mem, Finset.mem_univ _⟩
  have h_card : S_u.card ≤ (2 * r0BDL + 1) ^ 3 * (qCodeBDL + 2 * mMaxBDL) := by
    calc S_u.card
      _ ≤ (P_ball.image mkStaticCSSCheckIdx).card := Finset.card_le_card h_sub
      _ ≤ P_ball.card := Finset.card_image_le
      _ = (boxBall u r0BDL).card *
          (Finset.univ : Finset (Fin qCodeBDL ⊕ Fin mMaxBDL ⊕ Fin mMaxBDL)).card :=
        Finset.card_product _ _
      _ ≤ (2 * r0BDL + 1) ^ 3 * (qCodeBDL + 2 * mMaxBDL) := by
        have h1 := card_boxBall_le_pow u r0BDL
        have h2 : (Finset.univ : Finset (Fin qCodeBDL ⊕ Fin mMaxBDL ⊕ Fin mMaxBDL)).card =
            qCodeBDL + 2 * mMaxBDL := by
          rw [Finset.card_univ, Fintype.card_sum, Fintype.card_sum, Fintype.card_fin, Fintype.card_fin]
          omega
        rw [h2]
        exact Nat.mul_le_mul_right _ h1
  have h_sum_eq : (∑ i ∈ S_u, mem.sys.weight i) = (S_u.card : ℝ) := by
    calc ∑ i ∈ S_u, mem.sys.weight i
      _ = ∑ _i ∈ S_u, (1 : ℝ) := Finset.sum_congr rfl fun i _ => (mem.h_sys_checks i).2.2
      _ = (S_u.card : ℝ) := by rw [Finset.sum_const, nsmul_eq_mul, mul_one]
  rw [h_sum_eq]
  dsimp [bdlInhomogeneousSiteWeightBound]
  exact_mod_cast h_card

/-- $L$-independent upper bound on `uniformCubeCommutatorFactor 3 L (2 * r_0_BDL + 1) f`. -/
def bdlInhomogeneousCommutatorBound (f : ℕ → ℝ) : ℝ :=
  (((2 * r0BDL + 1 : ℕ) : ℝ) + 1) ^ 3 * ∑' q : ℕ, (q : ℝ) ^ 3 * f q

/-- Explicit $L$-independent zero-mode base norm `m_0` parameterized by both
    the perturbation decay profile `f` and the QAC generator decay profile `f_D`. -/
def bdlInhomogeneousBaseNormM0WithGenDecay (f f_D : ℕ → ℝ) : ℝ :=
  4 * ((∑' q : ℕ, (q : ℝ) ^ 3 * f q) +
    Real.pi * (2 * bdlInhomogeneousSiteWeightBound * bdlInhomogeneousCommutatorBound f) +
    2 * bdlInhomogeneousSiteWeightBound * bdlInhomogeneousCommutatorBound f_D)

lemma bdlInhomogeneousBaseNormM0_of_f_D_nonneg {f f_D : ℕ → ℝ}
    (hf : IsSuperpolynomialDecay f) (hf_D : IsSuperpolynomialDecay f_D) :
    0 ≤ bdlInhomogeneousBaseNormM0WithGenDecay f f_D := by
  have h_tsum_f : 0 ≤ ∑' q : ℕ, (q : ℝ) ^ 3 * f q :=
    tsum_nonneg fun q => mul_nonneg (by positivity) (hf.1 q)
  have h_tsum_fD : 0 ≤ ∑' q : ℕ, (q : ℝ) ^ 3 * f_D q :=
    tsum_nonneg fun q => mul_nonneg (by positivity) (hf_D.1 q)
  have h_comm_f : 0 ≤ bdlInhomogeneousCommutatorBound f := mul_nonneg (by positivity) h_tsum_f
  have h_comm_fD : 0 ≤ bdlInhomogeneousCommutatorBound f_D := mul_nonneg (by positivity) h_tsum_fD
  have h_w_nn := bdlInhomogeneousSiteWeightBound_nonneg
  have h_pi_nn : 0 ≤ Real.pi := Real.pi_pos.le
  dsimp [bdlInhomogeneousBaseNormM0WithGenDecay]
  positivity

lemma bdlInhomogeneousBaseNormM0_of_f_D_ge {L : ℕ} [NeZero L] {f f_D : ℕ → ℝ}
    (hf : IsSuperpolynomialDecay f) (hf_D : IsSuperpolynomialDecay f_D) :
    4 * ((∑ q ∈ Finset.Icc 1 L, f q) +
      Real.pi * (2 * bdlInhomogeneousSiteWeightBound *
        uniformCubeCommutatorFactor 3 L (2 * r0BDL + 1) f) +
      2 * bdlInhomogeneousSiteWeightBound *
        uniformCubeCommutatorFactor 3 L (2 * r0BDL + 1) f_D) ≤
      bdlInhomogeneousBaseNormM0WithGenDecay f f_D := by
  haveI : NeZero 3 := ⟨by decide⟩
  have h_sum_f : ∑ q ∈ Finset.Icc 1 L, f q ≤ ∑' q : ℕ, (q : ℝ) ^ 3 * f q := by
    calc ∑ q ∈ Finset.Icc 1 L, f q
      _ ≤ ∑ q ∈ Finset.Icc 1 L, (q : ℝ) ^ 3 * f q := by
        refine Finset.sum_le_sum fun q hq => ?_
        have hq1 : (1 : ℝ) ≤ (q : ℝ) := by exact_mod_cast (Finset.mem_Icc.mp hq).1
        have hq3 : (1 : ℝ) ≤ (q : ℝ) ^ 3 := one_le_pow₀ hq1
        calc f q = 1 * f q := (one_mul _).symm
          _ ≤ (q : ℝ) ^ 3 * f q := mul_le_mul_of_nonneg_right hq3 (hf.1 q)
      _ ≤ ∑' q : ℕ, (q : ℝ) ^ 3 * f q :=
        (summable_pow_mul_of_isSuperpolynomialDecay hf 3).sum_le_tsum (Finset.Icc 1 L)
          (fun q _ => mul_nonneg (by positivity) (hf.1 q))
  have h_uc_f : uniformCubeCommutatorFactor 3 L (2 * r0BDL + 1) f ≤
      bdlInhomogeneousCommutatorBound f :=
    uniformCubeCommutatorFactor_le_tsum (D := 3) (L := L) (r_c := 2 * r0BDL + 1) hf
  have h_uc_fD : uniformCubeCommutatorFactor 3 L (2 * r0BDL + 1) f_D ≤
      bdlInhomogeneousCommutatorBound f_D :=
    uniformCubeCommutatorFactor_le_tsum (D := 3) (L := L) (r_c := 2 * r0BDL + 1) hf_D
  have h_w_nn := bdlInhomogeneousSiteWeightBound_nonneg
  have h_pi_nn : 0 ≤ Real.pi := Real.pi_pos.le
  have h_pi_term : Real.pi * (2 * bdlInhomogeneousSiteWeightBound *
        uniformCubeCommutatorFactor 3 L (2 * r0BDL + 1) f) ≤
      Real.pi * (2 * bdlInhomogeneousSiteWeightBound * bdlInhomogeneousCommutatorBound f) := by
    refine mul_le_mul_of_nonneg_left ?_ h_pi_nn
    exact mul_le_mul_of_nonneg_left h_uc_f (by positivity)
  have h_u_term : 2 * bdlInhomogeneousSiteWeightBound *
        uniformCubeCommutatorFactor 3 L (2 * r0BDL + 1) f_D ≤
      2 * bdlInhomogeneousSiteWeightBound * bdlInhomogeneousCommutatorBound f_D :=
    mul_le_mul_of_nonneg_left h_uc_fD (by positivity)
  dsimp [bdlInhomogeneousBaseNormM0WithGenDecay]
  linarith

/-- Explicit $L$-independent zero-mode base norm `m_0` when `f_D = fun r => 2 * f r`. -/
def bdlInhomogeneousBaseNormM0 (f : ℕ → ℝ) : ℝ :=
  bdlInhomogeneousBaseNormM0WithGenDecay f (fun r => 2 * f r)

lemma bdlInhomogeneousBaseNormM0_nonneg {f : ℕ → ℝ} (hf : IsSuperpolynomialDecay f) :
    0 ≤ bdlInhomogeneousBaseNormM0 f :=
  bdlInhomogeneousBaseNormM0_of_f_D_nonneg hf (isSuperpolynomialDecay_const_mul hf zero_le_two)

lemma bdlInhomogeneousBaseNormM0_ge {L : ℕ} [NeZero L] {f : ℕ → ℝ}
    (hf : IsSuperpolynomialDecay f) :
    4 * ((∑ q ∈ Finset.Icc 1 L, f q) +
      Real.pi * (2 * bdlInhomogeneousSiteWeightBound *
        uniformCubeCommutatorFactor 3 L (2 * r0BDL + 1) f) +
      2 * bdlInhomogeneousSiteWeightBound *
        uniformCubeCommutatorFactor 3 L (2 * r0BDL + 1) (fun r => 2 * f r)) ≤
      bdlInhomogeneousBaseNormM0 f :=
  bdlInhomogeneousBaseNormM0_of_f_D_ge hf (isSuperpolynomialDecay_const_mul hf zero_le_two)

/-- **Site Check Operator Duhamel Drift Bound Along Any `IsKatoHastingsFlowSystem`**:
    For any `mem : Inhomogeneous3DMemoryRealization` and any Kato–Hastings QAC flow
    `IsKatoHastingsFlowSystem mem.sys.P0 (fun τ => (D_loc τ).V_tot) U_flow P_flow` whose generator
    satisfies `(D_loc τ).SatisfiesDecayBound J f_D` for `τ ∈ Set.Icc 0 s`:
    `‖(U_flow s)† * anchoredSiteCheckOp anchorOfRegion mem.sys u * U_flow s - anchoredSiteCheckOp anchorOfRegion mem.sys u‖ ≤ J * (2 * bdlInhomogeneousSiteWeightBound * uniformCubeCommutatorFactor 3 L (2 * r_0_BDL + 1) f_D)`. -/
theorem norm_siteCheckOp_drift_inhomogeneous_le_of_katoHastingsFlow {L : ℕ} [NeZero L]
    {c_star C β_c c_F η c_mem : ℝ}
    (mem : Inhomogeneous3DMemoryRealization L qCodeBDL r0BDL mMaxBDL c_star C β_c c_F η c_mem)
    (D_loc : ℝ → QuasiLocalPerturbation 3 L (UniformSite3D L (CodeSlotConfig qCodeBDL)))
    (U_flow P_flow : ℝ → (ManyBodyHilbertSpace (UniformSite3D L (CodeSlotConfig qCodeBDL)) →L[ℂ]
      ManyBodyHilbertSpace (UniformSite3D L (CodeSlotConfig qCodeBDL))))
    (hFlow : IsKatoHastingsFlowSystem mem.sys.P0 (fun τ => (D_loc τ).totalPerturbation) U_flow P_flow)
    {J s : ℝ} {f_D : ℕ → ℝ}
    (hJ_nn : 0 ≤ J) (hs : s ∈ Set.Icc 0 1) (hf_D_nn : ∀ r : ℕ, 0 ≤ f_D r)
    (hD_dec : ∀ τ ∈ Set.Icc 0 s, (D_loc τ).SatisfiesDecayBound J f_D)
    (u : Box3D L) :
    ‖(U_flow s)† * anchoredSiteCheckOp anchorOfRegion mem.sys u * U_flow s -
      anchoredSiteCheckOp anchorOfRegion mem.sys u‖ ≤
      J * (2 * bdlInhomogeneousSiteWeightBound *
        uniformCubeCommutatorFactor 3 L (2 * r0BDL + 1) f_D) := by
  have h_ball_cov : ∀ idx : StaticCSSCheckIdx L qCodeBDL mMaxBDL,
      ∃ v0 : Box3D L, mem.sys.support idx ⊆ boxBall v0 r0BDL := fun idx =>
    ⟨staticCSSCheckSite idx,
      (mem.h_sys_checks idx).2.1 ▸ (staticCSSCheckSite_mem_and_subset_boxBall mem.D_field idx).2⟩
  exact (norm_qacUnitaryFlow_siteCheckOp_drift_le_of_ball_cover anchorOfRegion mem.sys h_ball_cov
    D_loc U_flow P_flow hFlow hs hJ_nn hf_D_nn hD_dec u
    (sum_weight_anchorOfRegion_inhomogeneous_le mem u)).2

end
