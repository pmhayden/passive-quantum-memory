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

import Proofs.HastingsKomaLightCone.FrustrationFreeGroundAnnihilation

open scoped Classical InnerProduct ComplexConjugate BigOperators
open Filter Topology Asymptotics ContinuousLinearMap KMSPinchedGibbs PerturbedThermalBarrier
open WeldedHierarchy WeldedHierarchy.BDLDecoder InhomogeneousMemoryChallenge

noncomputable section

set_option maxRecDepth 200000
set_option maxHeartbeats 800000

/-!
# Lattice Ball Geometry and System-Size-Independent Interaction Moments

Establishes open-box ball and cube diameter inequalities, localized support of `siteCheckOp`, and system-size-independent Hastings–Koma `s1` interaction bounds for quasi-local perturbations (`perturbationLatticeHamiltonian`, `quasiLocalS1Factor`) and finite-range commuting checks (`bdlInhomogeneousUnperturbedS1Bound`).

## References

* Part I, Section 6.1 (`subsec:dsuper-banach`), Definition 6.1 (`def:banach-quasilocal`)
* Part I, Section 6.2 (`subsec:bochner-lr`), Equation (70) (`eq:hastings-koma-lr`)
* Hastings–Koma (2006), Communications in Mathematical Physics 265, 781–804
-/

/-! ## 1. Region Diameter, `boxBall` Distance Bounds & Unconditional `siteCheckOp` Support -/

/-- Monotonicity of `regionDiam` under subset inclusion $A \subseteq B$. -/
lemma regionDiam_mono {D L : ℕ} {A B : Finset (BoxD D L)} (hAB : A ⊆ B) :
    regionDiam A ≤ regionDiam B := by
  unfold regionDiam
  exact Finset.sup_mono (Finset.product_subset_product hAB hAB)

/-- Every open-box cube `boxCube x0 r` has $\ell_\infty$ diameter at most `r`. -/
lemma regionDiam_boxCube_le {D L : ℕ} (x0 : BoxD D L) (r : ℕ) :
    regionDiam (boxCube x0 r) ≤ r := by
  unfold regionDiam
  refine Finset.sup_le fun p hp => ?_
  rcases Finset.mem_product.mp hp with ⟨h1, h2⟩
  simp only [boxCube, Finset.mem_filter, Finset.mem_univ, true_and] at h1 h2
  dsimp [boxDist]
  refine Finset.sup_le fun i _ => ?_
  have hi1 := h1 i
  have hi2 := h2 i
  dsimp [coordDist]
  omega

/-- Every $\ell_\infty$-ball `boxBall v r` has $\ell_\infty$ diameter at most `2 * r + 1`. -/
lemma regionDiam_boxBall_le {D L : ℕ} (v : BoxD D L) (r : ℕ) :
    regionDiam (boxBall v r) ≤ 2 * r + 1 :=
  le_trans (regionDiam_mono (boxBall_subset_boxCube v r)) (regionDiam_boxCube_le _ (2 * r + 1))

/-- For concentric $\ell_\infty$-balls `boxBall u r_1` and `boxBall u r_2` with $r_1 \le r_2$,
    whenever `Finset.univ \ boxBall u r_2` is nonempty:
    `r_2 + 1 - r_1 ≤ regionDist (boxBall u r_1) (Finset.univ \ boxBall u r_2)`. -/
theorem regionDist_boxBall_compl_boxBall_ge {D L : ℕ}
    (u : BoxD D L) {r_1 r_2 : ℕ} (_hr : r_1 ≤ r_2)
    (h_ne : (Finset.univ \ boxBall u r_2).Nonempty) :
    r_2 + 1 - r_1 ≤ regionDist (boxBall u r_1) (Finset.univ \ boxBall u r_2) := by
  have h1_ne : (boxBall u r_1).Nonempty := ⟨u, mem_boxBall_self u r_1⟩
  rw [regionDist, dif_pos ⟨h1_ne, h_ne⟩]
  apply Finset.le_inf'
  intro p hp
  rcases Finset.mem_product.mp hp with ⟨hx, hy⟩
  have hy_not : p.2 ∉ boxBall u r_2 := (Finset.mem_sdiff.mp hy).2
  simp only [boxBall, Finset.mem_filter, Finset.mem_univ, true_and, not_le] at hx hy_not
  have h_tri := boxDist_triangle u p.1 p.2
  omega

/-- For `boxCube u q` with $1 \le q \le r_1$ and `boxBall u r_2` with $r_1 \le r_2$,
    whenever `Finset.univ \ boxBall u r_2` is nonempty:
    `r_2 + 1 - r_1 ≤ regionDist (boxCube u q) (Finset.univ \ boxBall u r_2)`. -/
theorem regionDist_boxCube_compl_boxBall_ge {D L : ℕ}
    (u : BoxD D L) {q r_1 r_2 : ℕ} (hq1 : 1 ≤ q) (hqr : q ≤ r_1) (_hr : r_1 ≤ r_2)
    (h_ne : (Finset.univ \ boxBall u r_2).Nonempty) :
    r_2 + 1 - r_1 ≤ regionDist (boxCube u q) (Finset.univ \ boxBall u r_2) := by
  have hq_ne : (boxCube u q).Nonempty :=
    ⟨u, singleton_subset_boxCube u hq1 (Finset.mem_singleton_self u)⟩
  rw [regionDist, dif_pos ⟨hq_ne, h_ne⟩]
  apply Finset.le_inf'
  intro p hp
  rcases Finset.mem_product.mp hp with ⟨hx, hy⟩
  have hx_ball : p.1 ∈ boxBall u r_1 :=
    boxBall_mono u hqr (boxCube_subset_boxBall u q hx)
  have hy_not : p.2 ∉ boxBall u r_2 := (Finset.mem_sdiff.mp hy).2
  simp only [boxBall, Finset.mem_filter, Finset.mem_univ, true_and, not_le] at hx_ball hy_not
  have h_tri := boxDist_triangle u p.1 p.2
  omega

/-- Every check `idx` of `mem : Inhomogeneous3DMemoryRealization` containing a site `u ∈ mem.sys.support idx`
    has `mem.sys.support idx ⊆ boxBall u (2 * r_0_BDL)`. -/
theorem support_subset_boxBall_two_mul_of_mem_inhomogeneous {L : ℕ} [NeZero L]
    {c_star C β_c c_F η c_mem : ℝ}
    (mem : Inhomogeneous3DMemoryRealization L qCodeBDL r0BDL mMaxBDL c_star C β_c c_F η c_mem)
    {idx : StaticCSSCheckIdx L qCodeBDL mMaxBDL} {u : Box3D L}
    (hu : u ∈ mem.sys.support idx) :
    mem.sys.support idx ⊆ boxBall u (2 * r0BDL) := by
  have h_supp_eq : mem.sys.support idx = staticCSSCheckSupport mem.D_field idx :=
    (mem.h_sys_checks idx).2.1
  rcases staticCSSCheckSite_mem_and_subset_boxBall mem.D_field idx with ⟨_h_mem, h_sub_ball⟩
  have hu_ball : u ∈ boxBall (staticCSSCheckSite idx) r0BDL :=
    h_sub_ball (h_supp_eq ▸ hu)
  intro x hx
  have hx_ball : x ∈ boxBall (staticCSSCheckSite idx) r0BDL :=
    h_sub_ball (h_supp_eq ▸ hx)
  simp only [boxBall, Finset.mem_filter, Finset.mem_univ, true_and] at hu_ball hx_ball ⊢
  have h_tri := boxDist_triangle u (staticCSSCheckSite idx) x
  rw [boxDist_comm u (staticCSSCheckSite idx)] at h_tri
  omega

/-- **Unconditional Symmetric `boxBall` Support of `mem.sys.siteCheckOp u`
    (`isSupportedOn_boxBall_siteCheckOp_inhomogeneous`)**:
    For every `mem : Inhomogeneous3DMemoryRealization` and every `u : Box3D L`,
    `mem.sys.siteCheckOp u` is supported on `boxBall u (2 * r_0_BDL)` (and on `boxBall u r`
    for all `2 * r_0_BDL ≤ r`). -/
theorem isSupportedOn_boxBall_siteCheckOp_inhomogeneous {L : ℕ} [NeZero L]
    {c_star C β_c c_F η c_mem : ℝ}
    (mem : Inhomogeneous3DMemoryRealization L qCodeBDL r0BDL mMaxBDL c_star C β_c c_F η c_mem)
    (u : Box3D L) {r : ℕ} (hr : 2 * r0BDL ≤ r) :
    IsSupportedOn (UniformSite3D L (CodeSlotConfig qCodeBDL))
      (boxBall u r) (mem.sys.siteCheckOp u) := by
  rw [siteCheckOp_eq_anchoredSiteCheckOp]
  dsimp [anchoredSiteCheckOp]
  refine isSupportedOn_finset_sum (boxBall u r) _ _ fun idx hidx => ?_
  have h_anc : anchorOfRegion (mem.sys.support idx) = u := (Finset.mem_filter.mp hidx).2
  have h_supp_eq : mem.sys.support idx = staticCSSCheckSupport mem.D_field idx :=
    (mem.h_sys_checks idx).2.1
  rcases staticCSSCheckSite_mem_and_subset_boxBall mem.D_field idx with ⟨h_mem, _⟩
  have h_ne : (mem.sys.support idx).Nonempty := ⟨staticCSSCheckSite idx, h_supp_eq ▸ h_mem⟩
  have hu_mem : u ∈ mem.sys.support idx := h_anc ▸ anchorOfRegion_mem_of_nonempty h_ne
  have h_sub : mem.sys.support idx ⊆ boxBall u r :=
    Finset.Subset.trans (support_subset_boxBall_two_mul_of_mem_inhomogeneous mem hu_mem)
      (boxBall_mono u hr)
  exact isSupportedOn_smul (boxBall u r) (mem.sys.weight idx : ℂ)
    (_root_.isSupportedOn_mono h_sub (mem.sys.is_supported idx))

/-- For any `Inhomogeneous3DMemoryRealization` and any site `x : Box3D L`, the sum of weights of
    all checks `i` whose support contains `x` is bounded by `bdlInhomogeneousSiteWeightBound`. -/
theorem sum_weight_mem_support_inhomogeneous_le {L : ℕ} [NeZero L]
    {c_star C β_c c_F η c_mem : ℝ}
    (mem : Inhomogeneous3DMemoryRealization L qCodeBDL r0BDL mMaxBDL c_star C β_c c_F η c_mem)
    (x : Box3D L) :
    (∑ i ∈ Finset.univ.filter (fun i : StaticCSSCheckIdx L qCodeBDL mMaxBDL =>
        x ∈ mem.sys.support i),
      mem.sys.weight i) ≤ bdlInhomogeneousSiteWeightBound := by
  haveI : NeZero 3 := ⟨by decide⟩
  let S_x := Finset.univ.filter (fun i : StaticCSSCheckIdx L qCodeBDL mMaxBDL =>
    x ∈ mem.sys.support i)
  let P_ball : Finset (Box3D L × (Fin qCodeBDL ⊕ Fin mMaxBDL ⊕ Fin mMaxBDL)) :=
    (boxBall x r0BDL) ×ˢ Finset.univ
  have h_sub : S_x ⊆ P_ball.image mkStaticCSSCheckIdx := by
    intro idx hidx
    have hx_mem : x ∈ mem.sys.support idx := (Finset.mem_filter.mp hidx).2
    have h_supp_eq : mem.sys.support idx = staticCSSCheckSupport mem.D_field idx :=
      (mem.h_sys_checks idx).2.1
    rcases staticCSSCheckSite_mem_and_subset_boxBall mem.D_field idx with ⟨_, h_sub_ball⟩
    have hx_ball : x ∈ boxBall (staticCSSCheckSite idx) r0BDL :=
      h_sub_ball (h_supp_eq ▸ hx_mem)
    have h_site_mem : staticCSSCheckSite idx ∈ boxBall x r0BDL :=
      (mem_boxBall_comm (staticCSSCheckSite idx) x r0BDL).mp hx_ball
    rw [Finset.mem_image]
    refine ⟨(staticCSSCheckSite idx, staticCSSCheckSlot idx), ?_, mkStaticCSSCheckIdx_site_slot idx⟩
    exact Finset.mem_product.mpr ⟨h_site_mem, Finset.mem_univ _⟩
  have h_card : S_x.card ≤ (2 * r0BDL + 1) ^ 3 * (qCodeBDL + 2 * mMaxBDL) := by
    calc S_x.card
      _ ≤ (P_ball.image mkStaticCSSCheckIdx).card := Finset.card_le_card h_sub
      _ ≤ P_ball.card := Finset.card_image_le
      _ = (boxBall x r0BDL).card *
          (Finset.univ : Finset (Fin qCodeBDL ⊕ Fin mMaxBDL ⊕ Fin mMaxBDL)).card :=
        Finset.card_product _ _
      _ ≤ (2 * r0BDL + 1) ^ 3 * (qCodeBDL + 2 * mMaxBDL) := by
        have h1 := card_boxBall_le_pow x r0BDL
        have h2 : (Finset.univ : Finset (Fin qCodeBDL ⊕ Fin mMaxBDL ⊕ Fin mMaxBDL)).card =
            qCodeBDL + 2 * mMaxBDL := by
          rw [Finset.card_univ, Fintype.card_sum, Fintype.card_sum, Fintype.card_fin, Fintype.card_fin]
          omega
        rw [h2]
        exact Nat.mul_le_mul_right _ h1
  have h_sum_eq : (∑ i ∈ S_x, mem.sys.weight i) = (S_x.card : ℝ) := by
    calc ∑ i ∈ S_x, mem.sys.weight i
      _ = ∑ _i ∈ S_x, (1 : ℝ) := Finset.sum_congr rfl fun i _ => (mem.h_sys_checks i).2.2
      _ = (S_x.card : ℝ) := by rw [Finset.sum_const, nsmul_eq_mul, mul_one]
  rw [h_sum_eq]
  dsimp [bdlInhomogeneousSiteWeightBound]
  exact_mod_cast h_card

/-! ## 2. `perturbationLatticeHamiltonian` and $L$-Independent `LatticeHamiltonian.s1` Bounds -/

/-- Packages $(s : \mathbb{C}) \bullet V.V_{\mathrm{tot}}$ as a `LatticeHamiltonian D L Site`. -/
def perturbationLatticeHamiltonian {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    (V : QuasiLocalPerturbation D L Site) (s : ℝ) :
    LatticeHamiltonian D L Site where
  h Z := perturbationLatticeTerm V s Z
  is_selfAdjoint Z := by
    refine isSelfAdjoint_finset_sum _ _ fun r _ => ?_
    split_ifs
    · exact isSelfAdjoint_real_smul s (V.is_selfAdjoint r Z)
    · exact IsSelfAdjoint.zero _
  is_supported Z := by
    refine isSupportedOn_finset_sum Z _ _ fun r hr => ?_
    split_ifs with hZ
    · exact isSupportedOn_smul Z (s : ℂ) (V.is_supported r hr Z hZ)
    · exact _root_.isSupportedOn_zero Z

/-- Global Hamiltonian identity `(perturbationLatticeHamiltonian V s).H_tot = (s : ℂ) • V.V_tot`. -/
theorem perturbationLatticeHamiltonian_H_tot {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    (V : QuasiLocalPerturbation D L Site) (s : ℝ) :
    (perturbationLatticeHamiltonian V s).totalHamiltonian = (s : ℂ) • V.totalPerturbation := by
  unfold LatticeHamiltonian.totalHamiltonian perturbationLatticeHamiltonian perturbationLatticeTerm
    QuasiLocalPerturbation.totalPerturbation
  (try dsimp only)
  rw [Finset.sum_comm, Finset.smul_sum]
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [← Finset.sum_filter, Finset.smul_sum]
  refine Finset.sum_congr ?_ fun _ _ => rfl
  ext Z; simp

/-- At $s = 1$, `(perturbationLatticeHamiltonian V 1).H_tot = V.V_tot`. -/
theorem perturbationLatticeHamiltonian_one_H_tot {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    (V : QuasiLocalPerturbation D L Site) :
    (perturbationLatticeHamiltonian V 1).totalHamiltonian = V.totalPerturbation := by
  rw [perturbationLatticeHamiltonian_H_tot, Complex.ofReal_one, one_smul]

/-- $L$-independent Hastings–Koma `s1` factor for a `QuasiLocalPerturbation` with decay profile `f`:
    `quasiLocalS1Factor D f η := (2 : ℝ) ^ (D + Nat.ceil η) * ∑' r : ℕ, (r : ℝ) ^ (2 * D + Nat.ceil η) * f r`. -/
def quasiLocalS1Factor (D : ℕ) (f : ℕ → ℝ) (η : ℝ) : ℝ :=
  (2 : ℝ) ^ (D + Nat.ceil η) * ∑' r : ℕ, (r : ℝ) ^ (2 * D + Nat.ceil η) * f r

lemma quasiLocalS1Factor_nonneg (D : ℕ) {f : ℕ → ℝ} (hf : IsSuperpolynomialDecay f) (η : ℝ) :
    0 ≤ quasiLocalS1Factor D f η := by
  unfold quasiLocalS1Factor
  exact mul_nonneg (by positivity) (tsum_nonneg fun r => mul_nonneg (by positivity) (hf.1 r))

/-- Helper: for any region `Z` with `Z.card ≤ r ^ D`, `regionDiam Z ≤ r`, `1 ≤ r`, and `0 ≤ η`:
    `(Z.card : ℝ) * (1 + (regionDiam Z : ℝ)) ^ η ≤ (2 : ℝ) ^ (Nat.ceil η) * (r : ℝ) ^ (D + Nat.ceil η)`. -/
lemma card_mul_one_add_regionDiam_rpow_le {D L : ℕ} {Z : Finset (BoxD D L)} {r : ℕ} {η : ℝ}
    (hr1 : 1 ≤ r) (hη : 0 ≤ η) (hcard : Z.card ≤ r ^ D) (hdiam : regionDiam Z ≤ r) :
    (Z.card : ℝ) * (1 + (regionDiam Z : ℝ)) ^ η ≤
      (2 : ℝ) ^ (Nat.ceil η) * (r : ℝ) ^ (D + Nat.ceil η) := by
  have hcard_r : (Z.card : ℝ) ≤ (r : ℝ) ^ D := by exact_mod_cast hcard
  have h1_le_base : (1 : ℝ) ≤ 1 + (regionDiam Z : ℝ) :=
    le_add_of_nonneg_right (Nat.cast_nonneg _)
  have h_base_le : 1 + (regionDiam Z : ℝ) ≤ 2 * (r : ℝ) := by
    have hd_r : (regionDiam Z : ℝ) ≤ (r : ℝ) := by exact_mod_cast hdiam
    have hr_r : (1 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr1
    linarith
  have h_rpow_le : (1 + (regionDiam Z : ℝ)) ^ η ≤
      (2 : ℝ) ^ (Nat.ceil η) * (r : ℝ) ^ (Nat.ceil η) := by
    calc (1 + (regionDiam Z : ℝ)) ^ η
      _ ≤ (1 + (regionDiam Z : ℝ)) ^ ((Nat.ceil η : ℕ) : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le h1_le_base (Nat.le_ceil η)
      _ = (1 + (regionDiam Z : ℝ)) ^ (Nat.ceil η) := Real.rpow_natCast _ _
      _ ≤ (2 * (r : ℝ)) ^ (Nat.ceil η) :=
        pow_le_pow_left₀ (by positivity) h_base_le (Nat.ceil η)
      _ = (2 : ℝ) ^ (Nat.ceil η) * (r : ℝ) ^ (Nat.ceil η) := mul_pow _ _ _
  calc (Z.card : ℝ) * (1 + (regionDiam Z : ℝ)) ^ η
    _ ≤ (r : ℝ) ^ D * ((2 : ℝ) ^ (Nat.ceil η) * (r : ℝ) ^ (Nat.ceil η)) :=
      mul_le_mul hcard_r h_rpow_le (by positivity) (by positivity)
    _ = (2 : ℝ) ^ (Nat.ceil η) * (r : ℝ) ^ (D + Nat.ceil η) := by
      rw [pow_add]; ring

/-- Pointwise site sum bound for `perturbationLatticeTerm V s Z` at any site `x : BoxD D L`. -/
theorem sum_perturbationLatticeTerm_s1_le_J_mul {D L : ℕ} [NeZero D] [NeZero L]
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    (V : QuasiLocalPerturbation D L Site) {J s η : ℝ} {f : ℕ → ℝ}
    (hJ : 0 ≤ J) (hs : |s| ≤ 1) (hf : IsSuperpolynomialDecay f)
    (hV : V.SatisfiesDecayBound J f) (hη : 0 ≤ η) (x : BoxD D L) :
    (∑ Z ∈ Finset.univ.filter (fun Z : Finset (BoxD D L) => x ∈ Z),
      ‖perturbationLatticeTerm V s Z‖ * (Z.card : ℝ) * (1 + (regionDiam Z : ℝ)) ^ η) ≤
      J * quasiLocalS1Factor D f η := by
  let w : Finset (BoxD D L) → ℝ := fun Z => (Z.card : ℝ) * (1 + (regionDiam Z : ℝ)) ^ η
  have hw_nn : ∀ Z, 0 ≤ w Z := fun Z => by dsimp [w]; positivity
  have h_term : ∀ Z ∈ Finset.univ.filter (fun Z : Finset (BoxD D L) => x ∈ Z),
      ‖perturbationLatticeTerm V s Z‖ * w Z ≤
        ∑ r ∈ Finset.Icc 1 L,
          if Z ∈ (boxCubes D L r).filter (fun A => ¬ Disjoint A (boxCube x 1)) then
            J * f r * ((2 : ℝ) ^ (Nat.ceil η) * (r : ℝ) ^ (D + Nat.ceil η))
          else 0 := by
    intro Z hZ
    have hxZ : x ∈ Z := (Finset.mem_filter.mp hZ).2
    have hx1 : x ∈ boxCube x 1 := singleton_subset_boxCube x le_rfl (Finset.mem_singleton_self x)
    have h_nd : ¬ Disjoint Z (boxCube x 1) := Finset.not_disjoint_iff.mpr ⟨x, hxZ, hx1⟩
    unfold perturbationLatticeTerm
    calc ‖∑ r ∈ Finset.Icc 1 L, if Z ∈ boxCubes D L r then (s : ℂ) • V.term r Z else 0‖ * w Z
      _ ≤ (∑ r ∈ Finset.Icc 1 L, ‖if Z ∈ boxCubes D L r then (s : ℂ) • V.term r Z else 0‖) * w Z :=
        mul_le_mul_of_nonneg_right (norm_sum_le _ _) (hw_nn Z)
      _ = ∑ r ∈ Finset.Icc 1 L, ‖if Z ∈ boxCubes D L r then (s : ℂ) • V.term r Z else 0‖ * w Z :=
        Finset.sum_mul _ _ _
      _ ≤ ∑ r ∈ Finset.Icc 1 L,
            if Z ∈ (boxCubes D L r).filter (fun A => ¬ Disjoint A (boxCube x 1)) then
              J * f r * ((2 : ℝ) ^ (Nat.ceil η) * (r : ℝ) ^ (D + Nat.ceil η))
            else 0 := by
        refine Finset.sum_le_sum fun r hr => ?_
        by_cases hZr : Z ∈ boxCubes D L r
        · have hZ_mem : Z ∈ (boxCubes D L r).filter (fun A => ¬ Disjoint A (boxCube x 1)) :=
            Finset.mem_filter.mpr ⟨hZr, h_nd⟩
          rw [if_pos hZr, if_pos hZ_mem, norm_smul, Complex.norm_real, Real.norm_eq_abs]
          have h_norm_V : |s| * ‖V.term r Z‖ ≤ J * f r := by
            calc |s| * ‖V.term r Z‖
              _ ≤ 1 * (J * f r) := mul_le_mul hs (hV r hr Z hZr) (norm_nonneg _) zero_le_one
              _ = J * f r := one_mul _
          have hZ_eq : boxCube (anchorOfCube r Z) r = Z := boxCube_anchorOfCube hZr
          have h_wZ : w Z ≤ (2 : ℝ) ^ (Nat.ceil η) * (r : ℝ) ^ (D + Nat.ceil η) :=
            card_mul_one_add_regionDiam_rpow_le (Finset.mem_Icc.mp hr).1 hη
              (hZ_eq ▸ card_boxCube_le_pow (anchorOfCube r Z) r)
              (hZ_eq ▸ regionDiam_boxCube_le (anchorOfCube r Z) r)
          exact mul_le_mul h_norm_V h_wZ (hw_nn Z) (mul_nonneg hJ (hf.1 r))
        · have hZ_nmem : Z ∉ (boxCubes D L r).filter (fun A => ¬ Disjoint A (boxCube x 1)) :=
            fun h => hZr (Finset.mem_filter.mp h).1
          rw [if_neg hZr, if_neg hZ_nmem, norm_zero, zero_mul]
  have h_scale : ∀ r ∈ Finset.Icc 1 L,
      (∑ Z ∈ Finset.univ.filter (fun Z : Finset (BoxD D L) => x ∈ Z),
        if Z ∈ (boxCubes D L r).filter (fun A => ¬ Disjoint A (boxCube x 1)) then
          J * f r * ((2 : ℝ) ^ (Nat.ceil η) * (r : ℝ) ^ (D + Nat.ceil η))
        else 0) ≤
      J * (2 : ℝ) ^ (D + Nat.ceil η) * ((r : ℝ) ^ (2 * D + Nat.ceil η) * f r) := by
    intro r hr
    let S_r := (boxCubes D L r).filter (fun A => ¬ Disjoint A (boxCube x 1))
    let C_r := J * f r * ((2 : ℝ) ^ (Nat.ceil η) * (r : ℝ) ^ (D + Nat.ceil η))
    have hCr_nn : 0 ≤ C_r := by dsimp [C_r]; have := hf.1 r; positivity
    have h_le_univ : (∑ Z ∈ Finset.univ.filter (fun Z : Finset (BoxD D L) => x ∈ Z),
        if Z ∈ S_r then C_r else 0) ≤
        ∑ Z : Finset (BoxD D L), if Z ∈ S_r then C_r else 0 :=
      Finset.sum_le_univ_sum_of_nonneg fun Z => by split_ifs <;> [exact hCr_nn; exact le_rfl]
    have h_univ_eq : (∑ Z : Finset (BoxD D L), if Z ∈ S_r then C_r else 0) =
        (S_r.card : ℝ) * C_r := by
      rw [← Finset.sum_filter, Finset.filter_univ_mem, Finset.sum_const, nsmul_eq_mul]
    have hr1 : 1 ≤ r := (Finset.mem_Icc.mp hr).1
    have h_card_nat : S_r.card ≤ (2 * r) ^ D := by
      have h1 : S_r.card ≤ (r + 1) ^ D := card_filter_not_disjoint_boxCube_le_pow x r 1
      have h2 : (r + 1) ^ D ≤ (2 * r) ^ D := Nat.pow_le_pow_left (by omega) D
      exact le_trans h1 h2
    have h_card_r : (S_r.card : ℝ) ≤ (2 : ℝ) ^ D * (r : ℝ) ^ D := by
      have h_c : (S_r.card : ℝ) ≤ ((2 * r : ℝ)) ^ D := by exact_mod_cast h_card_nat
      rwa [mul_pow] at h_c
    calc (∑ Z ∈ Finset.univ.filter (fun Z : Finset (BoxD D L) => x ∈ Z),
          if Z ∈ S_r then C_r else 0)
      _ ≤ (S_r.card : ℝ) * C_r := h_univ_eq ▸ h_le_univ
      _ ≤ ((2 : ℝ) ^ D * (r : ℝ) ^ D) * C_r := mul_le_mul_of_nonneg_right h_card_r hCr_nn
      _ = J * (2 : ℝ) ^ (D + Nat.ceil η) * ((r : ℝ) ^ (2 * D + Nat.ceil η) * f r) := by
        dsimp [C_r]
        have h_pow2 : (2 : ℝ) ^ (D + Nat.ceil η) = (2 : ℝ) ^ D * (2 : ℝ) ^ (Nat.ceil η) :=
          pow_add 2 D (Nat.ceil η)
        have h_powr : (r : ℝ) ^ (2 * D + Nat.ceil η) =
            (r : ℝ) ^ D * ((r : ℝ) ^ D * (r : ℝ) ^ (Nat.ceil η)) := by
          have h_idx : 2 * D + Nat.ceil η = D + (D + Nat.ceil η) := by omega
          rw [h_idx, pow_add, pow_add]
        rw [h_pow2, h_powr]; ring
  calc (∑ Z ∈ Finset.univ.filter (fun Z : Finset (BoxD D L) => x ∈ Z),
        ‖perturbationLatticeTerm V s Z‖ * (Z.card : ℝ) * (1 + (regionDiam Z : ℝ)) ^ η)
    _ = ∑ Z ∈ Finset.univ.filter (fun Z : Finset (BoxD D L) => x ∈ Z),
          ‖perturbationLatticeTerm V s Z‖ * w Z := by
      refine Finset.sum_congr rfl fun Z _ => by dsimp [w]; ring
    _ ≤ ∑ Z ∈ Finset.univ.filter (fun Z : Finset (BoxD D L) => x ∈ Z),
          ∑ r ∈ Finset.Icc 1 L,
            if Z ∈ (boxCubes D L r).filter (fun A => ¬ Disjoint A (boxCube x 1)) then
              J * f r * ((2 : ℝ) ^ (Nat.ceil η) * (r : ℝ) ^ (D + Nat.ceil η))
            else 0 := Finset.sum_le_sum h_term
    _ = ∑ r ∈ Finset.Icc 1 L,
          ∑ Z ∈ Finset.univ.filter (fun Z : Finset (BoxD D L) => x ∈ Z),
            if Z ∈ (boxCubes D L r).filter (fun A => ¬ Disjoint A (boxCube x 1)) then
              J * f r * ((2 : ℝ) ^ (Nat.ceil η) * (r : ℝ) ^ (D + Nat.ceil η))
            else 0 := Finset.sum_comm
    _ ≤ ∑ r ∈ Finset.Icc 1 L,
          J * (2 : ℝ) ^ (D + Nat.ceil η) * ((r : ℝ) ^ (2 * D + Nat.ceil η) * f r) :=
      Finset.sum_le_sum h_scale
    _ = (J * (2 : ℝ) ^ (D + Nat.ceil η)) *
          ∑ r ∈ Finset.Icc 1 L, (r : ℝ) ^ (2 * D + Nat.ceil η) * f r := by
      rw [← Finset.mul_sum]
    _ ≤ (J * (2 : ℝ) ^ (D + Nat.ceil η)) *
          ∑' r : ℕ, (r : ℝ) ^ (2 * D + Nat.ceil η) * f r := by
      refine mul_le_mul_of_nonneg_left ?_ (by positivity)
      exact (summable_pow_mul_of_isSuperpolynomialDecay hf (2 * D + Nat.ceil η)).sum_le_tsum
        (Finset.Icc 1 L) (fun r _ => mul_nonneg (by positivity) (hf.1 r))
    _ = J * quasiLocalS1Factor D f η := by unfold quasiLocalS1Factor; ring

/-- **$L$-Independent `s1` Bound for `perturbationLatticeHamiltonian`
    (`perturbationLatticeHamiltonian_s1_le_J_mul`)**:
    When `V.SatisfiesDecayBound J f` (`0 ≤ J`, `|s| ≤ 1`, `IsSuperpolynomialDecay f`, `0 ≤ η`),
    `(perturbationLatticeHamiltonian V s).s1 η ≤ J * quasiLocalS1Factor D f η`. -/
theorem perturbationLatticeHamiltonian_s1_le_J_mul {D L : ℕ} [NeZero D] [NeZero L]
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    (V : QuasiLocalPerturbation D L Site) {J s η : ℝ} {f : ℕ → ℝ}
    (hJ : 0 ≤ J) (hs : |s| ≤ 1) (hf : IsSuperpolynomialDecay f)
    (hV : V.SatisfiesDecayBound J f) (hη : 0 ≤ η) :
    (perturbationLatticeHamiltonian V s).s1 η ≤ J * quasiLocalS1Factor D f η := by
  unfold LatticeHamiltonian.s1 perturbationLatticeHamiltonian
  (try dsimp only)
  exact Finset.sup'_le Finset.univ_nonempty _ fun x _ =>
    sum_perturbationLatticeTerm_s1_le_J_mul V hJ hs hf hV hη x

/-- $L$-independent Hastings–Koma `s1` bound for the unperturbed CSS Hamiltonian `mem.sys.H0`. -/
def bdlInhomogeneousUnperturbedS1Bound (η : ℝ) : ℝ :=
  bdlInhomogeneousSiteWeightBound *
    (((2 * r0BDL + 1 : ℕ) : ℝ) ^ 3) *
    (1 + ((2 * r0BDL + 1 : ℕ) : ℝ)) ^ (Nat.ceil η)

lemma bdlInhomogeneousUnperturbedS1Bound_nonneg (η : ℝ) :
    0 ≤ bdlInhomogeneousUnperturbedS1Bound η := by
  unfold bdlInhomogeneousUnperturbedS1Bound
  have := bdlInhomogeneousSiteWeightBound_nonneg
  positivity

/-- Pointwise site sum bound for `unperturbedLatticeTerm mem.sys Z` at any site `x : Box3D L`. -/
theorem sum_unperturbedLatticeTerm_s1_inhomogeneous_le {L : ℕ} [NeZero L]
    {c_star C β_c c_F η_mem c_mem η : ℝ}
    (mem : Inhomogeneous3DMemoryRealization L qCodeBDL r0BDL mMaxBDL c_star C β_c c_F η_mem c_mem)
    (hη : 0 ≤ η) (x : Box3D L) :
    (∑ Z ∈ Finset.univ.filter (fun Z : Finset (Box3D L) => x ∈ Z),
      ‖unperturbedLatticeTerm mem.sys Z‖ * (Z.card : ℝ) * (1 + (regionDiam Z : ℝ)) ^ η) ≤
      bdlInhomogeneousUnperturbedS1Bound η := by
  haveI : NeZero 3 := ⟨by decide⟩
  let w : Finset (Box3D L) → ℝ := fun Z => (Z.card : ℝ) * (1 + (regionDiam Z : ℝ)) ^ η
  let W_max : ℝ := (((2 * r0BDL + 1 : ℕ) : ℝ) ^ 3) *
    (1 + ((2 * r0BDL + 1 : ℕ) : ℝ)) ^ (Nat.ceil η)
  let S_x := Finset.univ.filter (fun i : StaticCSSCheckIdx L qCodeBDL mMaxBDL =>
    x ∈ mem.sys.support i)
  have hw_nn : ∀ Z, 0 ≤ w Z := fun Z => by dsimp [w]; positivity
  have hw_supp : ∀ i : StaticCSSCheckIdx L qCodeBDL mMaxBDL,
      w (mem.sys.support i) ≤ W_max := by
    intro i
    have h_supp_eq : mem.sys.support i = staticCSSCheckSupport mem.D_field i :=
      (mem.h_sys_checks i).2.1
    rcases staticCSSCheckSite_mem_and_subset_boxBall mem.D_field i with ⟨_, h_sub_ball⟩
    have h_sub_cube : mem.sys.support i ⊆
        boxCube (fun d => ⟨(staticCSSCheckSite i d).val - r0BDL,
          Nat.sub_lt_of_lt (staticCSSCheckSite i d).isLt⟩) (2 * r0BDL + 1) :=
      Finset.Subset.trans (h_supp_eq ▸ h_sub_ball)
        (boxBall_subset_boxCube (staticCSSCheckSite i) r0BDL)
    have hcard : ((mem.sys.support i).card : ℝ) ≤ ((2 * r0BDL + 1 : ℕ) : ℝ) ^ 3 := by
      have hc : (mem.sys.support i).card ≤ (2 * r0BDL + 1) ^ 3 :=
        le_trans (Finset.card_le_card h_sub_cube) (card_boxCube_le_pow _ (2 * r0BDL + 1))
      exact_mod_cast hc
    have hdiam : (regionDiam (mem.sys.support i) : ℝ) ≤ ((2 * r0BDL + 1 : ℕ) : ℝ) := by
      have hd : regionDiam (mem.sys.support i) ≤ 2 * r0BDL + 1 :=
        le_trans (regionDiam_mono h_sub_cube) (regionDiam_boxCube_le _ (2 * r0BDL + 1))
      exact_mod_cast hd
    have h_rpow : (1 + (regionDiam (mem.sys.support i) : ℝ)) ^ η ≤
        (1 + ((2 * r0BDL + 1 : ℕ) : ℝ)) ^ (Nat.ceil η) := by
      calc (1 + (regionDiam (mem.sys.support i) : ℝ)) ^ η
        _ ≤ (1 + (regionDiam (mem.sys.support i) : ℝ)) ^ ((Nat.ceil η : ℕ) : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le (le_add_of_nonneg_right (Nat.cast_nonneg _))
            (Nat.le_ceil η)
        _ = (1 + (regionDiam (mem.sys.support i) : ℝ)) ^ (Nat.ceil η) := Real.rpow_natCast _ _
        _ ≤ (1 + ((2 * r0BDL + 1 : ℕ) : ℝ)) ^ (Nat.ceil η) :=
          pow_le_pow_left₀ (by positivity) (by linarith) (Nat.ceil η)
    exact mul_le_mul hcard h_rpow (by positivity) (by positivity)
  have h_term : ∀ Z ∈ Finset.univ.filter (fun Z : Finset (Box3D L) => x ∈ Z),
      ‖unperturbedLatticeTerm mem.sys Z‖ * w Z ≤
        ∑ i ∈ S_x, if mem.sys.support i = Z then mem.sys.weight i * W_max else 0 := by
    intro Z hZ
    have hxZ : x ∈ Z := (Finset.mem_filter.mp hZ).2
    have h_filt_eq : Finset.univ.filter (fun i => mem.sys.support i = Z) =
        S_x.filter (fun i => mem.sys.support i = Z) := by
      ext i
      simp only [S_x, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨fun h => ⟨h ▸ hxZ, h⟩, fun h => h.2⟩
    unfold unperturbedLatticeTerm
    rw [h_filt_eq]
    calc ‖∑ i ∈ S_x.filter (fun i => mem.sys.support i = Z),
            (mem.sys.weight i : ℂ) • mem.sys.checkProj i‖ * w Z
      _ ≤ (∑ i ∈ S_x.filter (fun i => mem.sys.support i = Z),
            ‖(mem.sys.weight i : ℂ) • mem.sys.checkProj i‖) * w Z :=
        mul_le_mul_of_nonneg_right (norm_sum_le _ _) (hw_nn Z)
      _ = ∑ i ∈ S_x.filter (fun i => mem.sys.support i = Z),
            ‖(mem.sys.weight i : ℂ) • mem.sys.checkProj i‖ * w Z :=
        Finset.sum_mul _ _ _
      _ ≤ ∑ i ∈ S_x.filter (fun i => mem.sys.support i = Z), mem.sys.weight i * W_max := by
        refine Finset.sum_le_sum fun i hi => ?_
        have h_eqZ : mem.sys.support i = Z := (Finset.mem_filter.mp hi).2
        have hw_i_nn : 0 ≤ mem.sys.weight i := le_trans zero_le_one (mem.sys.weight_ge_one i)
        have hQ_le : ‖(mem.sys.weight i : ℂ) • mem.sys.checkProj i‖ ≤ mem.sys.weight i := by
          rw [norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hw_i_nn]
          have hP : ‖mem.sys.checkProj i‖ ≤ 1 := by
            have hproj := mem.sys.is_projector i
            by_cases h0 : ‖mem.sys.checkProj i‖ = 0
            · linarith
            · have hp : 0 < ‖mem.sys.checkProj i‖ :=
                lt_of_le_of_ne (norm_nonneg _) (Ne.symm h0)
              have hsq : ‖mem.sys.checkProj i‖ * ‖mem.sys.checkProj i‖ ≤
                  1 * ‖mem.sys.checkProj i‖ := by
                rw [one_mul, ← CStarRing.norm_star_mul_self, hproj.isSelfAdjoint.star_eq,
                  hproj.isIdempotentElem.eq]
              exact le_of_mul_le_mul_right hsq hp
          nlinarith
        rw [← h_eqZ]
        exact mul_le_mul hQ_le (hw_supp i) (hw_nn _) hw_i_nn
      _ = ∑ i ∈ S_x, if mem.sys.support i = Z then mem.sys.weight i * W_max else 0 := by
        rw [Finset.sum_filter]
  calc (∑ Z ∈ Finset.univ.filter (fun Z : Finset (Box3D L) => x ∈ Z),
        ‖unperturbedLatticeTerm mem.sys Z‖ * (Z.card : ℝ) * (1 + (regionDiam Z : ℝ)) ^ η)
    _ = ∑ Z ∈ Finset.univ.filter (fun Z : Finset (Box3D L) => x ∈ Z),
          ‖unperturbedLatticeTerm mem.sys Z‖ * w Z := by
      refine Finset.sum_congr rfl fun Z _ => by dsimp [w]; ring
    _ ≤ ∑ Z ∈ Finset.univ.filter (fun Z : Finset (Box3D L) => x ∈ Z),
          ∑ i ∈ S_x, if mem.sys.support i = Z then mem.sys.weight i * W_max else 0 :=
      Finset.sum_le_sum h_term
    _ = ∑ i ∈ S_x,
          ∑ Z ∈ Finset.univ.filter (fun Z : Finset (Box3D L) => x ∈ Z),
            if mem.sys.support i = Z then mem.sys.weight i * W_max else 0 :=
      Finset.sum_comm
    _ = ∑ i ∈ S_x, mem.sys.weight i * W_max := by
      refine Finset.sum_congr rfl fun i hi => ?_
      have h_mem_Z : mem.sys.support i ∈ Finset.univ.filter (fun Z : Finset (Box3D L) => x ∈ Z) :=
        Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hi).2⟩
      rw [Finset.sum_ite_eq, if_pos h_mem_Z]
    _ = (∑ i ∈ S_x, mem.sys.weight i) * W_max := (Finset.sum_mul _ _ _).symm
    _ ≤ bdlInhomogeneousSiteWeightBound * W_max :=
      mul_le_mul_of_nonneg_right (sum_weight_mem_support_inhomogeneous_le mem x) (by positivity)
    _ = bdlInhomogeneousUnperturbedS1Bound η := by
      unfold bdlInhomogeneousUnperturbedS1Bound; dsimp [W_max]; ring

end
