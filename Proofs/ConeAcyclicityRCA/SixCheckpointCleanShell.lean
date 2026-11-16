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

import Proofs.ConeAcyclicityRCA.BlockSDRAndTwoStepNilpotency
import Proofs.F2TQOToOperatorTQO

/-!
# Clean-Shell Pigeonhole Principle, Rescaled RCA, and Open-Box F_2 Linear TQO

Proves the finite-support pigeonhole principle selecting a clean checkpoint shell (checkpoint_pigeonhole_clean_shell), establishes primal and dual RescaledRelativeConeAcyclicity for bdlWeldedCode (bdlWeldedCode_rescaledRCA), and transfers continuum cone acyclicity via fiber-rank slot bijections and open-box snapping to prove SatisfiesBoxF2LinearTQO for bdlLocalDescriptor (bdlLocalDescriptor_satisfiesBoxF2LinearTQO).

## References

* Part I, Section 3.1 (`subsec:rca-trinity`), Definition 3.1 (`def:rca`), Definition 3.2 (`def:tqo`), Proposition 3.3 (`prop:trinity-equivalence`)
* Part I, Section 3.3 (`subsec:scale-matched-rca`), Lemma 3.8 (`lem:clean-shell-subcylinder`), Theorem 3.9 (`thm:rca-welded-hierarchy`)
* Part II, Section 2 (`subsec:setup`), Definition 2.1 (`def:bdl-lattice`), Definition 2.2 (`def:RCA`)
* Part II, Section 4 (`subsec:welded-hierarchy-cleaner`), Proposition 4.3 (`prop:rca-hierarchy`)
-/

noncomputable section

open scoped Classical BigOperators

/-! ## 1. `numCheckpointsBDL` Radial Checkpoints and Clean Shell Selection (Part I, Section 3.3 (`subsec:scale-matched-rca`), Lemma 3.8 (`lem:clean-shell-subcylinder`)) -/

/-- Radial checkpoint step spacing $s_{\mathrm{chk}} = m / (2 \cdot \mathrm{numCheckpointsBDL})$
    inside the $m = \mathrm{bdlSubdivM}$ cylinder subdivision. -/
def bdlCheckpointSpacing : ℕ := bdlSubdivM / (2 * numCheckpointsBDL)

/-- For any `numCheckpointsBDL` pairwise separated radial checkpoint shells $S_i$ such that no
    two distinct shells can both intersect $U$, at least one shell $S_i$ is completely disjoint from $U$. -/
theorem checkpoint_pigeonhole_clean_shell {α : Type} [DecidableEq α]
    (S : Fin numCheckpointsBDL → Finset α) (U : Finset α)
    (h_sep : ∀ i j : Fin numCheckpointsBDL, i ≠ j → ¬((S i ∩ U).Nonempty ∧ (S j ∩ U).Nonempty)) :
    ∃ i : Fin numCheckpointsBDL, Disjoint (S i) U := by
  let i0 : Fin numCheckpointsBDL := ⟨0, by decide⟩
  let i1 : Fin numCheckpointsBDL := ⟨1, by decide⟩
  by_cases h0 : Disjoint (S i0) U
  · exact ⟨i0, h0⟩
  · refine ⟨i1, ?_⟩
    rw [Finset.disjoint_iff_inter_eq_empty] at h0 ⊢
    have h0_ne : (S i0 ∩ U).Nonempty := Finset.nonempty_iff_ne_empty.mpr h0
    have h1_not : ¬(S i1 ∩ U).Nonempty := fun h1_ne =>
      h_sep i0 i1 (by decide) ⟨h0_ne, h1_ne⟩
    exact Finset.not_nonempty_iff_eq_empty.mp h1_not

/-! ## 2. Inductive Rescaled Relative Cone Acyclicity & $\mathbb{F}_2$ Linear TQO (Part I, Theorem 3.9 (`thm:rca-welded-hierarchy`); Part II, Proposition 4.3 (`prop:rca-hierarchy`)) -/

/-- **Inductive Rescaled Relative Cone Acyclicity & $\mathbb{F}_2$ Linear TQO (Part I, Theorem 3.9 (`thm:rca-welded-hierarchy`); Part II, Proposition 4.3 (`prop:rca-hierarchy`))**:
    Across all hierarchy levels $k \in \mathbb{N}$, the 6-checkpoint clean-shell pigeonhole lemma and
    scale-matched stopping depth $s^*$ establish `SatisfiesF2LinearTQO` for both
    `bdlWeldedCode k` and `dualCode (bdlWeldedCode k)` up to macroscopic radius `bdlLinearTQORadius k`
    with multiplicative factor `collarConstRCABDL` and additive collar `cAddBDL`. -/
theorem bdlWeldedCode_rescaledRCA :
    ∀ k : ℕ,
      SatisfiesF2LinearTQO (bdlWeldedCode k) (bdlLinearTQORadius k : ℝ)
        (collarConstRCABDL : ℝ) cAddBDL ∧
      SatisfiesF2LinearTQO (dualCode (bdlWeldedCode k)) (bdlLinearTQORadius k : ℝ)
        (collarConstRCABDL : ℝ) cAddBDL := by
  intro k
  refine ⟨⟨fun x0 r hr hr_max => (bdlWeldedStep_blockSDR_transfer k x0 r hr hr_max).1,
           fun x0 r hr hr_max => (bdlWeldedStep_blockSDR_transfer k x0 r hr hr_max).2⟩,
          ⟨fun x0 r hr hr_max => (bdlWeldedStep_blockSDR_transfer k x0 r hr hr_max).2,
           fun x0 r hr hr_max => (bdlWeldedStep_blockSDR_transfer k x0 r hr hr_max).1⟩⟩

/-! ## 3. Open-Box Lattice $\mathbb{F}_2$ Linear TQO (`SatisfiesBoxF2LinearTQO (bdlLocalDescriptor k)`) -/

private lemma fiber_localRank_lt_card {X V : Type*} [Fintype X] [DecidableEq V]
    (f : X → V) (idx : X → ℕ) (x : X) :
    ((Finset.univ.filter (fun x' : X => f x' = f x)).filter (fun x' => idx x' < idx x)).card <
      (Finset.univ.filter (fun x' : X => f x' = f x)).card := by
  apply Finset.card_lt_card
  rw [Finset.ssubset_iff_subset_ne]
  refine ⟨Finset.filter_subset _ _, fun h_eq => ?_⟩
  have hx : x ∈ Finset.univ.filter (fun x' : X => f x' = f x) := by simp
  rw [← h_eq, Finset.mem_filter] at hx
  exact Nat.lt_irrefl _ hx.2

private lemma fiber_localRank_injective {X V : Type*} [Fintype X] [DecidableEq V]
    (f : X → V) (idx : X → ℕ) (h_inj : Function.Injective idx) :
    Function.Injective (fun x : X =>
      (f x, ((Finset.univ.filter (fun x' : X => f x' = f x)).filter
        (fun x' => idx x' < idx x)).card)) := by
  intro x₁ x₂ h
  have hf : f x₁ = f x₂ := (Prod.ext_iff.mp h).1
  have hr := (Prod.ext_iff.mp h).2
  have h_lt : ∀ a b : X, f a = f b → idx a < idx b →
      ((Finset.univ.filter (fun x' : X => f x' = f a)).filter (fun x' => idx x' < idx a)).card <
      ((Finset.univ.filter (fun x' : X => f x' = f b)).filter (fun x' => idx x' < idx b)).card := by
    intro a b hab hlt; rw [hab]; apply Finset.card_lt_card; rw [Finset.ssubset_iff_subset_ne]
    refine ⟨fun y hy => ?_, fun h_eq => ?_⟩
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hy ⊢
      exact ⟨hy.1, Nat.lt_trans hy.2 hlt⟩
    · have ha : a ∈ (Finset.univ.filter (fun x' : X => f x' = f b)).filter (fun x' => idx x' < idx b) :=
        Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, hab⟩, hlt⟩
      rw [← h_eq, Finset.mem_filter] at ha; exact Nat.lt_irrefl _ ha.2
  rcases lt_trichotomy (idx x₁) (idx x₂) with h1 | heq | h2
  · exact False.elim (ne_of_lt (h_lt x₁ x₂ hf h1) hr)
  · exact h_inj heq
  · exact False.elim (ne_of_gt (h_lt x₂ x₁ hf.symm h2) hr)

private lemma fiber_localRank_surjective {X V : Type*} [Fintype X] [DecidableEq X] [DecidableEq V]
    (f : X → V) (idx : X → ℕ) (h_inj : Function.Injective idx)
    (v : V) (c : ℕ) (hc : c < (Finset.univ.filter (fun x' : X => f x' = v)).card) :
    ∃ x : X, f x = v ∧
      ((Finset.univ.filter (fun x' : X => f x' = f x)).filter
        (fun x' => idx x' < idx x)).card = c := by
  let S := Finset.univ.filter (fun x' : X => f x' = v)
  let g : S → Fin S.card := fun x =>
    ⟨((Finset.univ.filter (fun x' : X => f x' = f x.1)).filter (fun x' => idx x' < idx x.1)).card, by
      have hx : f x.1 = v := (Finset.mem_filter.mp x.2).2
      simpa [S, hx] using fiber_localRank_lt_card f idx x.1⟩
  have hg_inj : Function.Injective g := fun x₁ x₂ h =>
    Subtype.ext (fiber_localRank_injective f idx h_inj
      (Prod.ext ((Finset.mem_filter.mp x₁.2).2.trans (Finset.mem_filter.mp x₂.2).2.symm)
        (congr_arg Fin.val h)))
  obtain ⟨x, hx⟩ := ((Fintype.bijective_iff_injective_and_card g).mpr
    ⟨hg_inj, by simp [Fintype.card_coe, Fintype.card_fin]⟩).2 ⟨c, hc⟩
  exact ⟨x.1, (Finset.mem_filter.mp x.2).2, congr_arg Fin.val hx⟩

private lemma activeSlot_eq_true_iff_mem_image_bdlQubitSiteSlot (k : ℕ)
    (p : BoxSlot3D (bdlBoxSide k) qCodeBDL) :
    (bdlLocalDescriptor k p.1).activeSlot p.2 = true ↔
      p ∈ Finset.univ.image (bdlQubitSiteSlot k) := by
  rcases p with ⟨v, s⟩
  dsimp [bdlLocalDescriptor, bdlLocalDescriptorOfPlacement]
  rw [decide_eq_true_iff, Finset.mem_image]
  refine ⟨fun hs => ?_, ?_⟩
  · have h_injQ : Function.Injective (bdlCellIndexQ k) :=
      Fin.val_injective.comp (Fintype.equivFin _).injective
    obtain ⟨q, hqv, hqr⟩ :=
      fiber_localRank_surjective (bdlGridVertexQ k) (bdlCellIndexQ k) h_injQ v s.val hs
    refine ⟨q, Finset.mem_univ q, ?_⟩
    rw [bdlQubitSiteSlot_eq k q]
    exact Prod.ext hqv (Fin.ext hqr)
  · rintro ⟨q, _, hq⟩
    rw [bdlQubitSiteSlot_eq k q] at hq
    have hqv : bdlGridVertexQ k q = v := (Prod.ext_iff.mp hq).1
    have hqs : bdlQubitLocalRank k q = s.val := congr_arg Fin.val (Prod.ext_iff.mp hq).2
    rw [← hqv, ← hqs]
    exact bdlQubitLocalRank_lt_card k q

private lemma descriptorCheckXChain_eq_zero_of_not_mem_image' (k : ℕ)
    (vX : Box3D (bdlBoxSide k)) (idxX : Fin mMaxBDL)
    (p : BoxSlot3D (bdlBoxSide k) qCodeBDL)
    (hp : p ∉ Finset.univ.image (bdlQubitSiteSlot k)) :
    descriptorCheckXChain (bdlLocalDescriptor k) vX idxX p = 0 := by
  rcases p with ⟨w, s⟩
  dsimp [descriptorCheckXChain]
  rw [if_neg]
  rintro ⟨_, nb, _, h_sh, h_mask⟩
  dsimp [bdlLocalDescriptor, bdlLocalDescriptorOfPlacement] at h_mask
  rw [Bool.and_eq_true] at h_mask
  rcases decide_eq_true_iff.mp h_mask.2 with ⟨_, q, _, _, hq, _⟩
  apply hp
  rw [Finset.mem_image]
  exact ⟨q, Finset.mem_univ q, by simpa [h_sh, bdlQubitSiteSlot] using hq⟩

private lemma descriptorCheckZChain_eq_zero_of_not_mem_image' (k : ℕ)
    (vZ : Box3D (bdlBoxSide k)) (idxZ : Fin mMaxBDL)
    (p : BoxSlot3D (bdlBoxSide k) qCodeBDL)
    (hp : p ∉ Finset.univ.image (bdlQubitSiteSlot k)) :
    descriptorCheckZChain (bdlLocalDescriptor k) vZ idxZ p = 0 := by
  rcases p with ⟨w, s⟩
  dsimp [descriptorCheckZChain]
  rw [if_neg]
  rintro ⟨_, nb, _, h_sh, h_mask⟩
  dsimp [bdlLocalDescriptor, bdlLocalDescriptorOfPlacement] at h_mask
  rw [Bool.and_eq_true] at h_mask
  rcases decide_eq_true_iff.mp h_mask.2 with ⟨_, q, _, _, hq, _⟩
  apply hp
  rw [Finset.mem_image]
  exact ⟨q, Finset.mem_univ q, by simpa [h_sh, bdlQubitSiteSlot] using hq⟩

private lemma bdlCheckXLocalRank_lt_card (k : ℕ) (mX : BDLWeldedCheckX k) :
    bdlCheckXLocalRank k mX < (bdlCheckXFiber k (bdlGridVertexX k mX)).card :=
  fiber_localRank_lt_card (bdlGridVertexX k) (bdlCellIndexX k) mX

private lemma bdlCheckXLocalRank_lt_m_max (k : ℕ) (mX : BDLWeldedCheckX k) :
    bdlCheckXLocalRank k mX < mMaxBDL :=
  (bdlCheckXLocalRank_lt_card k mX).trans_le (bdlFiber_card_bounds k (bdlGridVertexX k mX)).2.1

private def bdlCheckXSlot (k : ℕ) (mX : BDLWeldedCheckX k) :
    Box3D (bdlBoxSide k) × Fin mMaxBDL :=
  (bdlGridVertexX k mX, ⟨bdlCheckXLocalRank k mX, bdlCheckXLocalRank_lt_m_max k mX⟩)

private lemma bdlCheckZLocalRank_lt_card (k : ℕ) (mZ : BDLWeldedCheckZ k) :
    bdlCheckZLocalRank k mZ < (bdlCheckZFiber k (bdlGridVertexZ k mZ)).card :=
  fiber_localRank_lt_card (bdlGridVertexZ k) (bdlCellIndexZ k) mZ

private lemma bdlCheckZLocalRank_lt_m_max (k : ℕ) (mZ : BDLWeldedCheckZ k) :
    bdlCheckZLocalRank k mZ < mMaxBDL :=
  (bdlCheckZLocalRank_lt_card k mZ).trans_le (bdlFiber_card_bounds k (bdlGridVertexZ k mZ)).2.2

private def bdlCheckZSlot (k : ℕ) (mZ : BDLWeldedCheckZ k) :
    Box3D (bdlBoxSide k) × Fin mMaxBDL :=
  (bdlGridVertexZ k mZ, ⟨bdlCheckZLocalRank k mZ, bdlCheckZLocalRank_lt_m_max k mZ⟩)

private lemma snapPointToOpenBox_mem_boxCube_imp_distInf3D_le {L : ℕ} [NeZero L] {M : ℝ}
    (hL : M + 1000 ≤ (L : ℝ) / 2) {p : Point3D} (hp : ∀ μ, |p μ| ≤ M)
    (x0 : Box3D L) (r : ℕ) (hq : snapPointToOpenBox L p ∈ boxCube x0 r) :
    distInf3D p (fun μ => ((x0 μ).val : ℝ) - (L : ℝ) / 2 + (r : ℝ) / 2) ≤ (r : ℝ) / 2 := by
  have h_cube := (Finset.mem_filter.mp hq).2
  have h_axis : ∀ μ : Fin 3,
      |p μ - (((x0 μ).val : ℝ) - (L : ℝ) / 2 + (r : ℝ) / 2)| ≤ (r : ℝ) / 2 := by
    intro μ
    have hc := h_cube μ
    have h_lo_nat : ((x0 μ).val : ℝ) ≤ ((snapPointToOpenBox L p μ).val : ℝ) :=
      Nat.cast_le.mpr hc.1
    have h_hi_nat : ((snapPointToOpenBox L p μ).val : ℝ) + 1 ≤ ((x0 μ).val : ℝ) + (r : ℝ) := by
      exact_mod_cast Nat.succ_le_of_lt hc.2
    have h_snap := (snapPointToOpenBox_bounds hL hp μ).2
    exact abs_le.mpr ⟨by linarith, by linarith⟩
  dsimp [distInf3D]
  exact max_le (max_le (h_axis 0) (h_axis 1)) (h_axis 2)

private lemma boxCube_subset_enclosingBoxCube (k : ℕ)
    (x0 : Box3D (bdlBoxSide k)) {r : ℕ} (hr1 : 1 ≤ r) :
    boxCube x0 r ⊆ enclosingBoxCube x0 r (linearExpansionRadius (collarConstRCABDL : ℝ) r) := by
  have hR_eq : linearExpansionRadius (collarConstRCABDL : ℝ) r = collarConstRCABDL * r := by
    dsimp [linearExpansionRadius]
    exact_mod_cast Nat.ceil_natCast (collarConstRCABDL * r)
  have hC_ge : 20 ≤ collarConstRCABDL := by
    dsimp [collarConstRCABDL]; omega
  intro y hy
  have hy_cube := (Finset.mem_filter.mp hy).2
  rw [hR_eq]
  refine Finset.mem_filter.mpr ⟨Finset.mem_univ y, fun μ => ?_⟩
  have hμ := hy_cube μ
  dsimp
  have : 20 * r ≤ collarConstRCABDL * r := Nat.mul_le_mul_right r hC_ge
  omega

private def kLinBDL : ℕ :=
  bdlLambda * (bdlLambda * (10005 * bdlLambda + 13006) + 13008)

private lemma kLinBDL_cast_eq : (kLinBDL : ℝ) = WeldedHierarchy.bdlRandomLinearConstant := by
  dsimp [kLinBDL, WeldedHierarchy.bdlRandomLinearConstant, WeldedHierarchy.bdlBaseFillingRadius]
  push_cast; ring

private lemma collarConstRCABDL_eq_two_mul_kLinBDL : collarConstRCABDL = 2 * kLinBDL + 20 := by
  dsimp [collarConstRCABDL, kLinBDL]
  rw [Nat.mul_assoc]

private lemma snapPointToOpenBox_boxBall_subset_enclosingBoxCube_aux
    {L K R : ℕ} [NeZero L] {M : ℝ} (hL : M + 1000 ≤ (L : ℝ) / 2)
    (x0 : Box3D L) {r : ℕ} (hr1 : 1 ≤ r) (hR : R = 2 * (K * r) + 20 * r)
    {p : Point3D} (hp : ∀ μ, |p μ| ≤ M)
    (h_dist_K : distInf3D p
      (fun μ => ((x0 μ).val : ℝ) - (L : ℝ) / 2 + (r : ℝ) / 2) ≤
      (K : ℝ) * (r : ℝ)) :
    boxBall (snapPointToOpenBox L p) r0BDL ⊆
      enclosingBoxCube x0 r R := by
  have hv_bounds : ∀ μ : Fin 3,
      (x0 μ).val ≤ (snapPointToOpenBox L p μ).val + K * r ∧
      2 * (snapPointToOpenBox L p μ).val ≤ 2 * (x0 μ).val + r + 2 * (K * r) := by
    intro μ
    have h_axis : |p μ - (((x0 μ).val : ℝ) - (L : ℝ) / 2 + (r : ℝ) / 2)| ≤
        (K : ℝ) * (r : ℝ) := by
      dsimp [distInf3D] at h_dist_K
      have h01 : max |p 0 - (((x0 0).val : ℝ) - (L : ℝ) / 2 + (r : ℝ) / 2)|
          |p 1 - (((x0 1).val : ℝ) - (L : ℝ) / 2 + (r : ℝ) / 2)| ≤
          (K : ℝ) * (r : ℝ) := le_trans (le_max_left _ _) h_dist_K
      fin_cases μ
      · exact le_trans (le_max_left _ _) h01
      · exact le_trans (le_max_right _ _) h01
      · exact le_trans (le_max_right _ _) h_dist_K
    have h_abs := abs_le.mp h_axis
    have h_snap := (snapPointToOpenBox_bounds hL hp μ).2
    have hr_nonneg : (0 : ℝ) ≤ (r : ℝ) := Nat.cast_nonneg r
    have h_lo_lt : ((x0 μ).val : ℝ) < (((snapPointToOpenBox L p μ).val + K * r + 1 : ℕ) : ℝ) := by
      push_cast; linarith
    have h_lo_nat : (x0 μ).val < (snapPointToOpenBox L p μ).val + K * r + 1 :=
      Nat.cast_lt.mp h_lo_lt
    have h_hi_le : ((2 * (snapPointToOpenBox L p μ).val : ℕ) : ℝ) ≤
        ((2 * (x0 μ).val + r + 2 * (K * r) : ℕ) : ℝ) := by
      push_cast; linarith
    exact ⟨Nat.lt_succ_iff.mp h_lo_nat, Nat.cast_le.mp h_hi_le⟩
  intro y hy
  have hy_ball : boxDist (snapPointToOpenBox L p) y ≤ r0BDL := (Finset.mem_filter.mp hy).2
  rw [hR]
  refine Finset.mem_filter.mpr ⟨Finset.mem_univ y, fun μ => ?_⟩
  have h_coord : coordDist (snapPointToOpenBox L p μ) (y μ) ≤ r0BDL := by
    dsimp [boxDist] at hy_ball
    exact le_trans
      (Finset.le_sup (f := fun i : Fin 3 => coordDist (snapPointToOpenBox L p i) (y i))
        (Finset.mem_univ μ))
      hy_ball
  have hvμ := hv_bounds μ
  dsimp [coordDist, r0BDL] at h_coord ⊢
  omega

private lemma snapPointToOpenBox_boxBall_subset_enclosingBoxCube (k : ℕ)
    (x0 : Box3D (bdlBoxSide k)) {r : ℕ} (hr1 : 1 ≤ r)
    {p : Point3D} (hp : ∀ μ, |p μ| ≤ bdlCoordBound (k + 1))
    (h_dist : distInf3D p
      (fun μ => ((x0 μ).val : ℝ) - (bdlBoxSide k : ℝ) / 2 + (r : ℝ) / 2) ≤
      (WeldedHierarchy.bdlRandomLinearConstant / 11) * (2 * ((r : ℝ) / 2) + 1) +
        WeldedHierarchy.bdlBaseFillingRadius) :
    boxBall (snapPointToOpenBox (bdlBoxSide k) p) r0BDL ⊆
      enclosingBoxCube x0 r (linearExpansionRadius (collarConstRCABDL : ℝ) r) := by
  have hR_eq : linearExpansionRadius (collarConstRCABDL : ℝ) r =
      2 * (kLinBDL * r) + 20 * r := by
    have h1 : linearExpansionRadius (collarConstRCABDL : ℝ) r = collarConstRCABDL * r := by
      dsimp [linearExpansionRadius]
      exact_mod_cast Nat.ceil_natCast (collarConstRCABDL * r)
    rw [h1, collarConstRCABDL_eq_two_mul_kLinBDL, Nat.right_distrib, Nat.mul_assoc]
  have hr1_real : (1 : ℝ) ≤ (r : ℝ) := Nat.one_le_cast.mpr hr1
  have hlam : (10000 : ℝ) ≤ (bdlLambda : ℝ) := WeldedHierarchy.bdlLambda_ge_10000
  have h_base_nonneg : (0 : ℝ) ≤ WeldedHierarchy.bdlBaseFillingRadius := by
    dsimp [WeldedHierarchy.bdlBaseFillingRadius]; nlinarith
  have h_lin_ge : 10000 * WeldedHierarchy.bdlBaseFillingRadius ≤ WeldedHierarchy.bdlRandomLinearConstant := by
    dsimp [WeldedHierarchy.bdlRandomLinearConstant]; nlinarith
  have h_lin_nonneg : (0 : ℝ) ≤ WeldedHierarchy.bdlRandomLinearConstant := by linarith
  have h_lin_le_r : WeldedHierarchy.bdlRandomLinearConstant ≤
      WeldedHierarchy.bdlRandomLinearConstant * (r : ℝ) :=
    le_mul_of_one_le_right h_lin_nonneg hr1_real
  have h_dist_K : distInf3D p
      (fun μ => ((x0 μ).val : ℝ) - (bdlBoxSide k : ℝ) / 2 + (r : ℝ) / 2) ≤
      (kLinBDL : ℝ) * (r : ℝ) := by
    have h_step : (WeldedHierarchy.bdlRandomLinearConstant / 11) * (2 * ((r : ℝ) / 2) + 1) +
        WeldedHierarchy.bdlBaseFillingRadius ≤
        WeldedHierarchy.bdlRandomLinearConstant * (r : ℝ) := by linarith
    have h_step2 := le_trans h_dist h_step
    rwa [← kLinBDL_cast_eq] at h_step2
  exact snapPointToOpenBox_boxBall_subset_enclosingBoxCube_aux
    (bdlCoordBound_add_1000_le_half_L k) x0 hr1 hR_eq hp h_dist_K

/-- **Open-Box Lattice $\mathbb{F}_2$ Linear TQO (`SatisfiesBoxF2LinearTQO (bdlLocalDescriptor k)`)**:
    For every hierarchy level $k \in \mathbb{N}$, the open-box BDL descriptor field `bdlLocalDescriptor k`
    on `Box3D (bdlBoxSide k)` satisfies `SatisfiesBoxF2LinearTQO` up to linear radius
    `bdlLinearTQORadius k` with linear expansion factor `(collarConstRCABDL : ℝ)`. -/
theorem bdlLocalDescriptor_satisfiesBoxF2LinearTQO (k : ℕ) :
    SatisfiesBoxF2LinearTQO (bdlLocalDescriptor k) (bdlLinearTQORadius k)
      (collarConstRCABDL : ℝ) := by
  intro r hr1 hr_max x0
  let A := boxCube x0 r
  let B := enclosingBoxCube x0 r (linearExpansionRadius (collarConstRCABDL : ℝ) r)
  let x_center : Point3D := fun μ => ((x0 μ).val : ℝ) - (bdlBoxSide k : ℝ) / 2 + (r : ℝ) / 2
  let r_inf : ℝ := (r : ℝ) / 2
  have hr_inf0 : 0 ≤ r_inf := by dsimp [r_inf]; positivity
  have h_r_max_le : (bdlLinearTQORadius k : ℝ) ≤ (bdlLambda : ℝ) ^ (2 * k) :=
    bdlLinearTQORadius_le_pow k
  have hr_inf_hi : r_inf ≤ (bdlLambda : ℝ) ^ (2 * k) + 2 := by
    have hr_cast : (r : ℝ) ≤ (bdlLinearTQORadius k : ℝ) := Nat.cast_le.mpr hr_max
    have hr_nonneg : (0 : ℝ) ≤ (r : ℝ) := Nat.cast_nonneg r
    dsimp [r_inf]
    linarith
  have h_rca := WeldedHierarchy.bdlWeldedCode_inf_cone_acyclicity k x_center hr_inf0 hr_inf_hi
  have hb_coords := hasBounded3DCoords_bdlWeldedBundled k
  have hL := bdlCoordBound_add_1000_le_half_L k
  refine ⟨?_, ?_⟩
  · intro a ha_supp ha_comm
    let z1 : BDLWeldedQubit k → ZMod 2 := fun q => a (bdlQubitSiteSlot k q)
    have hz1_supp : ∀ q, z1 q ≠ 0 → q ∈ ballQ (bdlWeldedCode k) x_center r_inf := by
      intro q hq_ne
      have h_in_A : (bdlQubitSiteSlot k q).1 ∈ A := ha_supp (bdlQubitSiteSlot k q) hq_ne
      have h_fst : (bdlQubitSiteSlot k q).1 = bdlGridVertexQ k q :=
        congr_arg Prod.fst (bdlQubitSiteSlot_eq k q)
      rw [h_fst] at h_in_A
      exact snapPointToOpenBox_mem_boxCube_imp_distInf3D_le hL (hb_coords.1 q) x0 r h_in_A
    have hz1_syn : syndrome (bdlWeldedCode k) z1 = 0 := by
      ext mX
      have h_lt : (bdlCheckXSlot k mX).2.val <
          (bdlLocalDescriptor k (bdlCheckXSlot k mX).1).numXChecks.val := by
        rw [numXChecks_val_eq_card_fiber]
        exact bdlCheckXLocalRank_lt_card k mX
      have h_comm := ha_comm (bdlCheckXSlot k mX).1 (bdlCheckXSlot k mX).2 h_lt
      have h_sum_eq :
          (∑ p : BoxSlot3D (bdlBoxSide k) qCodeBDL,
            a p * descriptorCheckXChain (bdlLocalDescriptor k)
              (bdlCheckXSlot k mX).1 (bdlCheckXSlot k mX).2 p) =
          syndrome (bdlWeldedCode k) z1 mX := by
        refine (Finset.sum_subset (Finset.subset_univ (Finset.univ.image (bdlQubitSiteSlot k))) ?_).symm.trans ?_
        · intro p _ hp
          rw [descriptorCheckXChain_eq_zero_of_not_mem_image' k _ _ p hp, mul_zero]
        · rw [Finset.sum_image (fun q₁ _ q₂ _ h => bdlQubitSiteSlot_injective k h)]
          dsimp [syndrome, f2Syndrome, z1, bdlCheckXSlot]
          apply Finset.sum_congr rfl
          intro q _
          rw [descriptorCheckXChain_bdlQubitSiteSlot_eq k mX _ rfl q, mul_comm]
      exact h_sum_eq.symm.trans h_comm
    obtain ⟨c2, hc2_gen, hc2_supp⟩ := h_rca.1 z1 hz1_syn hz1_supp
    let c_pin : Box3D (bdlBoxSide k) × Fin qCodeBDL → ZMod 2 :=
      fun p => if (bdlLocalDescriptor k p.1).activeSlot p.2 = false then a p else 0
    let c_Z : Box3D (bdlBoxSide k) × Fin mMaxBDL → ZMod 2 :=
      fun p => ∑ mZ : BDLWeldedCheckZ k, if bdlCheckZSlot k mZ = p then c2 mZ else 0
    refine ⟨c_pin, c_Z, ?_, ?_, ?_⟩
    · intro p hp_ne
      dsimp [c_pin] at hp_ne
      split_ifs at hp_ne with h_inact
      · exact ⟨h_inact, boxCube_subset_enclosingBoxCube k x0 hr1 (ha_supp p hp_ne)⟩
      · exact False.elim (hp_ne rfl)
    · intro p hp_ne
      obtain ⟨mZ, _, hmZ_ne⟩ := Finset.exists_ne_zero_of_sum_ne_zero hp_ne
      split_ifs at hmZ_ne with h_slot
      · subst h_slot
        refine ⟨?_, ?_⟩
        · rw [numZChecks_val_eq_card_fiber]
          exact bdlCheckZLocalRank_lt_card k mZ
        · exact snapPointToOpenBox_boxBall_subset_enclosingBoxCube k x0 hr1
            (hb_coords.2.1 mZ) (hc2_supp mZ hmZ_ne)
      · exact False.elim (hmZ_ne rfl)
    · ext p0
      simp only [Pi.add_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
      have h_pin_eval :
          (∑ p : Box3D (bdlBoxSide k) × Fin qCodeBDL, c_pin p * singleSlotChain p.1 p.2 p0) =
          c_pin p0 := by
        rw [Finset.sum_eq_single p0]
        · dsimp [singleSlotChain]; rw [if_pos rfl, mul_one]
        · intro p _ hne
          dsimp [singleSlotChain]
          rw [if_neg (Ne.symm hne), mul_zero]
        · intro h_abs; exact False.elim (h_abs (Finset.mem_univ p0))
      have h_cZ_eval :
          (∑ p : Box3D (bdlBoxSide k) × Fin mMaxBDL,
            c_Z p * descriptorCheckZChain (bdlLocalDescriptor k) p.1 p.2 p0) =
          ∑ mZ : BDLWeldedCheckZ k,
            c2 mZ * descriptorCheckZChain (bdlLocalDescriptor k)
              (bdlCheckZSlot k mZ).1 (bdlCheckZSlot k mZ).2 p0 := by
        dsimp [c_Z]
        simp_rw [Finset.sum_mul]
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro mZ _
        simp_rw [ite_mul, zero_mul]
        rw [Finset.sum_ite_eq]
        simp
      rw [h_pin_eval, h_cZ_eval]
      by_cases h_act : (bdlLocalDescriptor k p0.1).activeSlot p0.2 = true
      · have hp0_pin : c_pin p0 = 0 := by
          dsimp [c_pin]; rw [if_neg (by rw [h_act]; decide)]
        rw [hp0_pin, zero_add]
        have hp0_mem := (activeSlot_eq_true_iff_mem_image_bdlQubitSiteSlot k p0).mp h_act
        rcases Finset.mem_image.mp hp0_mem with ⟨q, _, rfl⟩
        have h_gen_q := congr_fun hc2_gen q
        dsimp [checkGen, f2CheckGen, z1] at h_gen_q
        rw [← h_gen_q]
        apply Finset.sum_congr rfl
        intro mZ _
        dsimp [bdlCheckZSlot]
        rw [descriptorCheckZChain_bdlQubitSiteSlot_eq k mZ _ rfl q, mul_comm]
      · have h_inact : (bdlLocalDescriptor k p0.1).activeSlot p0.2 = false :=
          Bool.eq_false_iff.mpr h_act
        have hp0_pin : c_pin p0 = a p0 := by
          dsimp [c_pin]; rw [if_pos h_inact]
        have hp0_not_mem : p0 ∉ Finset.univ.image (bdlQubitSiteSlot k) :=
          fun hm => h_act ((activeSlot_eq_true_iff_mem_image_bdlQubitSiteSlot k p0).mpr hm)
        have h_sum_zero :
            (∑ mZ : BDLWeldedCheckZ k,
              c2 mZ * descriptorCheckZChain (bdlLocalDescriptor k)
                (bdlCheckZSlot k mZ).1 (bdlCheckZSlot k mZ).2 p0) = 0 := by
          apply Finset.sum_eq_zero
          intro mZ _
          rw [descriptorCheckZChain_eq_zero_of_not_mem_image' k _ _ p0 hp0_not_mem, mul_zero]
        rw [hp0_pin, h_sum_zero, add_zero]
  · intro b hb_supp hb_act hb_comm
    let b1 : BDLWeldedQubit k → ZMod 2 := fun q => b (bdlQubitSiteSlot k q)
    have hb1_supp : ∀ q, b1 q ≠ 0 → q ∈ ballQ (bdlWeldedCode k) x_center r_inf := by
      intro q hq_ne
      have h_in_A : (bdlQubitSiteSlot k q).1 ∈ A := hb_supp (bdlQubitSiteSlot k q) hq_ne
      have h_fst : (bdlQubitSiteSlot k q).1 = bdlGridVertexQ k q :=
        congr_arg Prod.fst (bdlQubitSiteSlot_eq k q)
      rw [h_fst] at h_in_A
      exact snapPointToOpenBox_mem_boxCube_imp_distInf3D_le hL (hb_coords.1 q) x0 r h_in_A
    have hb1_syn : syndrome (dualCode (bdlWeldedCode k)) b1 = 0 := by
      ext mZ
      have h_lt : (bdlCheckZSlot k mZ).2.val <
          (bdlLocalDescriptor k (bdlCheckZSlot k mZ).1).numZChecks.val := by
        rw [numZChecks_val_eq_card_fiber]
        exact bdlCheckZLocalRank_lt_card k mZ
      have h_comm := hb_comm (bdlCheckZSlot k mZ).1 (bdlCheckZSlot k mZ).2 h_lt
      have h_sum_eq :
          (∑ p : BoxSlot3D (bdlBoxSide k) qCodeBDL,
            b p * descriptorCheckZChain (bdlLocalDescriptor k)
              (bdlCheckZSlot k mZ).1 (bdlCheckZSlot k mZ).2 p) =
          syndrome (dualCode (bdlWeldedCode k)) b1 mZ := by
        refine (Finset.sum_subset (Finset.subset_univ (Finset.univ.image (bdlQubitSiteSlot k))) ?_).symm.trans ?_
        · intro p _ hp
          rw [descriptorCheckZChain_eq_zero_of_not_mem_image' k _ _ p hp, mul_zero]
        · rw [Finset.sum_image (fun q₁ _ q₂ _ h => bdlQubitSiteSlot_injective k h)]
          dsimp [syndrome, dualCode, f2Syndrome, dualF2ChainComplex, b1, bdlCheckZSlot]
          apply Finset.sum_congr rfl
          intro q _
          rw [descriptorCheckZChain_bdlQubitSiteSlot_eq k mZ _ rfl q, mul_comm]
      exact h_sum_eq.symm.trans h_comm
    obtain ⟨d2, hd2_gen, hd2_supp⟩ := h_rca.2 b1 hb1_syn hb1_supp
    let c_X : Box3D (bdlBoxSide k) × Fin mMaxBDL → ZMod 2 :=
      fun p => ∑ mX : BDLWeldedCheckX k, if bdlCheckXSlot k mX = p then d2 mX else 0
    refine ⟨c_X, ?_, ?_⟩
    · intro p hp_ne
      obtain ⟨mX, _, hmX_ne⟩ := Finset.exists_ne_zero_of_sum_ne_zero hp_ne
      split_ifs at hmX_ne with h_slot
      · subst h_slot
        refine ⟨?_, ?_⟩
        · rw [numXChecks_val_eq_card_fiber]
          exact bdlCheckXLocalRank_lt_card k mX
        · exact snapPointToOpenBox_boxBall_subset_enclosingBoxCube k x0 hr1
            (hb_coords.2.2 mX) (hd2_supp mX hmX_ne)
      · exact False.elim (hmX_ne rfl)
    · ext p0
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
      have h_cX_eval :
          (∑ p : Box3D (bdlBoxSide k) × Fin mMaxBDL,
            c_X p * descriptorCheckXChain (bdlLocalDescriptor k) p.1 p.2 p0) =
          ∑ mX : BDLWeldedCheckX k,
            d2 mX * descriptorCheckXChain (bdlLocalDescriptor k)
              (bdlCheckXSlot k mX).1 (bdlCheckXSlot k mX).2 p0 := by
        dsimp [c_X]
        simp_rw [Finset.sum_mul]
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro mX _
        simp_rw [ite_mul, zero_mul]
        rw [Finset.sum_ite_eq]
        simp
      rw [h_cX_eval]
      by_cases h_act : (bdlLocalDescriptor k p0.1).activeSlot p0.2 = true
      · have hp0_mem := (activeSlot_eq_true_iff_mem_image_bdlQubitSiteSlot k p0).mp h_act
        rcases Finset.mem_image.mp hp0_mem with ⟨q, _, rfl⟩
        have h_gen_q := congr_fun hd2_gen q
        dsimp [checkGen, dualCode, f2CheckGen, dualF2ChainComplex, b1] at h_gen_q
        rw [← h_gen_q]
        apply Finset.sum_congr rfl
        intro mX _
        dsimp [bdlCheckXSlot]
        rw [descriptorCheckXChain_bdlQubitSiteSlot_eq k mX _ rfl q, mul_comm]
      · have hp0_b : b p0 = 0 := by
          by_contra hb_ne
          exact h_act (hb_act p0 hb_ne)
        have hp0_not_mem : p0 ∉ Finset.univ.image (bdlQubitSiteSlot k) :=
          fun hm => h_act ((activeSlot_eq_true_iff_mem_image_bdlQubitSiteSlot k p0).mpr hm)
        rw [hp0_b]
        apply (Finset.sum_eq_zero ?_).symm
        intro mX _
        rw [descriptorCheckXChain_eq_zero_of_not_mem_image' k _ _ p0 hp0_not_mem, mul_zero]
