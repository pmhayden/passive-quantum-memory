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

import Defs.BHMStability
import Proofs.CubeTelescoping.LocalToGlobalNormTransfer

/-!
# Elementary Cube Defect Projectors and Coarse-Graining Hamiltonian Functor

Develops the algebra of local ground projectors on `IndexedCommutingProjectorHamiltonian`, defines the elementary `2^D`-cube defect projectors `indexedCubeDefectProj`, and constructs the coarse-graining functor `coarseCubeHamiltonian` to a `CommutingProjectorHamiltonian` preserving the global ground projector `P0`, TQO-1, and low-energy band stability.

## References

* Part I, Section 6.1 (`subsec:dsuper-banach`), Definition 6.1 (`def:banach-quasilocal`)
* Part I, Section 7.1 (`subsec:single-cube-telescoping`), Lemma 7.1 (`lem:norm-transfer`)
* Bravyi and Hastings (2011), Commun. Math. Phys. 307, 609–627
-/

noncomputable section

open scoped Classical InnerProduct ComplexConjugate BigOperators
open ContinuousLinearMap

/-!
## 1. Local Cube Defect Projector $Q_A = 1 - P_A$ and Coarse-Grained `CommutingProjectorHamiltonian`
-/

/-- Every local ground projector `sys.P_loc B` of an `IndexedCommutingProjectorHamiltonian` is a star projection. -/
lemma IndexedCommutingProjectorHamiltonian.isStarProjection_P_loc_bhm {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (sys : IndexedCommutingProjectorHamiltonian D L Site ι) (B : Finset (BoxD D L)) :
    IsStarProjection (sys.localGroundProj B) := by
  dsimp [IndexedCommutingProjectorHamiltonian.localGroundProj,
    IndexedCommutingProjectorHamiltonian.localGroundProj]
  set S := (Finset.univ : Finset ι).filter (fun i : ι => sys.support i ⊆ B)
  apply isStarProjection_list_prod_bhm
  · intro p hp
    rcases List.mem_map.mp hp with ⟨i, _, rfl⟩
    exact (sys.is_projector i).one_sub
  · rw [List.pairwise_map]
    refine List.Pairwise.imp_of_mem ?_ S.nodup_toList
    intro i j _ _ _
    exact commute_one_sub_right_bhm (commute_one_sub_left_bhm (sys.pairwise_commute i j))

/-- The global ground projector `sys.P0` of an `IndexedCommutingProjectorHamiltonian` is a star projection. -/
lemma IndexedCommutingProjectorHamiltonian.isStarProjection_P0 {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (sys : IndexedCommutingProjectorHamiltonian D L Site ι) :
    IsStarProjection sys.P0 := by
  dsimp [IndexedCommutingProjectorHamiltonian.P0, IndexedCommutingProjectorHamiltonian.groundProj]
  apply isStarProjection_list_prod_bhm
  · intro p hp
    rcases List.mem_map.mp hp with ⟨i, _, rfl⟩
    exact (sys.is_projector i).one_sub
  · rw [List.pairwise_map]
    refine List.Pairwise.imp_of_mem ?_ (Finset.univ : Finset ι).nodup_toList
    intro i j _ _ _
    exact commute_one_sub_right_bhm (commute_one_sub_left_bhm (sys.pairwise_commute i j))

/-- Every check $Q_i$ with $\mathrm{supp}(Q_i) \subseteq B$ is annihilated on the right by `sys.P_loc B`. -/
lemma IndexedCommutingProjectorHamiltonian.checkProj_mul_P_loc_eq_zero {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (sys : IndexedCommutingProjectorHamiltonian D L Site ι)
    (i : ι) (B : Finset (BoxD D L)) (hiB : sys.support i ⊆ B) :
    sys.checkProj i * sys.localGroundProj B = 0 := by
  dsimp [IndexedCommutingProjectorHamiltonian.localGroundProj,
    IndexedCommutingProjectorHamiltonian.localGroundProj]
  set S := (Finset.univ : Finset ι).filter (fun j : ι => sys.support j ⊆ B)
  have h_mem : 1 - sys.checkProj i ∈ S.toList.map (fun j => 1 - sys.checkProj j) := by
    apply List.mem_map_of_mem
    rw [Finset.mem_toList, Finset.mem_filter]
    exact ⟨Finset.mem_univ i, hiB⟩
  have h_sub : sys.checkProj i = 1 - (1 - sys.checkProj i) :=
    (sub_sub_cancel 1 (sys.checkProj i)).symm
  rw [h_sub]
  apply one_sub_mul_list_prod_eq_zero_bhm _ (1 - sys.checkProj i) h_mem
    (sys.is_projector i).one_sub.isIdempotentElem
  intro q hq
  rcases List.mem_map.mp hq with ⟨j, _, rfl⟩
  exact commute_one_sub_right_bhm (commute_one_sub_left_bhm (sys.pairwise_commute i j))

/-- Every local ground projector `sys.P_loc B` commutes with every check projector `sys.checkProj i`. -/
lemma IndexedCommutingProjectorHamiltonian.commute_P_loc_checkProj {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (sys : IndexedCommutingProjectorHamiltonian D L Site ι)
    (B : Finset (BoxD D L)) (i : ι) :
    Commute (sys.localGroundProj B) (sys.checkProj i) := by
  dsimp [IndexedCommutingProjectorHamiltonian.localGroundProj,
    IndexedCommutingProjectorHamiltonian.localGroundProj]
  apply Commute.list_prod_left
  intro p hp
  rcases List.mem_map.mp hp with ⟨j, _, rfl⟩
  exact commute_one_sub_left_bhm (sys.pairwise_commute j i)

/-- Local ground projectors `sys.P_loc A` and `sys.P_loc B` of an `IndexedCommutingProjectorHamiltonian` commute. -/
lemma IndexedCommutingProjectorHamiltonian.commute_P_loc {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (sys : IndexedCommutingProjectorHamiltonian D L Site ι)
    (A B : Finset (BoxD D L)) :
    Commute (sys.localGroundProj A) (sys.localGroundProj B) := by
  dsimp [IndexedCommutingProjectorHamiltonian.localGroundProj,
    IndexedCommutingProjectorHamiltonian.localGroundProj]
  apply Commute.list_prod_right
  intro p hp
  rcases List.mem_map.mp hp with ⟨i, _, rfl⟩
  exact commute_one_sub_right_bhm (sys.commute_P_loc_checkProj A i)

/-- For nested regions $B_1 \subseteq B_2$, `sys.P_loc B₁` absorbs `sys.P_loc B₂` on both sides. -/
lemma IndexedCommutingProjectorHamiltonian.localProj_mul_localProj_of_subset_bhm {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (sys : IndexedCommutingProjectorHamiltonian D L Site ι)
    {B₁ B₂ : Finset (BoxD D L)} (hSub : B₁ ⊆ B₂) :
    sys.localGroundProj B₁ * sys.localGroundProj B₂ = sys.localGroundProj B₂ ∧
    sys.localGroundProj B₂ * sys.localGroundProj B₁ = sys.localGroundProj B₂ := by
  have h_left : sys.localGroundProj B₁ * sys.localGroundProj B₂ = sys.localGroundProj B₂ := by
    dsimp [IndexedCommutingProjectorHamiltonian.localGroundProj,
      IndexedCommutingProjectorHamiltonian.localGroundProj]
    apply list_prod_mul_eq_right_bhm
    intro p hp
    rcases List.mem_map.mp hp with ⟨i, hi_mem, rfl⟩
    have hiB1 : sys.support i ⊆ B₁ :=
      (Finset.mem_filter.mp (Finset.mem_toList.mp hi_mem)).2
    have hiB2 : sys.support i ⊆ B₂ := Finset.Subset.trans hiB1 hSub
    have h_zero : sys.checkProj i * sys.localGroundProj B₂ = 0 :=
      sys.checkProj_mul_P_loc_eq_zero i B₂ hiB2
    change (1 - sys.checkProj i) * sys.localGroundProj B₂ = sys.localGroundProj B₂
    rw [sub_mul, one_mul, h_zero, sub_zero]
  exact ⟨h_left, (sys.commute_P_loc B₂ B₁).eq.trans h_left⟩

/-- `sys.P_loc Finset.univ = sys.P0`. -/
lemma IndexedCommutingProjectorHamiltonian.localProj_univ_eq_proj0 {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (sys : IndexedCommutingProjectorHamiltonian D L Site ι) :
    sys.localGroundProj Finset.univ = sys.P0 := by
  dsimp [IndexedCommutingProjectorHamiltonian.localGroundProj,
    IndexedCommutingProjectorHamiltonian.localGroundProj,
    IndexedCommutingProjectorHamiltonian.P0,
    IndexedCommutingProjectorHamiltonian.groundProj]
  have h_filter : (Finset.univ : Finset ι).filter (fun i : ι => sys.support i ⊆ Finset.univ) =
      Finset.univ := by
    ext i
    simp [Finset.subset_univ]
  rw [h_filter]

/-- For any region $B \subseteq \mathrm{BoxD}\ D\ L$, `sys.P_loc B` absorbs `sys.P0` on both sides. -/
lemma IndexedCommutingProjectorHamiltonian.localProj_mul_proj0_eq_proj0 {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (sys : IndexedCommutingProjectorHamiltonian D L Site ι) (B : Finset (BoxD D L)) :
    sys.localGroundProj B * sys.P0 = sys.P0 ∧ sys.P0 * sys.localGroundProj B = sys.P0 := by
  rw [← sys.localProj_univ_eq_proj0]
  exact sys.localProj_mul_localProj_of_subset_bhm (Finset.subset_univ B)

/-- For an `IndexedCommutingProjectorHamiltonian sys` on `BoxD D L`, the elementary $2$-cube defect
    projector on $A \in \mathrm{BoxCubes}\ D\ L\ 2$ is $Q_A := 1 - \mathrm{sys.P\_loc}\ A$. -/
def indexedCubeDefectProj {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (sys : IndexedCommutingProjectorHamiltonian D L Site ι)
    (A : Finset (BoxD D L)) :
    ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site :=
  if A ∈ boxCubes D L 2 then 1 - sys.localGroundProj A else 0

/-- Every `indexedCubeDefectProj sys A` for $A \in \mathrm{BoxCubes}\ D\ L\ 2$ is an orthogonal
    projector supported on $A$, and the family pairwise commutes. -/
lemma indexedCubeDefectProj_properties {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (sys : IndexedCommutingProjectorHamiltonian D L Site ι) :
    (∀ A ∈ boxCubes D L 2, IsStarProjection (indexedCubeDefectProj sys A)) ∧
    (∀ A ∈ boxCubes D L 2, IsSupportedOn Site A (indexedCubeDefectProj sys A)) ∧
    (∀ A ∈ boxCubes D L 2, ∀ B ∈ boxCubes D L 2,
      Commute (indexedCubeDefectProj sys A) (indexedCubeDefectProj sys B)) := by
  refine ⟨?_, ?_, ?_⟩
  · intro A hA
    dsimp [indexedCubeDefectProj]
    rw [if_pos hA]
    exact (sys.isStarProjection_P_loc_bhm A).one_sub
  · intro A hA
    dsimp [indexedCubeDefectProj]
    rw [if_pos hA]
    exact isSupportedOn_sub A (isSupportedOn_one A) (sys.isSupportedOn_P_loc A)
  · intro A hA B hB
    dsimp [indexedCubeDefectProj]
    rw [if_pos hA, if_pos hB]
    exact commute_one_sub_right_bhm (commute_one_sub_left_bhm (sys.commute_P_loc A B))

/-- If $p \in l$ and every element of $l$ commutes with $q$, and $q \cdot p = 0$, then $q \cdot \prod l = 0$. -/
lemma mul_list_prod_eq_zero_of_mem {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [CompleteSpace E] (l : List (E →L[ℂ] E)) (p q : E →L[ℂ] E)
    (hp_mem : p ∈ l) (hq_p : q * p = 0)
    (hq_comm : ∀ r ∈ l, Commute q r) :
    q * l.prod = 0 := by
  induction l with
  | nil => cases hp_mem
  | cons r tail ih =>
    rw [List.prod_cons, ← mul_assoc]
    rcases List.mem_cons.mp hp_mem with rfl | hp_tail
    · rw [hq_p, zero_mul]
    · rw [(hq_comm r List.mem_cons_self).eq, mul_assoc,
        ih hp_tail (fun s hs => hq_comm s (List.mem_cons_of_mem r hs)), mul_zero]

/-- Under `h_cube_cov : ∀ i : ι, ∃ A ∈ BoxCubes D L 2, sys.support i ⊆ A`, the global ground projector
    `globalGroundProjector (indexedCubeDefectProj sys)` equals `sys.P0`. -/
lemma globalGroundProjector_indexedCubeDefectProj_eq_P0 {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (sys : IndexedCommutingProjectorHamiltonian D L Site ι)
    (h_cube_cov : ∀ i : ι, ∃ A ∈ boxCubes D L 2, sys.support i ⊆ A) :
    globalGroundProjector (indexedCubeDefectProj sys) = sys.P0 := by
  set P_cube := globalGroundProjector (indexedCubeDefectProj sys)
  have h1 : P_cube * sys.P0 = sys.P0 := by
    dsimp [P_cube, globalGroundProjector, localGroundProjector]
    apply list_prod_mul_eq_right_bhm
    intro p hp
    rcases List.mem_map.mp hp with ⟨A, hA_mem, rfl⟩
    have hA_cube : A ∈ boxCubes D L 2 :=
      (Finset.mem_filter.mp (Finset.mem_toList.mp hA_mem)).1
    dsimp [indexedCubeDefectProj]
    rw [if_pos hA_cube, sub_sub_cancel]
    exact (sys.localProj_mul_proj0_eq_proj0 A).1
  have h2 : sys.P0 * P_cube = P_cube := by
    dsimp [IndexedCommutingProjectorHamiltonian.P0,
      IndexedCommutingProjectorHamiltonian.groundProj]
    apply list_prod_mul_eq_right_bhm
    intro p hp
    rcases List.mem_map.mp hp with ⟨i, _, rfl⟩
    rcases h_cube_cov i with ⟨A, hA_cube, hiA⟩
    have h_zero : sys.checkProj i * P_cube = 0 := by
      dsimp [P_cube, globalGroundProjector, localGroundProjector]
      set S := (boxCubes D L 2).filter (fun C => C ⊆ Finset.univ)
      have h_mem : 1 - indexedCubeDefectProj sys A ∈
          S.toList.map (fun C => 1 - indexedCubeDefectProj sys C) := by
        apply List.mem_map_of_mem
        rw [Finset.mem_toList, Finset.mem_filter]
        exact ⟨hA_cube, Finset.subset_univ A⟩
      have hq_p : sys.checkProj i * (1 - indexedCubeDefectProj sys A) = 0 := by
        dsimp [indexedCubeDefectProj]
        rw [if_pos hA_cube, sub_sub_cancel]
        exact sys.checkProj_mul_P_loc_eq_zero i A hiA
      apply mul_list_prod_eq_zero_of_mem _ (1 - indexedCubeDefectProj sys A) (sys.checkProj i)
        h_mem hq_p
      intro r hr
      rcases List.mem_map.mp hr with ⟨C, hC_mem, rfl⟩
      have hC_cube : C ∈ boxCubes D L 2 :=
        (Finset.mem_filter.mp (Finset.mem_toList.mp hC_mem)).1
      dsimp [indexedCubeDefectProj]
      rw [if_pos hC_cube, sub_sub_cancel]
      exact (sys.commute_P_loc_checkProj C i).symm
    change (1 - sys.checkProj i) * P_cube = P_cube
    rw [sub_mul, one_mul, h_zero, sub_zero]
  have h_comm : Commute P_cube sys.P0 := by
    dsimp [P_cube, globalGroundProjector, localGroundProjector]
    apply Commute.list_prod_left
    intro p hp
    rcases List.mem_map.mp hp with ⟨A, hA_mem, rfl⟩
    have hA_cube : A ∈ boxCubes D L 2 :=
      (Finset.mem_filter.mp (Finset.mem_toList.mp hA_mem)).1
    dsimp [indexedCubeDefectProj]
    rw [if_pos hA_cube, sub_sub_cancel, ← sys.localProj_univ_eq_proj0]
    exact sys.commute_P_loc A Finset.univ
  calc P_cube
    _ = sys.P0 * P_cube := h2.symm
    _ = P_cube * sys.P0 := h_comm.symm.eq
    _ = sys.P0 := h1

/-- Coarse-grained $2^D$-cube `CommutingProjectorHamiltonian` associated to an
    `IndexedCommutingProjectorHamiltonian` whose checks are each supported inside some $2$-cube. -/
def coarseCubeHamiltonian {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (sys : IndexedCommutingProjectorHamiltonian D L Site ι)
    (h_cube_cov : ∀ i : ι, ∃ A ∈ boxCubes D L 2, sys.support i ⊆ A) :
    CommutingProjectorHamiltonian D L Site where
  Q := indexedCubeDefectProj sys
  is_projector := (indexedCubeDefectProj_properties sys).1
  is_supported := (indexedCubeDefectProj_properties sys).2.1
  pairwise_commute := (indexedCubeDefectProj_properties sys).2.2
  frustration_free := by
    rw [globalGroundProjector_indexedCubeDefectProj_eq_P0 sys h_cube_cov]
    exact sys.frustration_free

/-- The global ground projector of `coarseCubeHamiltonian sys h_cube_cov` equals `sys.P0`. -/
lemma coarseCubeHamiltonian_P_eq_P0 {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (sys : IndexedCommutingProjectorHamiltonian D L Site ι)
    (h_cube_cov : ∀ i : ι, ∃ A ∈ boxCubes D L 2, sys.support i ⊆ A) :
    (coarseCubeHamiltonian sys h_cube_cov).P = sys.P0 :=
  globalGroundProjector_indexedCubeDefectProj_eq_P0 sys h_cube_cov

/-- `coarseCubeHamiltonian sys h_cube_cov` preserves `SatisfiesTQO1`. -/
lemma coarseCubeHamiltonian_satisfiesTQO1 {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (sys : IndexedCommutingProjectorHamiltonian D L Site ι)
    {L_star : ℕ}
    (h_cube_cov : ∀ i : ι, ∃ A ∈ boxCubes D L 2, sys.support i ⊆ A)
    (hTQO1 : SatisfiesTQO1 sys L_star) :
    (coarseCubeHamiltonian sys h_cube_cov).SatisfiesTQO1 L_star := by
  unfold CommutingProjectorHamiltonian.SatisfiesTQO1 SatisfiesTQO1 at *
  rw [coarseCubeHamiltonian_P_eq_P0 sys h_cube_cov]
  exact hTQO1

/-- **Coarse-Grained Cube Hamiltonian Reduction (`coarseCubeReduction_transfers_stability`)**:
    When every check support `sys.support i` is contained in some $2$-cube $A \in \mathrm{BoxCubes}\ D\ L\ 2$,
    the $2$-cube defect projectors `indexedCubeDefectProj sys` form a frustration-free
    `CommutingProjectorHamiltonian D L Site` with the exact same global ground projector
    (`(coarseCubeHamiltonian sys h_cube_cov).P = sys.P0`) and preserve `SatisfiesTQO1`. -/
theorem coarseCubeReduction_transfers_stability {D L : ℕ} [NeZero D] [NeZero L]
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (sys : IndexedCommutingProjectorHamiltonian D L Site ι)
    {L_star : ℕ}
    (h_cube_cov : ∀ i : ι, ∃ A ∈ boxCubes D L 2, sys.support i ⊆ A)
    (hTQO1 : SatisfiesTQO1 sys L_star) :
    (coarseCubeHamiltonian sys h_cube_cov).P = sys.P0 ∧
    (coarseCubeHamiltonian sys h_cube_cov).SatisfiesTQO1 L_star :=
  ⟨coarseCubeHamiltonian_P_eq_P0 sys h_cube_cov,
   coarseCubeHamiltonian_satisfiesTQO1 sys h_cube_cov hTQO1⟩
