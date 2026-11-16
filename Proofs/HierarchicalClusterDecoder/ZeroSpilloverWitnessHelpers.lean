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

import Proofs.HierarchicalClusterDecoder.ClusterDecoderSynthesis

/-!
# Multiscale Check Graph Packages and Rooted Klarner Animal Counting

Formalizes padded spanning walks (`IsHierWalk`) and proves the rooted bounded-degree Klarner connected-subset bound (`card_connected_subsets_rooted_le`). Constructs the inductive multiscale check graph package `HierStepPkg` and witness invariant `IsHierClusterWitness`, proving linear multiscale support volume and exponential weight-shell bounds (`HierStepPkg.card_shell_le`) across primal and dual welded steps.

## References

* Part I, Section 5.3 (`subsec:walsh-fourier-peierls`), Lemma 5.4 (`lem:percolating-cluster-bounds`)
* Part II, Section 3.1 (`subsec:weyl-witness-poisson`), Lemma 3.3 (`lem:klarner-bound`)
* Part II, Section 4 (`subsec:welded-hierarchy-cleaner`), Definition 4.2 (`def:multiscale-cluster-decoder`), Lemma 4.4 (`lem:two-stage-cleaner-contraction`)
-/

noncomputable section

open scoped Classical
open BigOperators

set_option maxHeartbeats 800000
set_option linter.constructorNameAsVariable false

namespace WeldedHierarchy
namespace BDLDecoder

/-! ## 1. Spanning-Walk Splicing and Rooted Klarner Animal Counting Bound -/

/-- Set-restricted graph connectivity (`HierSetConnected`,
    Part II, Definition 4.2 (`def:multiscale-cluster-decoder`) and
    Theorem 5.1(iii) (`thm:direct-worldline-intact-cluster-erasure`)). -/
def HierSetConnected {V : Type} (Adj : V → V → Prop) (S : Finset V) : Prop :=
  ∀ u ∈ S, ∀ v ∈ S, Relation.ReflTransGen (fun a b => a ∈ S ∧ b ∈ S ∧ Adj a b) u v

/-- Inductive walk relation on `(V, Adj)` permitting self-loops `a = b` or edges `Adj a b`. -/
inductive IsHierWalk {V : Type} (Adj : V → V → Prop) : V → List V → V → Prop
  | nil (a : V) : IsHierWalk Adj a [] a
  | cons {a b c : V} {xs : List V} (h : Adj a b ∨ a = b) (hw : IsHierWalk Adj b xs c) :
      IsHierWalk Adj a (b :: xs) c

lemma IsHierWalk.append {V : Type} {Adj : V → V → Prop} {a b c : V} {xs ys : List V}
    (h1 : IsHierWalk Adj a xs b) (h2 : IsHierWalk Adj b ys c) :
    IsHierWalk Adj a (xs ++ ys) c := by
  induction h1 with
  | nil _ => exact h2
  | cons h _ ih => exact IsHierWalk.cons h (ih h2)

lemma IsHierWalk.split_at {V : Type} [DecidableEq V] {Adj : V → V → Prop} {a c u : V} {xs : List V}
    (hw : IsHierWalk Adj a xs c) (hu : u ∈ insert a xs.toFinset) :
    ∃ xs1 xs2 : List V, xs = xs1 ++ xs2 ∧ IsHierWalk Adj a xs1 u ∧ IsHierWalk Adj u xs2 c := by
  induction hw with
  | nil a =>
    simp only [List.toFinset_nil, Finset.insert_empty, Finset.mem_singleton] at hu
    subst hu
    exact ⟨[], [], rfl, IsHierWalk.nil _, IsHierWalk.nil _⟩
  | @cons a b c xs h hw ih =>
    by_cases hua : u = a
    · subst hua
      exact ⟨[], b :: xs, rfl, IsHierWalk.nil _, IsHierWalk.cons h hw⟩
    · have hu_next : u ∈ insert b xs.toFinset := by
        simp only [List.toFinset_cons, Finset.mem_insert] at hu ⊢
        rcases hu with rfl | rfl | hu_xs
        · exact False.elim (hua rfl)
        · exact Or.inl rfl
        · exact Or.inr hu_xs
      obtain ⟨xs1, xs2, rfl, hw1, hw2⟩ := ih hu_next
      exact ⟨b :: xs1, xs2, rfl, IsHierWalk.cons h hw1, hw2⟩

lemma exists_edge_across_cut {V : Type} [DecidableEq V] {Adj : V → V → Prop}
    {S T : Finset V} {r0 w : V}
    (h_path : Relation.ReflTransGen (fun a b => a ∈ S ∧ b ∈ S ∧ Adj a b) r0 w)
    (hr0 : r0 ∈ T) (hw : w ∉ T) :
    ∃ u ∈ T, ∃ v ∈ S, v ∉ T ∧ Adj u v := by
  induction h_path with
  | refl => exact False.elim (hw hr0)
  | @tail b c _ hstep ih =>
    by_cases hb : b ∈ T
    · exact ⟨b, hb, c, hstep.2.1, hw, hstep.2.2⟩
    · exact ih hb

lemma exists_closed_hierWalk_subset {V : Type} [DecidableEq V] {Adj : V → V → Prop}
    (h_symm : ∀ u v : V, Adj u v → Adj v u)
    {S : Finset V} (h_conn : HierSetConnected Adj S) {r0 : V} (hr0 : r0 ∈ S) :
    ∀ k : ℕ, k < S.card →
      ∃ (T : Finset V) (xs : List V),
        T ⊆ S ∧ r0 ∈ T ∧ T.card = k + 1 ∧
        IsHierWalk Adj r0 xs r0 ∧ xs.length = 2 * k ∧ insert r0 xs.toFinset = T := by
  intro k
  induction k with
  | zero =>
    intro _
    refine ⟨{r0}, [], Finset.singleton_subset_iff.mpr hr0, Finset.mem_singleton_self r0,
      Finset.card_singleton r0, IsHierWalk.nil r0, rfl, ?_⟩
    simp
  | succ m ih =>
    intro h_lt
    obtain ⟨T, xs, hT_sub, hr0_T, hT_card, h_walk, h_len, h_vis⟩ := ih (by omega)
    have h_not_sub : ¬ S ⊆ T := by
      intro h_sub
      have h_le := Finset.card_le_card h_sub
      omega
    obtain ⟨w, hw_S, hw_not_T⟩ := Finset.not_subset.mp h_not_sub
    obtain ⟨u, hu_T, v, hv_S, hv_not_T, huv⟩ :=
      exists_edge_across_cut (h_conn r0 hr0 w hw_S) hr0_T hw_not_T
    have hu_vis : u ∈ insert r0 xs.toFinset := by rw [h_vis]; exact hu_T
    obtain ⟨xs1, xs2, rfl, hw1, hw2⟩ := h_walk.split_at hu_vis
    let xs' : List V := xs1 ++ (v :: u :: xs2)
    have hw_detour : IsHierWalk Adj u (v :: u :: xs2) r0 :=
      IsHierWalk.cons (Or.inl huv) (IsHierWalk.cons (Or.inl (h_symm u v huv)) hw2)
    have h_walk' : IsHierWalk Adj r0 xs' r0 := hw1.append hw_detour
    have h_len' : xs'.length = 2 * (m + 1) := by
      dsimp [xs']
      simp only [List.length_append, List.length_cons] at h_len ⊢
      omega
    have h_vis' : insert r0 xs'.toFinset = insert v T := by
      rw [← h_vis]
      dsimp [xs']
      ext x
      simp only [List.toFinset_append, List.toFinset_cons, Finset.mem_insert, Finset.mem_union]
      constructor
      · rintro (rfl | hx1 | rfl | rfl | hx2)
        · exact Or.inr (Or.inl rfl)
        · exact Or.inr (Or.inr (Or.inl hx1))
        · exact Or.inl rfl
        · simp only [List.toFinset_append, Finset.mem_insert, Finset.mem_union] at hu_vis
          exact Or.inr hu_vis
        · exact Or.inr (Or.inr (Or.inr hx2))
      · rintro (rfl | rfl | hx1 | hx2)
        · exact Or.inr (Or.inr (Or.inl rfl))
        · exact Or.inl rfl
        · exact Or.inr (Or.inl hx1)
        · exact Or.inr (Or.inr (Or.inr (Or.inr hx2)))
    refine ⟨insert v T, xs', Finset.insert_subset_iff.mpr ⟨hv_S, hT_sub⟩,
      Finset.mem_insert_of_mem hr0_T, ?_, h_walk', h_len', h_vis'⟩
    rw [Finset.card_insert_of_notMem hv_not_T, hT_card]

lemma exists_padded_hierWalk {V : Type} [DecidableEq V] {Adj : V → V → Prop}
    (h_symm : ∀ u v : V, Adj u v → Adj v u)
    {S : Finset V} (h_conn : HierSetConnected Adj S) {r0 : V} (hr0 : r0 ∈ S)
    {L : ℕ} (hL : 2 * (S.card - 1) ≤ L) :
    ∃ xs : List V, IsHierWalk Adj r0 xs r0 ∧ xs.length = L ∧ insert r0 xs.toFinset = S := by
  have h_pos : 0 < S.card := Finset.card_pos.mpr ⟨r0, hr0⟩
  obtain ⟨T, xs0, hT_sub, _, hT_card, h_walk0, h_len0, h_vis0⟩ :=
    exists_closed_hierWalk_subset h_symm h_conn hr0 (S.card - 1) (by omega)
  have hT_eq : T = S := Finset.eq_of_subset_of_card_le hT_sub (by omega)
  subst hT_eq
  let d := L - xs0.length
  have h_pad : ∀ n : ℕ, IsHierWalk Adj r0 (List.replicate n r0 ++ xs0) r0 ∧
      insert r0 (List.replicate n r0 ++ xs0).toFinset = insert r0 xs0.toFinset := by
    intro n
    induction n with
    | zero => exact ⟨h_walk0, rfl⟩
    | succ n ih =>
      refine ⟨IsHierWalk.cons (Or.inr rfl) ih.1, ?_⟩
      ext x
      simp only [List.replicate_succ, List.cons_append, List.toFinset_cons, Finset.mem_insert]
      have h_ih := Finset.ext_iff.mp ih.2 x
      simp only [Finset.mem_insert] at h_ih
      tauto
  refine ⟨List.replicate d r0 ++ xs0, (h_pad d).1, ?_, (h_pad d).2.trans h_vis0⟩
  simp only [List.length_append, List.length_replicate]
  omega

/-- Finite set of walks of length `n` starting from `u : V` under neighbor function `nexts`. -/
def hierWalksOfLength {V : Type} [DecidableEq V] (nexts : V → Finset V) : ℕ → V → Finset (List V)
  | 0, _ => {[]}
  | n + 1, u =>
      (nexts u).biUnion (fun v =>
        (hierWalksOfLength nexts n v).map ⟨List.cons v, fun _ _ h => (List.cons.inj h).2⟩)

lemma mem_hierWalksOfLength_of_isHierWalk {V : Type} [Fintype V] [DecidableEq V]
    (Adj : V → V → Prop) :
    ∀ {n : ℕ} {a c : V} {xs : List V},
      IsHierWalk Adj a xs c → xs.length = n →
      xs ∈ hierWalksOfLength (fun u => insert u (Finset.univ.filter (fun v => Adj u v))) n a
  | 0, a, _, _, IsHierWalk.nil _, _ => Finset.mem_singleton_self []
  | n + 1, a, _, _, IsHierWalk.cons (b := b) (xs := xs) h hw, hlen => by
      dsimp [hierWalksOfLength]
      rw [Finset.mem_biUnion]
      refine ⟨b, ?_, ?_⟩
      · rw [Finset.mem_insert, Finset.mem_filter]
        rcases h with hab | rfl
        · exact Or.inr ⟨Finset.mem_univ b, hab⟩
        · exact Or.inl rfl
      · rw [Finset.mem_map]
        exact ⟨xs, mem_hierWalksOfLength_of_isHierWalk Adj hw (by simpa using hlen), rfl⟩

lemma card_hierWalksOfLength_le {V : Type} [DecidableEq V] (nexts : V → Finset V) (B : ℕ)
    (hB : ∀ u : V, (nexts u).card ≤ B) :
    ∀ (n : ℕ) (u : V), (hierWalksOfLength nexts n u).card ≤ B ^ n
  | 0, _ => by simp [hierWalksOfLength]
  | n + 1, u => by
      dsimp [hierWalksOfLength]
      calc ((nexts u).biUnion (fun v =>
            (hierWalksOfLength nexts n v).map ⟨List.cons v, fun _ _ h => (List.cons.inj h).2⟩)).card
        _ ≤ ∑ v ∈ nexts u, ((hierWalksOfLength nexts n v).map
              ⟨List.cons v, fun _ _ h => (List.cons.inj h).2⟩).card := Finset.card_biUnion_le
        _ = ∑ v ∈ nexts u, (hierWalksOfLength nexts n v).card :=
              Finset.sum_congr rfl (fun _ _ => Finset.card_map _)
        _ ≤ ∑ _v ∈ nexts u, B ^ n :=
              Finset.sum_le_sum (fun v _ => card_hierWalksOfLength_le nexts B hB n v)
        _ = (nexts u).card * B ^ n := by rw [Finset.sum_const, smul_eq_mul]
        _ ≤ B * B ^ n := Nat.mul_le_mul_right (B ^ n) (hB u)
        _ = B ^ (n + 1) := by ring

/-- **Klarner Spanning-Walk Bound on Rooted Connected Subgraphs (`card_connected_subsets_rooted_le`,
    Part II, Lemma 3.3 (`lem:klarner-bound`), Equation (29) (`eq:klarner-rooted`), and
    Theorem 5.1(iii) (`thm:direct-worldline-intact-cluster-erasure`))**:
    On any finite graph `(V, Adj)` with symmetric adjacency and maximum degree `≤ D`, the number of
    connected subsets `S ⊆ V` of size `1 ≤ |S| ≤ K` intersecting a root set `R ⊆ V` is at most
    `|R| * (D + 1) ^ (2 * K)`. -/
theorem card_connected_subsets_rooted_le {V : Type} [Fintype V] [DecidableEq V]
    (Adj : V → V → Prop) (h_symm : ∀ u v : V, Adj u v → Adj v u)
    (R : Finset V) (D K : ℕ)
    (h_deg : ∀ u : V, (Finset.univ.filter (fun v => Adj u v)).card ≤ D)
    (F_set : Finset (Finset V))
    (h_sub : ∀ S ∈ F_set, (S ∩ R).Nonempty ∧ S.card ≤ K ∧ HierSetConnected Adj S) :
    F_set.card ≤ R.card * (D + 1) ^ (2 * K) := by
  let nexts : V → Finset V := fun u => insert u (Finset.univ.filter (fun v => Adj u v))
  have h_nexts : ∀ u : V, (nexts u).card ≤ D + 1 := by
    intro u
    calc (insert u (Finset.univ.filter (fun v => Adj u v))).card
      _ ≤ (Finset.univ.filter (fun v => Adj u v)).card + 1 := Finset.card_insert_le _ _
      _ ≤ D + 1 := Nat.add_le_add_right (h_deg u) 1
  let WalkPool : Finset (Finset V) :=
    R.biUnion (fun r0 => (hierWalksOfLength nexts (2 * K) r0).image (fun xs => insert r0 xs.toFinset))
  have h_f_sub : F_set ⊆ WalkPool := by
    intro S hS
    obtain ⟨⟨r0, hr0_inter⟩, hS_card, hS_conn⟩ := h_sub S hS
    have hr0_S : r0 ∈ S := (Finset.mem_inter.mp hr0_inter).1
    have hr0_R : r0 ∈ R := (Finset.mem_inter.mp hr0_inter).2
    obtain ⟨xs, h_walk, h_len, h_vis⟩ :=
      exists_padded_hierWalk h_symm hS_conn hr0_S (L := 2 * K) (by omega)
    rw [Finset.mem_biUnion]
    refine ⟨r0, hr0_R, Finset.mem_image.mpr ⟨xs, ?_, h_vis⟩⟩
    exact mem_hierWalksOfLength_of_isHierWalk Adj h_walk h_len
  calc F_set.card
    _ ≤ WalkPool.card := Finset.card_le_card h_f_sub
    _ ≤ ∑ r0 ∈ R, ((hierWalksOfLength nexts (2 * K) r0).image (fun xs => insert r0 xs.toFinset)).card :=
          Finset.card_biUnion_le
    _ ≤ ∑ r0 ∈ R, (hierWalksOfLength nexts (2 * K) r0).card :=
          Finset.sum_le_sum (fun _ _ => Finset.card_image_le)
    _ ≤ ∑ _r0 ∈ R, (D + 1) ^ (2 * K) :=
          Finset.sum_le_sum (fun r0 _ => card_hierWalksOfLength_le nexts (D + 1) h_nexts (2 * K) r0)
    _ = R.card * (D + 1) ^ (2 * K) := by rw [Finset.sum_const, smul_eq_mul]

/-! ## 2. Active Two-Hop Pool Existence & Downward Degree Bound -/

/-- If `rxCleanedCoarseSyndrome pcode M S z0 ≠ 0`, then `fineTwoHopPool pcode M {z0}` contains at
    least one active fine check `mZ` with `S mZ ≠ 0`. -/
lemma exists_active_in_fineTwoHopPool_of_rxCleanedCoarseSyndrome_ne_zero
    {Q M_Z M_X : Type}
    [Fintype Q] [DecidableEq Q] [Fintype M_Z] [DecidableEq M_Z] [Fintype M_X] [DecidableEq M_X]
    (pcode : CSSCode3D Q M_Z M_X) (M : ℕ)
    (S : BDLStepXMZ pcode M → ZMod 2) (z0 : M_Z)
    (hz0 : rxCleanedCoarseSyndrome pcode M S z0 ≠ 0) :
    ∃ mZ ∈ fineTwoHopPool pcode M {z0}, S mZ ≠ 0 := by
  by_contra h_none
  push_neg at h_none
  let D_1 := dualCode (bdlCylinderStepX pcode M)
  let S1 := S + syndrome D_1 (cleanStage1X pcode M S)
  have h_cyl0 : ∀ x ∈ twoHopX pcode {z0}, cleanCylinderX pcode M S x = 0 := by
    intro x hx
    apply cleanCylinderX_eq_zero_of_restrictCX2_eq_zero
    ext mZ
    dsimp [restrictCX2, restrictStepXMZ]
    split_ifs with hmZ
    · have h_own : stepXMZOwnerTanner pcode M mZ = inVX x := Finset.mem_singleton.mp hmZ
      have hmZ_pool : mZ ∈ fineTwoHopPool pcode M {z0} := by
        rw [fineTwoHopPool, Finset.mem_filter]
        exact ⟨Finset.mem_univ _, by rw [h_own, inVX_mem_twoHopTannerOfZ_iff]; exact hx⟩
      exact h_none mZ hmZ_pool
    · rfl
  have h_star0 : ∀ q0 ∈ oneHopQ pcode {z0}, cleanStarQ pcode M S1 q0 = 0 := by
    intro q0 hq0
    apply cleanStarQ_eq_zero_of_restrictCQ2_eq_zero
    have h_S_q0 : restrictCQ2 pcode M q0 S = 0 := by
      ext mZ
      dsimp [restrictCQ2, restrictStepXMZ]
      split_ifs with hmZ
      · have h_own : stepXMZOwnerTanner pcode M mZ = inVQ q0 := Finset.mem_singleton.mp hmZ
        have hmZ_pool : mZ ∈ fineTwoHopPool pcode M {z0} := by
          rw [fineTwoHopPool, Finset.mem_filter]
          exact ⟨Finset.mem_univ _, by rw [h_own, inVQ_mem_twoHopTannerOfZ_iff]; exact hq0⟩
        exact h_none mZ hmZ_pool
      · rfl
    have h_s1_q0 : restrictCQ2 pcode M q0 (syndrome D_1 (cleanStage1X pcode M S)) = 0 := by
      dsimp [cleanStage1X]
      rw [map_sum (syndrome D_1)]
      ext mZ
      dsimp [restrictCQ2, restrictStepXMZ]
      split_ifs with hmZ
      · rw [Finset.sum_apply]
        apply Finset.sum_eq_zero; intro x _
        by_cases hx_chk : pcode.checkX x q0 = 0
        · have h0 := congr_fun (restrictCQ2_syndrome_eq_zero_of_support_cyl_checkX_eq_zero
            pcode M x q0 hx_chk (cleanCylinderX pcode M S x) (cleanCylinderX_support pcode M S x)) mZ
          dsimp [restrictCQ2, restrictStepXMZ] at h0
          rw [if_pos hmZ] at h0
          exact h0
        · have hx_two : x ∈ twoHopX pcode {z0} := by
            rw [twoHopX, Finset.mem_filter]
            exact ⟨Finset.mem_univ _, q0, hq0, hx_chk⟩
          rw [h_cyl0 x hx_two, map_zero, Pi.zero_apply]
      · rfl
    dsimp [S1]
    rw [restrictCQ2_add, h_S_q0, h_s1_q0, add_zero]
  apply hz0
  dsimp [rxCleanedCoarseSyndrome, cleanTwoStageRX]
  change S (Sum.inr (Sum.inr (z0, 0))) +
    syndrome D_1 (cleanStage1X pcode M S + cleanStage2Q pcode M S1) (Sum.inr (Sum.inr (z0, 0))) = 0
  rw [map_add, Pi.add_apply, syndrome_cleanStage1X_cz2_eq_zero, zero_add]
  have h_S_z0 : S (Sum.inr (Sum.inr (z0, 0))) = 0 := by
    apply h_none (Sum.inr (Sum.inr (z0, 0)))
    rw [fineTwoHopPool, Finset.mem_filter]
    refine ⟨Finset.mem_univ _, ?_⟩
    change inVZ z0 ∈ twoHopTannerOfZ pcode {z0}
    rw [inVZ_mem_twoHopTannerOfZ_iff]
    exact Finset.mem_singleton_self z0
  rw [h_S_z0, zero_add]
  dsimp [cleanStage2Q]
  rw [map_sum, Finset.sum_apply]
  apply Finset.sum_eq_zero; intro q0 _
  have h_exp : syndrome D_1 (cleanStarQ pcode M S1 q0) (Sum.inr (Sum.inr (z0, 0))) =
      exportQZ pcode M (cleanStarQ pcode M S1 q0) (z0, 0) := by
    unfold exportQZ
    rw [splitStepXQ_Q_cleanStarQ]
  rw [h_exp]
  by_contra h_nz
  have h_chk : pcode.checkZ z0 q0 ≠ 0 :=
    checkZ_ne_zero_of_exportQZ_cleanStarQ_ne_zero pcode M S1 q0 z0 0 h_nz
  have hq0_one : q0 ∈ oneHopQ pcode {z0} := by
    rw [oneHopQ, Finset.mem_filter]
    exact ⟨Finset.mem_univ _, z0, Finset.mem_singleton_self z0, h_chk⟩
  rw [h_star0 q0 hq0_one, exportQZ_apply] at h_nz
  exact h_nz (Finset.sum_eq_zero (fun _ _ => mul_zero _))

/-- Downward degree bound for `fineTwoHopPool`: each fine Z-check `a : BDLStepXMZ pcode M` belongs
    to `fineTwoHopPool pcode M {z0}` for at most `32` coarse Z-checks `z0 : M_Z`. -/
lemma card_filter_fineTwoHopPool_singleton_le_32
    {Q M_Z M_X : Type}
    [Fintype Q] [DecidableEq Q] [Fintype M_Z] [DecidableEq M_Z] [Fintype M_X] [DecidableEq M_X]
    (pcode : CSSCode3D Q M_Z M_X) (M : ℕ)
    (hdX : ∀ x : M_X, (Finset.univ.filter (fun q0 : Q => pcode.checkX x q0 ≠ 0)).card ≤ 8)
    (hdQZ : ∀ q0 : Q, (Finset.univ.filter (fun z0 : M_Z => pcode.checkZ z0 q0 ≠ 0)).card ≤ 4)
    (a : BDLStepXMZ pcode M) :
    (Finset.univ.filter (fun z0 : M_Z => a ∈ fineTwoHopPool pcode M {z0})).card ≤ 32 := by
  rcases h_own : stepXMZOwnerTanner pcode M a with x0 | (q0 | z1)
  · have h_sub : Finset.univ.filter (fun z0 : M_Z => a ∈ fineTwoHopPool pcode M {z0}) ⊆
        (Finset.univ.filter (fun q0 : Q => pcode.checkX x0 q0 ≠ 0)).biUnion
          (fun q0 => Finset.univ.filter (fun z0 : M_Z => pcode.checkZ z0 q0 ≠ 0)) := by
      intro z0 hz0
      rw [Finset.mem_filter, fineTwoHopPool, Finset.mem_filter] at hz0
      have hx0 : inVX x0 ∈ twoHopTannerOfZ pcode {z0} := by
        change Sum.inl x0 ∈ twoHopTannerOfZ pcode {z0}
        rw [← h_own]
        exact hz0.2.2
      rw [inVX_mem_twoHopTannerOfZ_iff, twoHopX, Finset.mem_filter] at hx0
      rcases hx0.2 with ⟨q0, hq0, hchkX⟩
      rw [oneHopQ, Finset.mem_filter] at hq0
      rcases hq0.2 with ⟨z0', hz0', hchkZ⟩
      rw [Finset.mem_singleton] at hz0'
      subst hz0'
      rw [Finset.mem_biUnion]
      exact ⟨q0, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hchkX⟩,
        Finset.mem_filter.mpr ⟨Finset.mem_univ _, hchkZ⟩⟩
    calc (Finset.univ.filter (fun z0 : M_Z => a ∈ fineTwoHopPool pcode M {z0})).card
      _ ≤ ((Finset.univ.filter (fun q0 : Q => pcode.checkX x0 q0 ≠ 0)).biUnion
            (fun q0 => Finset.univ.filter (fun z0 : M_Z => pcode.checkZ z0 q0 ≠ 0))).card :=
            Finset.card_le_card h_sub
      _ ≤ ∑ q0 ∈ Finset.univ.filter (fun q0 : Q => pcode.checkX x0 q0 ≠ 0),
            (Finset.univ.filter (fun z0 : M_Z => pcode.checkZ z0 q0 ≠ 0)).card :=
            Finset.card_biUnion_le
      _ ≤ ∑ _q0 ∈ Finset.univ.filter (fun q0 : Q => pcode.checkX x0 q0 ≠ 0), 4 :=
            Finset.sum_le_sum (fun q0 _ => hdQZ q0)
      _ = (Finset.univ.filter (fun q0 : Q => pcode.checkX x0 q0 ≠ 0)).card * 4 := by
            rw [Finset.sum_const, smul_eq_mul]
      _ ≤ 8 * 4 := Nat.mul_le_mul_right 4 (hdX x0)
      _ = 32 := rfl
  · have h_sub : Finset.univ.filter (fun z0 : M_Z => a ∈ fineTwoHopPool pcode M {z0}) ⊆
        Finset.univ.filter (fun z0 : M_Z => pcode.checkZ z0 q0 ≠ 0) := by
      intro z0 hz0
      rw [Finset.mem_filter, fineTwoHopPool, Finset.mem_filter] at hz0
      rw [Finset.mem_filter]
      have hq0 : inVQ q0 ∈ twoHopTannerOfZ pcode {z0} := by
        change Sum.inr (Sum.inl q0) ∈ twoHopTannerOfZ pcode {z0}
        rw [← h_own]
        exact hz0.2.2
      rw [inVQ_mem_twoHopTannerOfZ_iff, oneHopQ, Finset.mem_filter] at hq0
      rcases hq0.2 with ⟨z0', hz0', hchkZ⟩
      rw [Finset.mem_singleton] at hz0'
      subst hz0'
      exact ⟨Finset.mem_univ _, hchkZ⟩
    exact (Finset.card_le_card h_sub).trans ((hdQZ q0).trans (by omega))
  · have h_sub : Finset.univ.filter (fun z0 : M_Z => a ∈ fineTwoHopPool pcode M {z0}) ⊆ {z1} := by
      intro z0 hz0
      rw [Finset.mem_filter, fineTwoHopPool, Finset.mem_filter] at hz0
      have hz1 : inVZ z1 ∈ twoHopTannerOfZ pcode {z0} := by
        change Sum.inr (Sum.inr z1) ∈ twoHopTannerOfZ pcode {z0}
        rw [← h_own]
        exact hz0.2.2
      rw [inVZ_mem_twoHopTannerOfZ_iff, Finset.mem_singleton] at hz1
      exact Finset.mem_singleton.mpr hz1.symm
    exact (Finset.card_le_card h_sub).trans (by simp)

/-! ## 3. Unified Multiscale Graph Extension (`StepGraphAdj`) & Degree Bounds -/

/-- Single-step multiscale graph adjacency extension (`StepGraphAdj`,
    Part II, Definition 4.2 (`def:multiscale-cluster-decoder`) and
    Theorem 5.1(iii) (`thm:direct-worldline-intact-cluster-erasure`)). -/
def StepGraphAdj {V M_0 W : Type} (Adj_V : V → V → Prop) (ι : M_0 → V)
    (VertLink : M_0 → W → Prop) : (V ⊕ W) → (V ⊕ W) → Prop
  | Sum.inl u, Sum.inl v => Adj_V u v
  | Sum.inl u, Sum.inr b => ∃ x0 : M_0, ι x0 = u ∧ VertLink x0 b
  | Sum.inr a, Sum.inl v => ∃ x0 : M_0, ι x0 = v ∧ VertLink x0 a
  | Sum.inr a, Sum.inr b => ∃ x0 : M_0, VertLink x0 a ∧ VertLink x0 b

lemma stepGraphAdj_symm {V M_0 W : Type} {Adj_V : V → V → Prop} {ι : M_0 → V}
    {VertLink : M_0 → W → Prop} (h_symm : ∀ u v : V, Adj_V u v → Adj_V v u) :
    ∀ u v : V ⊕ W, StepGraphAdj Adj_V ι VertLink u v → StepGraphAdj Adj_V ι VertLink v u
  | Sum.inl u, Sum.inl v, h => h_symm u v h
  | Sum.inl _, Sum.inr _, ⟨x0, h1, h2⟩ => ⟨x0, h1, h2⟩
  | Sum.inr _, Sum.inl _, ⟨x0, h1, h2⟩ => ⟨x0, h1, h2⟩
  | Sum.inr _, Sum.inr _, ⟨x0, h1, h2⟩ => ⟨x0, h2, h1⟩

lemma card_filter_sum_eq {A B : Type} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
    (P : A ⊕ B → Prop) :
    (Finset.univ.filter P).card =
      (Finset.univ.filter (fun a : A => P (Sum.inl a))).card +
      (Finset.univ.filter (fun b : B => P (Sum.inr b))).card := by
  rw [Finset.card_filter, Finset.card_filter, Finset.card_filter, Fintype.sum_sum_type]

lemma card_filter_stepGraphAdj_inl_le {V M_0 W : Type}
    [Fintype V] [DecidableEq V] [Fintype M_0] [DecidableEq M_0] [Fintype W] [DecidableEq W]
    (Adj_V : V → V → Prop) (ι : M_0 → V) (h_inj : Function.Injective ι)
    (VertLink : M_0 → W → Prop)
    {D_top D_up : ℕ}
    (h_all : ∀ u : V, (Finset.univ.filter (fun v : V => Adj_V u v)).card ≤ D_top + D_up)
    (h_top : ∀ x0 : M_0, (Finset.univ.filter (fun v : V => Adj_V (ι x0) v)).card ≤ D_top)
    (h_up : ∀ x0 : M_0, (Finset.univ.filter (fun b : W => VertLink x0 b)).card ≤ D_up)
    (u : V) :
    (Finset.univ.filter (fun w : V ⊕ W => StepGraphAdj Adj_V ι VertLink (Sum.inl u) w)).card ≤
      D_top + D_up := by
  rw [card_filter_sum_eq]
  by_cases hex : ∃ x0 : M_0, ι x0 = u
  · rcases hex with ⟨x0, rfl⟩
    have h_w_sub : Finset.univ.filter (fun b : W =>
        StepGraphAdj Adj_V ι VertLink (Sum.inl (ι x0)) (Sum.inr b)) ⊆
        Finset.univ.filter (fun b : W => VertLink x0 b) := by
      intro b hb
      rw [Finset.mem_filter] at hb ⊢
      rcases hb.2 with ⟨x0', hx0', hlink⟩
      rw [h_inj hx0'] at hlink
      exact ⟨Finset.mem_univ _, hlink⟩
    exact Nat.add_le_add (h_top x0) ((Finset.card_le_card h_w_sub).trans (h_up x0))
  · have h_w_empty : Finset.univ.filter (fun b : W =>
        StepGraphAdj Adj_V ι VertLink (Sum.inl u) (Sum.inr b)) = ∅ := by
      rw [Finset.filter_eq_empty_iff]
      intro b _ ⟨x0, hx0, _⟩
      exact hex ⟨x0, hx0⟩
    rw [h_w_empty, Finset.card_empty, add_zero]
    exact h_all u

lemma card_filter_stepGraphAdj_inr_le {V M_0 W : Type}
    [Fintype V] [DecidableEq V] [Fintype M_0] [DecidableEq M_0] [Fintype W] [DecidableEq W]
    (Adj_V : V → V → Prop) (ι : M_0 → V)
    (VertLink : M_0 → W → Prop)
    {D_down D_up : ℕ}
    (h_down : ∀ a : W, (Finset.univ.filter (fun x0 : M_0 => VertLink x0 a)).card ≤ D_down)
    (h_up : ∀ x0 : M_0, (Finset.univ.filter (fun b : W => VertLink x0 b)).card ≤ D_up)
    (a : W) :
    (Finset.univ.filter (fun w : V ⊕ W => StepGraphAdj Adj_V ι VertLink (Sum.inr a) w)).card ≤
      D_down + D_down * D_up := by
  rw [card_filter_sum_eq]
  let owners : Finset M_0 := Finset.univ.filter (fun x0 : M_0 => VertLink x0 a)
  have h_v_sub : Finset.univ.filter (fun v : V =>
      StepGraphAdj Adj_V ι VertLink (Sum.inr a) (Sum.inl v)) ⊆ owners.image ι := by
    intro v hv
    rw [Finset.mem_filter] at hv
    rcases hv.2 with ⟨x0, rfl, hlink⟩
    exact Finset.mem_image.mpr ⟨x0, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hlink⟩, rfl⟩
  have h_w_sub : Finset.univ.filter (fun b : W =>
      StepGraphAdj Adj_V ι VertLink (Sum.inr a) (Sum.inr b)) ⊆
      owners.biUnion (fun x0 => Finset.univ.filter (fun b : W => VertLink x0 b)) := by
    intro b hb
    rw [Finset.mem_filter] at hb
    rcases hb.2 with ⟨x0, ha, hb_link⟩
    exact Finset.mem_biUnion.mpr ⟨x0, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ha⟩,
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, hb_link⟩⟩
  have h_v_le : (Finset.univ.filter (fun v : V =>
      StepGraphAdj Adj_V ι VertLink (Sum.inr a) (Sum.inl v))).card ≤ D_down :=
    (Finset.card_le_card h_v_sub).trans (Finset.card_image_le.trans (h_down a))
  have h_w_le : (Finset.univ.filter (fun b : W =>
      StepGraphAdj Adj_V ι VertLink (Sum.inr a) (Sum.inr b))).card ≤ D_down * D_up := by
    calc (Finset.univ.filter (fun b : W =>
          StepGraphAdj Adj_V ι VertLink (Sum.inr a) (Sum.inr b))).card
      _ ≤ (owners.biUnion (fun x0 => Finset.univ.filter (fun b : W => VertLink x0 b))).card :=
            Finset.card_le_card h_w_sub
      _ ≤ ∑ x0 ∈ owners, (Finset.univ.filter (fun b : W => VertLink x0 b)).card :=
            Finset.card_biUnion_le
      _ ≤ ∑ _x0 ∈ owners, D_up := Finset.sum_le_sum (fun x0 _ => h_up x0)
      _ = owners.card * D_up := by rw [Finset.sum_const, smul_eq_mul]
      _ ≤ D_down * D_up := Nat.mul_le_mul_right D_up (h_down a)
  exact Nat.add_le_add h_v_le h_w_le

/-! ## 4. Multiscale Hierarchy Graph Package (`HierStepPkg`) & Witness Invariants -/

/-- Multiscale hierarchical check graph package with top check layer `M_top`
    (`HierStepPkg`, Part II, Definition 4.2 (`def:multiscale-cluster-decoder`) and
    Theorem 5.1(iii) (`thm:direct-worldline-intact-cluster-erasure`)). -/
structure HierStepPkg (M_top : Type) [Fintype M_top] [DecidableEq M_top] where
  V : Type
  instFintype : Fintype V
  instDecidableEq : DecidableEq V
  Adj : V → V → Prop
  R : Finset V
  ι : M_top → V
  symm : ∀ u v : V, Adj u v → Adj v u
  inj : Function.Injective ι
  card_R_le : R.card ≤ 9 * bdlSingleStepFactor ^ 2
  deg_all : ∀ u : V, (Finset.univ.filter (fun v : V => Adj u v)).card ≤
    32 + 1353 * bdlSingleStepFactor
  deg_top : ∀ x : M_top, (Finset.univ.filter (fun v : V => Adj (ι x) v)).card ≤
    32 + 1312 * bdlSingleStepFactor

attribute [instance] HierStepPkg.instFintype HierStepPkg.instDecidableEq

/-- Base-scale hierarchical graph package on a seed check set `M_0` of cardinality `≤ 32`. -/
def hierStepPkgBase (M_0 : Type) [Fintype M_0] [DecidableEq M_0]
    (h_card : Fintype.card M_0 ≤ 32) : HierStepPkg M_0 where
  V := M_0
  instFintype := inferInstance
  instDecidableEq := inferInstance
  Adj := fun _ _ => True
  R := Finset.univ
  ι := id
  symm := fun _ _ h => h
  inj := Function.injective_id
  card_R_le := by
    rw [Finset.card_univ]
    have hF : 2 ≤ bdlSingleStepFactor := bdlSingleStepFactor_ge_two
    nlinarith
  deg_all := fun _ => (Finset.card_le_univ _).trans (h_card.trans (by omega))
  deg_top := fun _ => (Finset.card_le_univ _).trans (h_card.trans (by omega))

/-- Resets the root set `R` of `G : HierStepPkg M_top` to the embedded top layer `Finset.univ.image G.ι`
    when `Fintype.card M_top ≤ 9 * bdlSingleStepFactor ^ 2`. -/
def hierStepPkgResetRoot {M_top : Type} [Fintype M_top] [DecidableEq M_top]
    (G : HierStepPkg M_top) (h_card : Fintype.card M_top ≤ 9 * bdlSingleStepFactor ^ 2) :
    HierStepPkg M_top where
  V := G.V
  instFintype := G.instFintype
  instDecidableEq := G.instDecidableEq
  Adj := G.Adj
  R := Finset.univ.map ⟨G.ι, G.inj⟩
  ι := G.ι
  symm := G.symm
  inj := G.inj
  card_R_le := by rw [Finset.card_map, Finset.card_univ]; exact h_card
  deg_all := G.deg_all
  deg_top := G.deg_top

/-- Extends `G : HierStepPkg M_0` by a new check layer `M_1` via vertical incidence `VertLink`. -/
def hierStepPkgExtend {M_0 M_1 : Type}
    [Fintype M_0] [DecidableEq M_0] [Fintype M_1] [DecidableEq M_1]
    (G : HierStepPkg M_0) (VertLink : M_0 → M_1 → Prop)
    (h_down : ∀ a : M_1, (Finset.univ.filter (fun x0 : M_0 => VertLink x0 a)).card ≤ 32)
    (h_up : ∀ x0 : M_0, (Finset.univ.filter (fun b : M_1 => VertLink x0 b)).card ≤
      41 * bdlSingleStepFactor) :
    HierStepPkg M_1 where
  V := G.V ⊕ M_1
  instFintype := inferInstance
  instDecidableEq := inferInstance
  Adj := StepGraphAdj G.Adj G.ι VertLink
  R := G.R.map ⟨Sum.inl, Sum.inl_injective⟩
  ι := Sum.inr
  symm := stepGraphAdj_symm G.symm
  inj := Sum.inr_injective
  card_R_le := by rw [Finset.card_map]; exact G.card_R_le
  deg_all := by
    rintro (u | a)
    · have h := card_filter_stepGraphAdj_inl_le G.Adj G.ι G.inj VertLink
        (D_top := 32 + 1312 * bdlSingleStepFactor) (D_up := 41 * bdlSingleStepFactor)
        (fun v => (G.deg_all v).trans (by omega)) G.deg_top h_up u
      omega
    · have h := card_filter_stepGraphAdj_inr_le G.Adj G.ι VertLink h_down h_up a
      omega
  deg_top := by
    intro a
    have h := card_filter_stepGraphAdj_inr_le G.Adj G.ι VertLink h_down h_up a
    omega

/-- Multiscale witness invariant on `G : HierStepPkg M_top` (`IsHierClusterWitness`,
    Part II, Definition 4.2 (`def:multiscale-cluster-decoder`),
    Lemma 4.4(iii) (`lem:two-stage-cleaner-contraction`), Equation (75) (`eq:total-multiscale-vertex-bound`),
    and Theorem 5.1(iii) (`thm:direct-worldline-intact-cluster-erasure`)). -/
structure IsHierClusterWitness {M_top : Type} [Fintype M_top] [DecidableEq M_top]
    (G : HierStepPkg M_top) (Conn : M_top → M_top → Prop) (w_coeff : ℕ)
    (c : M_top → ZMod 2) (C_hat : Finset G.V) : Prop where
  top_iff : ∀ x : M_top, G.ι x ∈ C_hat ↔ c x ≠ 0
  weight_le : 11 * C_hat.card ≤ w_coeff * syndromeWeightNat c
  upward_reach : ∀ u ∈ C_hat, ∃ x : M_top, c x ≠ 0 ∧
    Relation.ReflTransGen (fun a b => a ∈ C_hat ∧ b ∈ C_hat ∧ G.Adj a b) u (G.ι x)
  conn_sound : ∀ x y : M_top, c x ≠ 0 → c y ≠ 0 → Conn x y →
    Relation.ReflTransGen (fun a b => a ∈ C_hat ∧ b ∈ C_hat ∧ G.Adj a b) (G.ι x) (G.ι y)

lemma isHierClusterWitness_base {M_0 : Type} [Fintype M_0] [DecidableEq M_0]
    (h_card : Fintype.card M_0 ≤ 32) (c0 : M_0 → ZMod 2) :
    let G0 := hierStepPkgBase M_0 h_card
    let C_hat : Finset G0.V := Finset.univ.filter (fun x : M_0 => c0 x ≠ 0)
    IsHierClusterWitness G0 (fun a b => c0 a ≠ 0 ∧ c0 b ≠ 0) 11 c0 C_hat := by
  intro G0 C_hat
  let C_std : Finset M_0 := Finset.univ.filter (fun x : M_0 => c0 x ≠ 0)
  have hC : C_hat = C_std := by
    dsimp [G0, hierStepPkgBase, C_hat, C_std]
    congr 1
  change IsHierClusterWitness (hierStepPkgBase M_0 h_card) (fun a b => c0 a ≠ 0 ∧ c0 b ≠ 0) 11 c0 C_hat
  rw [hC]
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro x
    change x ∈ C_std ↔ c0 x ≠ 0
    simp [C_std]
  · change 11 * C_std.card ≤ 11 * syndromeWeightNat c0
    exact le_rfl
  · intro (u : M_0) (hu : u ∈ C_std)
    have hu_ne : c0 u ≠ 0 := (Finset.mem_filter.mp hu).2
    exact ⟨u, hu_ne, Relation.ReflTransGen.refl⟩
  · intro x y hx hy _
    have hx_mem : x ∈ C_std := Finset.mem_filter.mpr ⟨Finset.mem_univ x, hx⟩
    have hy_mem : y ∈ C_std := Finset.mem_filter.mpr ⟨Finset.mem_univ y, hy⟩
    exact Relation.ReflTransGen.single ⟨hx_mem, hy_mem, trivial⟩

lemma isHierClusterWitness_resetRoot {M_top : Type} [Fintype M_top] [DecidableEq M_top]
    (G : HierStepPkg M_top) (h_card : Fintype.card M_top ≤ 9 * bdlSingleStepFactor ^ 2)
    {Conn : M_top → M_top → Prop} {w_coeff : ℕ} {c : M_top → ZMod 2} {C_hat : Finset G.V}
    (hw : IsHierClusterWitness G Conn w_coeff c C_hat) (hc_ne : c ≠ 0) :
    IsHierClusterWitness (hierStepPkgResetRoot G h_card) Conn w_coeff c C_hat ∧
    (C_hat ∩ (hierStepPkgResetRoot G h_card).R).Nonempty := by
  refine ⟨⟨hw.top_iff, hw.weight_le, hw.upward_reach, hw.conn_sound⟩, ?_⟩
  have h_ex : ∃ x : M_top, c x ≠ 0 := by
    by_contra h_all
    push_neg at h_all
    exact hc_ne (funext h_all)
  rcases h_ex with ⟨x, hx⟩
  refine ⟨G.ι x, Finset.mem_inter.mpr ⟨(hw.top_iff x).mpr hx, ?_⟩⟩
  dsimp [hierStepPkgResetRoot]
  exact Finset.mem_map.mpr ⟨x, Finset.mem_univ x, rfl⟩

/-- Extends `C_hat_0 : Finset G.V` to `G.V ⊕ M_1` by adding the active top-layer checks of `c1`. -/
def extendHierClusterSupport {V M_1 : Type} [Fintype V] [DecidableEq V] [Fintype M_1] [DecidableEq M_1]
    (C_hat_0 : Finset V) (c1 : M_1 → ZMod 2) : Finset (V ⊕ M_1) :=
  C_hat_0.map ⟨Sum.inl, Sum.inl_injective⟩ ∪
    (Finset.univ.filter (fun a : M_1 => c1 a ≠ 0)).map ⟨Sum.inr, Sum.inr_injective⟩

lemma card_extendHierClusterSupport {V M_1 : Type}
    [Fintype V] [DecidableEq V] [Fintype M_1] [DecidableEq M_1]
    (C_hat_0 : Finset V) (c1 : M_1 → ZMod 2) :
    (extendHierClusterSupport C_hat_0 c1).card = C_hat_0.card + syndromeWeightNat c1 := by
  dsimp [extendHierClusterSupport, syndromeWeightNat]
  rw [Finset.card_union_of_disjoint, Finset.card_map, Finset.card_map]
  rw [Finset.disjoint_left]
  intro x hx1 hx2
  rcases Finset.mem_map.mp hx1 with ⟨u, _, rfl⟩
  rcases Finset.mem_map.mp hx2 with ⟨a, _, h_eq⟩
  nomatch h_eq

lemma reflTransGen_map_inl {V M_0 M_1 : Type}
    [Fintype V] [DecidableEq V] [Fintype M_1] [DecidableEq M_1]
    {Adj_V : V → V → Prop} {ι : M_0 → V} {VertLink : M_0 → M_1 → Prop}
    {C_hat_0 : Finset V} {c1 : M_1 → ZMod 2} {u v : V}
    (h : Relation.ReflTransGen (fun a b => a ∈ C_hat_0 ∧ b ∈ C_hat_0 ∧ Adj_V a b) u v) :
    let C_hat_1 := extendHierClusterSupport C_hat_0 c1
    Relation.ReflTransGen
      (fun a b => a ∈ C_hat_1 ∧ b ∈ C_hat_1 ∧ StepGraphAdj Adj_V ι VertLink a b)
      (Sum.inl u) (Sum.inl v) := by
  intro C_hat_1
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | @tail b c _ hstep ih =>
    apply Relation.ReflTransGen.tail ih
    refine ⟨?_, ?_, hstep.2.2⟩
    · dsimp [C_hat_1, extendHierClusterSupport]
      exact Finset.mem_union_left _ (Finset.mem_map.mpr ⟨b, hstep.1, rfl⟩)
    · dsimp [C_hat_1, extendHierClusterSupport]
      exact Finset.mem_union_left _ (Finset.mem_map.mpr ⟨c, hstep.2.1, rfl⟩)

lemma reflTransGen_symm_of_adj_symm {W : Type} {Adj : W → W → Prop}
    (h_symm : ∀ u v : W, Adj u v → Adj v u) {S : Finset W} {u v : W}
    (h : Relation.ReflTransGen (fun a b => a ∈ S ∧ b ∈ S ∧ Adj a b) u v) :
    Relation.ReflTransGen (fun a b => a ∈ S ∧ b ∈ S ∧ Adj a b) v u := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | @tail b c _ hstep ih =>
    exact Relation.ReflTransGen.head ⟨hstep.2.1, hstep.1, h_symm b c hstep.2.2⟩ ih

/-- Inductive step for `IsHierClusterWitness` across any primal or dual layer extension. -/
theorem isHierClusterWitness_extend {M_0 M_1 : Type}
    [Fintype M_0] [DecidableEq M_0] [Fintype M_1] [DecidableEq M_1]
    (G : HierStepPkg M_0) (VertLink : M_0 → M_1 → Prop)
    (h_down : ∀ a : M_1, (Finset.univ.filter (fun x0 : M_0 => VertLink x0 a)).card ≤ 32)
    (h_up : ∀ x0 : M_0, (Finset.univ.filter (fun b : M_1 => VertLink x0 b)).card ≤
      41 * bdlSingleStepFactor)
    {Conn0 : M_0 → M_0 → Prop} {w0 w1 : ℕ}
    {c0 : M_0 → ZMod 2} {c1 : M_1 → ZMod 2} {C_hat_0 : Finset G.V}
    (hw0 : IsHierClusterWitness G Conn0 w0 c0 C_hat_0)
    (h_wt : w0 * syndromeWeightNat c0 + 11 * syndromeWeightNat c1 ≤ w1 * syndromeWeightNat c1)
    (h_active : ∀ x0 : M_0, c0 x0 ≠ 0 → ∃ a : M_1, VertLink x0 a ∧ c1 a ≠ 0)
    (StepAdj : M_1 → M_1 → Prop)
    (h_adj : ∀ a b : M_1, StepAdj a b →
      c1 a ≠ 0 ∧ c1 b ≠ 0 ∧
      ((∃ x0 : M_0, VertLink x0 a ∧ VertLink x0 b) ∨
       (∃ x_a x_b : M_0, c0 x_a ≠ 0 ∧ c0 x_b ≠ 0 ∧ Conn0 x_a x_b ∧
         VertLink x_a a ∧ VertLink x_b b))) :
    let G1 := hierStepPkgExtend G VertLink h_down h_up
    let C_hat_1 : Finset G1.V := extendHierClusterSupport C_hat_0 c1
    IsHierClusterWitness G1 (Relation.ReflTransGen StepAdj) w1 c1 C_hat_1 ∧
    ((C_hat_0 ∩ G.R).Nonempty → (C_hat_1 ∩ G1.R).Nonempty) := by
  intro G1 C_hat_1
  have h_top_iff : ∀ a : M_1, G1.ι a ∈ C_hat_1 ↔ c1 a ≠ 0 := by
    intro a
    change Sum.inr a ∈ extendHierClusterSupport C_hat_0 c1 ↔ c1 a ≠ 0
    simp [extendHierClusterSupport]
  have h_wt1 : 11 * C_hat_1.card ≤ w1 * syndromeWeightNat c1 := by
    change 11 * (extendHierClusterSupport C_hat_0 c1).card ≤ w1 * syndromeWeightNat c1
    rw [card_extendHierClusterSupport]
    have h0 := hw0.weight_le
    omega
  have h_reach1 : ∀ w ∈ C_hat_1, ∃ a : M_1, c1 a ≠ 0 ∧
      Relation.ReflTransGen (fun x y => x ∈ C_hat_1 ∧ y ∈ C_hat_1 ∧ G1.Adj x y) w (G1.ι a) := by
    intro w hw
    dsimp [C_hat_1, extendHierClusterSupport] at hw
    rcases Finset.mem_union.mp hw with hw_inl | hw_inr
    · rcases Finset.mem_map.mp hw_inl with ⟨u, hu_mem, rfl⟩
      obtain ⟨x0, hx0_ne, h_path0⟩ := hw0.upward_reach u hu_mem
      obtain ⟨a, hlink, ha_ne⟩ := h_active x0 hx0_ne
      have h_path_inl := reflTransGen_map_inl (ι := G.ι) (VertLink := VertLink) (c1 := c1) h_path0
      have hx0_in1 : Sum.inl (G.ι x0) ∈ C_hat_1 := by
        dsimp [C_hat_1, extendHierClusterSupport]
        exact Finset.mem_union_left _ (Finset.mem_map.mpr ⟨G.ι x0, (hw0.top_iff x0).mpr hx0_ne, rfl⟩)
      have ha_in1 : Sum.inr a ∈ C_hat_1 := (h_top_iff a).mpr ha_ne
      refine ⟨a, ha_ne, Relation.ReflTransGen.tail h_path_inl ⟨hx0_in1, ha_in1, ⟨x0, rfl, hlink⟩⟩⟩
    · rcases Finset.mem_map.mp hw_inr with ⟨a, ha_mem, rfl⟩
      exact ⟨a, (Finset.mem_filter.mp ha_mem).2, Relation.ReflTransGen.refl⟩
  have h_step_sound : ∀ a b : M_1, StepAdj a b →
      Relation.ReflTransGen
        (fun x y => x ∈ C_hat_1 ∧ y ∈ C_hat_1 ∧ G1.Adj x y) (Sum.inr a) (Sum.inr b) := by
    intro a b hab
    obtain ⟨ha_ne, hb_ne, h_same | ⟨x_a, x_b, hxa_ne, hxb_ne, hconn0, hlink_a, hlink_b⟩⟩ :=
      h_adj a b hab
    · have ha_in1 : Sum.inr a ∈ C_hat_1 := (h_top_iff a).mpr ha_ne
      have hb_in1 : Sum.inr b ∈ C_hat_1 := (h_top_iff b).mpr hb_ne
      exact Relation.ReflTransGen.single ⟨ha_in1, hb_in1, h_same⟩
    · have ha_in1 : Sum.inr a ∈ C_hat_1 := (h_top_iff a).mpr ha_ne
      have hb_in1 : Sum.inr b ∈ C_hat_1 := (h_top_iff b).mpr hb_ne
      have hxa_in1 : Sum.inl (G.ι x_a) ∈ C_hat_1 := by
        dsimp [C_hat_1, extendHierClusterSupport]
        exact Finset.mem_union_left _ (Finset.mem_map.mpr ⟨G.ι x_a, (hw0.top_iff x_a).mpr hxa_ne, rfl⟩)
      have hxb_in1 : Sum.inl (G.ι x_b) ∈ C_hat_1 := by
        dsimp [C_hat_1, extendHierClusterSupport]
        exact Finset.mem_union_left _ (Finset.mem_map.mpr ⟨G.ι x_b, (hw0.top_iff x_b).mpr hxb_ne, rfl⟩)
      have h_mid := reflTransGen_map_inl (ι := G.ι) (VertLink := VertLink) (c1 := c1)
        (hw0.conn_sound x_a x_b hxa_ne hxb_ne hconn0)
      have h_first : Relation.ReflTransGen
          (fun x y => x ∈ C_hat_1 ∧ y ∈ C_hat_1 ∧ G1.Adj x y)
          (Sum.inr a) (Sum.inl (G.ι x_b)) :=
        Relation.ReflTransGen.head ⟨ha_in1, hxa_in1, ⟨x_a, rfl, hlink_a⟩⟩ h_mid
      exact Relation.ReflTransGen.tail h_first ⟨hxb_in1, hb_in1, ⟨x_b, rfl, hlink_b⟩⟩
  have h_conn_sound1_aux : ∀ a b : M_1,
      Relation.ReflTransGen StepAdj a b →
      Relation.ReflTransGen
        (fun x y => x ∈ C_hat_1 ∧ y ∈ C_hat_1 ∧ G1.Adj x y) (G1.ι a) (G1.ι b) := by
    intro a b h_path
    induction h_path with
    | refl => exact Relation.ReflTransGen.refl
    | @tail u v _ hstep ih =>
      exact Relation.ReflTransGen.trans ih (h_step_sound u v hstep)
  have h_conn_sound1 : ∀ a b : M_1, c1 a ≠ 0 → c1 b ≠ 0 →
      Relation.ReflTransGen StepAdj a b →
      Relation.ReflTransGen
        (fun x y => x ∈ C_hat_1 ∧ y ∈ C_hat_1 ∧ G1.Adj x y) (G1.ι a) (G1.ι b) :=
    fun a b _ _ h_path => h_conn_sound1_aux a b h_path
  refine ⟨⟨h_top_iff, h_wt1, h_reach1, h_conn_sound1⟩, ?_⟩
  rintro ⟨r0, hr0⟩
  have hr0_C : r0 ∈ C_hat_0 := (Finset.mem_inter.mp hr0).1
  have hr0_R : r0 ∈ G.R := (Finset.mem_inter.mp hr0).2
  refine ⟨Sum.inl r0, Finset.mem_inter.mpr ⟨?_, ?_⟩⟩
  · dsimp [C_hat_1, extendHierClusterSupport]
    exact Finset.mem_union_left _ (Finset.mem_map.mpr ⟨r0, hr0_C, rfl⟩)
  · dsimp [G1, hierStepPkgExtend]
    exact Finset.mem_map.mpr ⟨r0, hr0_R, rfl⟩

/-- Combines `upward_reach` and `conn_sound` at the top scale to deduce `HierSetConnected G.Adj C_hat`. -/
lemma IsHierClusterWitness.hier_set_connected {M_top : Type} [Fintype M_top] [DecidableEq M_top]
    {G : HierStepPkg M_top} {Conn : M_top → M_top → Prop} {w_coeff : ℕ}
    {c : M_top → ZMod 2} {C_hat : Finset G.V}
    (hw : IsHierClusterWitness G Conn w_coeff c C_hat)
    (h_conn_top : ∀ x y : M_top, c x ≠ 0 → c y ≠ 0 → Conn x y) :
    HierSetConnected G.Adj C_hat := by
  intro u hu v hv
  obtain ⟨x, hx_ne, h_ux⟩ := hw.upward_reach u hu
  obtain ⟨y, hy_ne, h_vy⟩ := hw.upward_reach v hv
  have h_xy := hw.conn_sound x y hx_ne hy_ne (h_conn_top x y hx_ne hy_ne)
  have h_yv := reflTransGen_symm_of_adj_symm G.symm h_vy
  exact Relation.ReflTransGen.trans h_ux (Relation.ReflTransGen.trans h_xy h_yv)

/-! ## 5. Arithmetic & Final Shell Cardinality Bound for `HierStepPkg` -/

private lemma nine_mul_sq_mul_pow_ten_le_pow_eight_gen {F B m : ℕ}
    (hF2 : 2 ≤ F) (h_base : 2 ^ (41 * F) ≤ B) (hm : 1 ≤ m) :
    9 * F ^ 2 * (33 + 1353 * F) ^ (10 * m) ≤ (B ^ 8) ^ m := by
  have h_deg_le : 33 + 1353 * F ≤ 2048 * F := by omega
  have h_2048 : (2048 : ℕ) = 2 ^ 11 := by decide
  have hF_two : F ≤ 2 ^ F := le_of_lt Nat.lt_two_pow_self
  have h_step : 33 + 1353 * F ≤ 2 ^ (12 * F) := by
    calc 33 + 1353 * F
      _ ≤ 2048 * F := h_deg_le
      _ ≤ 2 ^ 11 * 2 ^ F := by rw [h_2048]; exact Nat.mul_le_mul_left _ hF_two
      _ = 2 ^ (11 + F) := (Nat.pow_add 2 11 F).symm
      _ ≤ 2 ^ (12 * F) := Nat.pow_le_pow_right (by decide) (by omega)
  have h_16 : (16 : ℕ) = 2 ^ 4 := by decide
  have h_root : 9 * F ^ 2 ≤ 2 ^ (6 * F) := by
    calc 9 * F ^ 2
      _ ≤ 16 * (F * F) := by nlinarith
      _ = 2 ^ 4 * (F * F) := by rw [h_16]
      _ ≤ 2 ^ 4 * (2 ^ F * 2 ^ F) :=
          Nat.mul_le_mul_left _ (Nat.mul_le_mul hF_two hF_two)
      _ = 2 ^ (4 + F + F) := by rw [← Nat.pow_add, ← Nat.pow_add, add_assoc]
      _ ≤ 2 ^ (6 * F) := Nat.pow_le_pow_right (by decide) (by omega)
  have h_lhs : 9 * F ^ 2 * (33 + 1353 * F) ^ (10 * m) ≤ 2 ^ (328 * F * m) := by
    calc 9 * F ^ 2 * (33 + 1353 * F) ^ (10 * m)
      _ ≤ 2 ^ (6 * F) * (2 ^ (12 * F)) ^ (10 * m) :=
          Nat.mul_le_mul h_root (Nat.pow_le_pow_left h_step (10 * m))
      _ = 2 ^ (6 * F + 12 * F * (10 * m)) := by rw [← Nat.pow_mul, ← Nat.pow_add]
      _ ≤ 2 ^ (328 * F * m) := by
          apply Nat.pow_le_pow_right (by decide)
          nlinarith
  have h_exp : 328 * F * m = 41 * F * 8 * m := by nlinarith
  calc 9 * F ^ 2 * (33 + 1353 * F) ^ (10 * m)
    _ ≤ 2 ^ (328 * F * m) := h_lhs
    _ = 2 ^ (41 * F * 8 * m) := congrArg (2 ^ ·) h_exp
    _ = ((2 ^ (41 * F)) ^ 8) ^ m := by rw [Nat.pow_mul, Nat.pow_mul]
    _ ≤ (B ^ 8) ^ m :=
        Nat.pow_le_pow_left (Nat.pow_le_pow_left h_base 8) m

lemma nine_mul_sq_mul_pow_ten_le_clusterStepBase_pow_eight {m : ℕ} (hm : 1 ≤ m) :
    let F := bdlSingleStepFactor
    9 * F ^ 2 * (33 + 1353 * F) ^ (10 * m) ≤ (bdlClusterStepBase ^ 8) ^ m :=
  nine_mul_sq_mul_pow_ten_le_pow_eight_gen
    bdlSingleStepFactor_ge_two two_pow_le_bdlClusterStepBase hm

lemma zmod2_eq_of_ne_zero_iff (a b : ZMod 2) (h : a ≠ 0 ↔ b ≠ 0) : a = b := by
  revert a b; decide

lemma nat_choose_le_pow : ∀ (n m : ℕ), n.choose m ≤ n ^ m
  | n, 0 => by simp
  | 0, m + 1 => by simp
  | n + 1, m + 1 => by
    rw [Nat.choose_succ_succ]
    have h1 := nat_choose_le_pow n m
    have h2 := nat_choose_le_pow n (m + 1)
    have h3 : n ^ m ≤ (n + 1) ^ m := Nat.pow_le_pow_left (Nat.le_succ n) m
    have h4 : n ^ (m + 1) ≤ n * (n + 1) ^ m := by
      rw [pow_succ']
      exact Nat.mul_le_mul_left n h3
    calc n.choose m + n.choose (m + 1)
      _ ≤ (n + 1) ^ m + n * (n + 1) ^ m := Nat.add_le_add (h1.trans h3) (h2.trans h4)
      _ = (n + 1) ^ (m + 1) := by ring

lemma card_filter_syndrome_weight_le {M_X : Type} [Fintype M_X] [DecidableEq M_X]
    (W : Finset (M_X → ZMod 2)) {B : ℕ} (hB : Fintype.card M_X ≤ B) (m : ℕ) :
    (W.filter (fun c => (Finset.univ.filter (fun x => c x ≠ 0)).card = m)).card ≤ B ^ m := by
  let supp : (M_X → ZMod 2) → Finset M_X := fun c => Finset.univ.filter (fun x => c x ≠ 0)
  have h_inj : Set.InjOn supp ↑(W.filter (fun c => (supp c).card = m)) := by
    intro c₁ _ c₂ _ h_eq
    funext x
    apply zmod2_eq_of_ne_zero_iff
    have hx : x ∈ supp c₁ ↔ x ∈ supp c₂ := by rw [h_eq]
    simpa [supp] using hx
  have h_maps : Set.MapsTo supp ↑(W.filter (fun c => (supp c).card = m))
      ↑((Finset.univ : Finset M_X).powersetCard m) := by
    intro c hc
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_powersetCard,
      Finset.subset_univ, true_and] at hc ⊢
    exact hc.2
  calc (W.filter (fun c => (supp c).card = m)).card
    _ ≤ ((Finset.univ : Finset M_X).powersetCard m).card :=
        Finset.card_le_card_of_injOn supp h_maps h_inj
    _ = (Fintype.card M_X).choose m := by rw [Finset.card_powersetCard, Finset.card_univ]
    _ ≤ (Fintype.card M_X) ^ m := nat_choose_le_pow (Fintype.card M_X) m
    _ ≤ B ^ m := Nat.pow_le_pow_left hB m

/-- **Master Klarner Shell Cardinality Theorem for `HierStepPkg` (`HierStepPkg.card_shell_le`,
    Part II, Lemma 3.3 (`lem:klarner-bound`), Lemma 4.4(iii) (`lem:two-stage-cleaner-contraction`),
    Equation (75) (`eq:total-multiscale-vertex-bound`), and
    Theorem 5.1(iii) (`thm:direct-worldline-intact-cluster-erasure`))**:
    For any witness pool `W : Finset (M_top → ZMod 2)` on `G : HierStepPkg M_top` such that every
    `c ∈ W` has `c ≠ 0` and admits a multiscale support `C_hat : Finset G.V`, connectivity relation
    `Conn : M_top → M_top → Prop`, and weight coefficient `w_coeff ≤ 55` satisfying
    `IsHierClusterWitness G Conn w_coeff c C_hat`, `(C_hat ∩ G.R).Nonempty`, and
    `∀ x y, c x ≠ 0 → c y ≠ 0 → Conn x y`, every weight-`m` shell of `W` has cardinality at most
    `(bdlClusterStepBase ^ 8) ^ m`. -/
theorem HierStepPkg.card_shell_le {M_top : Type} [Fintype M_top] [DecidableEq M_top]
    (G : HierStepPkg M_top) (W : Finset (M_top → ZMod 2))
    (h_wit : ∀ c ∈ W, c ≠ 0 ∧ ∃ (Conn : M_top → M_top → Prop) (w_coeff : ℕ) (C_hat : Finset G.V),
      w_coeff ≤ 55 ∧
      IsHierClusterWitness G Conn w_coeff c C_hat ∧
      (C_hat ∩ G.R).Nonempty ∧
      (∀ x y : M_top, c x ≠ 0 → c y ≠ 0 → Conn x y))
    (m : ℕ) :
    (W.filter (fun c => (Finset.univ.filter (fun x => c x ≠ 0)).card = m)).card ≤
      (bdlClusterStepBase ^ 8) ^ m := by
  let W_m := W.filter (fun c => (Finset.univ.filter (fun x => c x ≠ 0)).card = m)
  by_cases hm0 : m = 0
  · subst hm0
    have h_empty : W_m = ∅ := by
      rw [Finset.filter_eq_empty_iff]
      intro c hc h_card0
      have hc_ne := (h_wit c hc).1
      rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff] at h_card0
      apply hc_ne
      ext x
      by_contra hx
      exact h_card0 (Finset.mem_univ x) hx
    change W_m.card ≤ (bdlClusterStepBase ^ 8) ^ 0
    rw [h_empty, Finset.card_empty, pow_zero]
    exact Nat.zero_le 1
  · have hm_pos : 1 ≤ m := Nat.pos_of_ne_zero hm0
    have h_ex_Chat : ∀ c : M_top → ZMod 2, ∃ C_hat : Finset G.V,
        c ∈ W_m →
          (∀ x : M_top, G.ι x ∈ C_hat ↔ c x ≠ 0) ∧
          (C_hat ∩ G.R).Nonempty ∧
          C_hat.card ≤ 5 * m ∧
          HierSetConnected G.Adj C_hat := by
      intro c
      by_cases hc : c ∈ W_m
      · have hc_W : c ∈ W := (Finset.mem_filter.mp hc).1
        have hc_m : syndromeWeightNat c = m := (Finset.mem_filter.mp hc).2
        obtain ⟨_, Conn, w_coeff, C_hat, hw_le, hw, h_root, h_conn_top⟩ := h_wit c hc_W
        have h_card_le : C_hat.card ≤ 5 * m := by
          have h11 := hw.weight_le
          rw [hc_m] at h11
          have h55 : w_coeff * m ≤ 55 * m := Nat.mul_le_mul_right m hw_le
          omega
        exact ⟨C_hat, fun _ => ⟨hw.top_iff, h_root, h_card_le, hw.hier_set_connected h_conn_top⟩⟩
      · exact ⟨∅, fun h_abs => False.elim (hc h_abs)⟩
    choose C_hat_of hC_hat_of using h_ex_Chat
    let F_set : Finset (Finset G.V) := W_m.image C_hat_of
    have h_inj : Set.InjOn C_hat_of ↑W_m := by
      intro c1 hc1 c2 hc2 h_eq
      have h1 := (hC_hat_of c1 hc1).1
      have h2 := (hC_hat_of c2 hc2).1
      funext x
      apply zmod2_eq_of_ne_zero_iff
      rw [← h1 x, h_eq, h2 x]
    have h_card_eq : W_m.card = F_set.card :=
      (Finset.card_image_of_injOn h_inj).symm
    have h_sub : ∀ S ∈ F_set, (S ∩ G.R).Nonempty ∧ S.card ≤ 5 * m ∧ HierSetConnected G.Adj S := by
      intro S hS
      rcases Finset.mem_image.mp hS with ⟨c, hc, rfl⟩
      exact ⟨(hC_hat_of c hc).2.1, (hC_hat_of c hc).2.2.1, (hC_hat_of c hc).2.2.2⟩
    have h_klarner := card_connected_subsets_rooted_le G.Adj G.symm G.R
      (32 + 1353 * bdlSingleStepFactor) (5 * m) G.deg_all F_set h_sub
    have h_exp_eq : 2 * (5 * m) = 10 * m := by omega
    have h_deg_eq : 32 + 1353 * bdlSingleStepFactor + 1 = 33 + 1353 * bdlSingleStepFactor := by omega
    rw [h_exp_eq, h_deg_eq] at h_klarner
    calc W_m.card
      _ = F_set.card := h_card_eq
      _ ≤ G.R.card * (33 + 1353 * bdlSingleStepFactor) ^ (10 * m) := h_klarner
      _ ≤ 9 * bdlSingleStepFactor ^ 2 * (33 + 1353 * bdlSingleStepFactor) ^ (10 * m) :=
            Nat.mul_le_mul_right _ G.card_R_le
      _ ≤ (bdlClusterStepBase ^ 8) ^ m :=
            nine_mul_sq_mul_pow_ten_le_clusterStepBase_pow_eight hm_pos

/-! ## 6. BDL Primal and Dual Step Specializations of `HierStepPkg` -/

lemma card_bdlIterated0_le_32 :
    Fintype.card (bdlIteratedBundled 0).M_X ≤ 32 ∧
    Fintype.card (bdlIteratedBundled 0).M_Z ≤ 32 := by
  have h_cards := card_MX_MZ_le_bundledCellCount (bdlIteratedBundled 0)
  have h_cell : bundledCellCount (bdlIteratedBundled 0) ≤ 9 * (bdlSingleStepFactor ^ 2) ^ 0 := by
    rw [bdlIteratedBundled_eq]
    exact bundledCellCount_iterated_le 0
  rw [pow_zero, mul_one] at h_cell
  exact ⟨h_cards.1.trans (h_cell.trans (by omega)), h_cards.2.trans (h_cell.trans (by omega))⟩

lemma card_bdlIterated1_le_nine_sq :
    Fintype.card (bdlIteratedBundled 1).M_X ≤ 9 * bdlSingleStepFactor ^ 2 ∧
    Fintype.card (bdlIteratedBundled 1).M_Z ≤ 9 * bdlSingleStepFactor ^ 2 := by
  have h_cards := card_MX_MZ_le_bundledCellCount (bdlIteratedBundled 1)
  have h_cell : bundledCellCount (bdlIteratedBundled 1) ≤ 9 * (bdlSingleStepFactor ^ 2) ^ 1 := by
    rw [bdlIteratedBundled_eq]
    exact bundledCellCount_iterated_le 1
  rw [pow_one] at h_cell
  exact ⟨h_cards.1.trans h_cell, h_cards.2.trans h_cell⟩

/-- Primal cylinder vertical link relation on `B`. -/
def BDLPrimalVertLink (B : BundledCSSCode3D) (x0 : B.M_X)
    (a : BDLStepXMX (bdlPerturbedOfBundled B) bdlSubdivPred) : Prop :=
  stepXMXOwnerX (bdlPerturbedOfBundled B) bdlSubdivPred a = x0

/-- Dual two-hop pool vertical link relation on `B`. -/
def BDLDualVertLink (B : BundledCSSCode3D) (z0 : B.M_Z)
    (a : BDLStepXMZ (bdlPerturbedOfBundled B) bdlSubdivPred) : Prop :=
  a ∈ fineTwoHopPool (bdlPerturbedOfBundled B) bdlSubdivPred {z0}

lemma bdlPrimal_down_le (B : BundledCSSCode3D)
    (a : BDLStepXMX (bdlPerturbedOfBundled B) bdlSubdivPred) :
    (Finset.univ.filter (fun x0 : B.M_X => BDLPrimalVertLink B x0 a)).card ≤ 32 := by
  have h_sub : Finset.univ.filter (fun x0 : B.M_X => BDLPrimalVertLink B x0 a) ⊆
      {stepXMXOwnerX (bdlPerturbedOfBundled B) bdlSubdivPred a} := by
    intro x0 hx0
    exact Finset.mem_singleton.mpr (Finset.mem_filter.mp hx0).2.symm
  have h_le := Finset.card_le_card h_sub
  rw [Finset.card_singleton] at h_le
  omega

lemma bdlPrimal_up_le (B : BundledCSSCode3D) (h_inv : HasBDLConeInvariants B) (x0 : B.M_X) :
    (Finset.univ.filter (fun a : BDLStepXMX (bdlPerturbedOfBundled B) bdlSubdivPred =>
      BDLPrimalVertLink B x0 a)).card ≤ 41 * bdlSingleStepFactor := by
  have h_eq : Finset.univ.filter (fun a : BDLStepXMX (bdlPerturbedOfBundled B) bdlSubdivPred =>
      BDLPrimalVertLink B x0 a) =
      Finset.univ.filter (fun a : BDLStepXMX (bdlPerturbedOfBundled B) bdlSubdivPred =>
        stepXMXOwnerX (bdlPerturbedOfBundled B) bdlSubdivPred a = x0) := by
    ext a; rw [Finset.mem_filter, Finset.mem_filter]; rfl
  rw [h_eq]
  have hsimp : HasBoundedSimplexDegreeD B 32 :=
    hasBoundedSimplexDegreeD_32_of_hasBoundedCheckDegreeOverlap B h_inv.1
  have h_fib : (Finset.univ.filter (fun a : BDLStepXMX (bdlPerturbedOfBundled B) bdlSubdivPred =>
      stepXMXOwnerX (bdlPerturbedOfBundled B) bdlSubdivPred a = x0)).card ≤
      bdlSingleStepFactor :=
    card_fiber_stepXMXOwnerX_le_bdlSingleStepFactor B h_inv.1.1 hsimp x0
  exact h_fib.trans (by omega)

lemma bdlDual_down_le (B : BundledCSSCode3D) (h_inv : HasBDLConeInvariants B)
    (a : BDLStepXMZ (bdlPerturbedOfBundled B) bdlSubdivPred) :
    (Finset.univ.filter (fun z0 : B.M_Z => BDLDualVertLink B z0 a)).card ≤ 32 := by
  have h_eq : Finset.univ.filter (fun z0 : B.M_Z => BDLDualVertLink B z0 a) =
      Finset.univ.filter (fun z0 : B.M_Z =>
        a ∈ fineTwoHopPool (bdlPerturbedOfBundled B) bdlSubdivPred {z0}) := by
    ext z0; rw [Finset.mem_filter, Finset.mem_filter]; rfl
  rw [h_eq]
  exact card_filter_fineTwoHopPool_singleton_le_32
    (bdlPerturbedOfBundled B) bdlSubdivPred h_inv.1.1.1 h_inv.1.1.2.2.2 a

lemma bdlDual_up_le (B : BundledCSSCode3D) (h_inv : HasBDLConeInvariants B) (z0 : B.M_Z) :
    (Finset.univ.filter (fun a : BDLStepXMZ (bdlPerturbedOfBundled B) bdlSubdivPred =>
      BDLDualVertLink B z0 a)).card ≤ 41 * bdlSingleStepFactor := by
  have h_eq : Finset.univ.filter (fun a : BDLStepXMZ (bdlPerturbedOfBundled B) bdlSubdivPred =>
      BDLDualVertLink B z0 a) =
      fineTwoHopPool (bdlPerturbedOfBundled B) bdlSubdivPred {z0} := by
    ext a; rw [Finset.mem_filter]; simp [BDLDualVertLink]
  rw [h_eq]
  have hsimp : HasBoundedSimplexDegreeD B 32 :=
    hasBoundedSimplexDegreeD_32_of_hasBoundedCheckDegreeOverlap B h_inv.1
  have h_pool : (fineTwoHopPool (bdlPerturbedOfBundled B) bdlSubdivPred {z0}).card ≤
      41 * bdlSingleStepFactor * ({z0} : Finset B.M_Z).card :=
    card_fineTwoHopPool_le B h_inv.1.1 hsimp {z0}
  rw [Finset.card_singleton, mul_one] at h_pool
  exact h_pool

/-- Extends `G : HierStepPkg B.M_X` across a BDL primal cylinder step on `B`. -/
def hierStepPkgBDLPrimal (B : BundledCSSCode3D) (h_inv : HasBDLConeInvariants B)
    (G : HierStepPkg B.M_X) :
    HierStepPkg (BDLStepXMX (bdlPerturbedOfBundled B) bdlSubdivPred) :=
  hierStepPkgExtend G (BDLPrimalVertLink B) (bdlPrimal_down_le B) (bdlPrimal_up_le B h_inv)

/-- Extends `G : HierStepPkg B.M_Z` across a BDL dual two-hop pool step on `B`. -/
def hierStepPkgBDLDual (B : BundledCSSCode3D) (h_inv : HasBDLConeInvariants B)
    (G : HierStepPkg B.M_Z) :
    HierStepPkg (BDLStepXMZ (bdlPerturbedOfBundled B) bdlSubdivPred) :=
  hierStepPkgExtend G (BDLDualVertLink B) (bdlDual_down_le B h_inv) (bdlDual_up_le B h_inv)

/-- Single-step witness lift across `hierStepPkgBDLPrimal`. -/
lemma isHierClusterWitness_bdlPrimal (B : BundledCSSCode3D) (h_inv : HasBDLConeInvariants B)
    (G : HierStepPkg B.M_X)
    {Conn0 : B.M_X → B.M_X → Prop} {w0 : ℕ}
    {c0 : B.M_X → ZMod 2}
    {c1 : BDLStepXMX (bdlPerturbedOfBundled B) bdlSubdivPred → ZMod 2}
    {C_hat_0 : Finset G.V}
    (hw0 : IsHierClusterWitness G Conn0 w0 c0 C_hat_0)
    (h_syn : coarseSyndromeStepXMX (bdlPerturbedOfBundled B) bdlSubdivPred c1 = c0)
    (h_wt_le : syndromeWeightNat c0 ≤ syndromeWeightNat c1)
    (StepAdj : BDLStepXMX (bdlPerturbedOfBundled B) bdlSubdivPred →
      BDLStepXMX (bdlPerturbedOfBundled B) bdlSubdivPred → Prop)
    (h_adj : ∀ a b, StepAdj a b →
      c1 a ≠ 0 ∧ c1 b ≠ 0 ∧
      (stepXMXOwnerX (bdlPerturbedOfBundled B) bdlSubdivPred a =
         stepXMXOwnerX (bdlPerturbedOfBundled B) bdlSubdivPred b ∨
       (c0 (stepXMXOwnerX (bdlPerturbedOfBundled B) bdlSubdivPred a) ≠ 0 ∧
        c0 (stepXMXOwnerX (bdlPerturbedOfBundled B) bdlSubdivPred b) ≠ 0 ∧
        Conn0 (stepXMXOwnerX (bdlPerturbedOfBundled B) bdlSubdivPred a)
          (stepXMXOwnerX (bdlPerturbedOfBundled B) bdlSubdivPred b)))) :
    let G1 := hierStepPkgBDLPrimal B h_inv G
    let C_hat_1 : Finset G1.V := extendHierClusterSupport C_hat_0 c1
    IsHierClusterWitness G1 (Relation.ReflTransGen StepAdj) (w0 + 11) c1 C_hat_1 ∧
    ((C_hat_0 ∩ G.R).Nonempty → (C_hat_1 ∩ G1.R).Nonempty) := by
  apply isHierClusterWitness_extend G (BDLPrimalVertLink B)
    (bdlPrimal_down_le B) (bdlPrimal_up_le B h_inv) hw0
  · have h_mul : w0 * syndromeWeightNat c0 ≤ w0 * syndromeWeightNat c1 :=
      Nat.mul_le_mul_left w0 h_wt_le
    rw [Nat.add_mul]
    omega
  · intro x0 hx0
    rw [← h_syn] at hx0
    exact exists_active_in_fiber_of_coarseSyndromeStepXMX_ne_zero
      (bdlPerturbedOfBundled B) bdlSubdivPred c1 x0 hx0
  · intro a b hab
    obtain ⟨ha, hb, h_same | ⟨hxa, hxb, hconn⟩⟩ := h_adj a b hab
    · exact ⟨ha, hb, Or.inl ⟨stepXMXOwnerX (bdlPerturbedOfBundled B) bdlSubdivPred a, rfl, h_same.symm⟩⟩
    · exact ⟨ha, hb, Or.inr ⟨_, _, hxa, hxb, hconn, rfl, rfl⟩⟩

/-- Single-step witness lift across `hierStepPkgBDLDual`. -/
lemma isHierClusterWitness_bdlDual (B : BundledCSSCode3D) (h_inv : HasBDLConeInvariants B)
    (G : HierStepPkg B.M_Z)
    {Conn0 : B.M_Z → B.M_Z → Prop} {w0 : ℕ} (hw0_le : w0 ≤ 54)
    {c0 : B.M_Z → ZMod 2}
    {c1 : BDLStepXMZ (bdlPerturbedOfBundled B) bdlSubdivPred → ZMod 2}
    {C_hat_0 : Finset G.V}
    (hw0 : IsHierClusterWitness G Conn0 w0 c0 C_hat_0)
    (h_syn : rxCleanedCoarseSyndrome (bdlPerturbedOfBundled B) bdlSubdivPred c1 = c0)
    (h_wt_le : 27 * syndromeWeightNat c0 ≤ 16 * syndromeWeightNat c1)
    (StepAdj : BDLStepXMZ (bdlPerturbedOfBundled B) bdlSubdivPred →
      BDLStepXMZ (bdlPerturbedOfBundled B) bdlSubdivPred → Prop)
    (h_adj : ∀ a b, StepAdj a b →
      c1 a ≠ 0 ∧ c1 b ≠ 0 ∧
      ((∃ z0 : B.M_Z,
          a ∈ fineTwoHopPool (bdlPerturbedOfBundled B) bdlSubdivPred {z0} ∧
          b ∈ fineTwoHopPool (bdlPerturbedOfBundled B) bdlSubdivPred {z0}) ∨
       (∃ z_a z_b : B.M_Z, c0 z_a ≠ 0 ∧ c0 z_b ≠ 0 ∧ Conn0 z_a z_b ∧
          a ∈ fineTwoHopPool (bdlPerturbedOfBundled B) bdlSubdivPred {z_a} ∧
          b ∈ fineTwoHopPool (bdlPerturbedOfBundled B) bdlSubdivPred {z_b}))) :
    let G1 := hierStepPkgBDLDual B h_inv G
    let C_hat_1 : Finset G1.V := extendHierClusterSupport C_hat_0 c1
    IsHierClusterWitness G1 (Relation.ReflTransGen StepAdj) 43 c1 C_hat_1 ∧
    ((C_hat_0 ∩ G.R).Nonempty → (C_hat_1 ∩ G1.R).Nonempty) := by
  apply isHierClusterWitness_extend G (BDLDualVertLink B)
    (bdlDual_down_le B h_inv) (bdlDual_up_le B h_inv) hw0
  · have h_mul : w0 * syndromeWeightNat c0 ≤ 54 * syndromeWeightNat c0 :=
      Nat.mul_le_mul_right _ hw0_le
    omega
  · intro z0 hz0
    rw [← h_syn] at hz0
    exact exists_active_in_fineTwoHopPool_of_rxCleanedCoarseSyndrome_ne_zero
      (bdlPerturbedOfBundled B) bdlSubdivPred c1 z0 hz0
  · exact h_adj

/-- Multiscale hierarchical check graph package for the primal X-check sector at level `k`. -/
def primalHierPkg : (k : ℕ) → HierStepPkg (bdlIteratedBundled (k + 1)).M_X
  | 0 =>
      let B := bdlIteratedBundled 0
      let h_inv_B := hasBDLConeInvariants_bdlIteratedBundled 0
      let B1 := bdlRandomStepX B
      let h_inv_B1 := hasBDLConeInvariants_dualBundled B1
        (hasBDLConeInvariants_bdlRandomStepX B h_inv_B)
      let G0 := hierStepPkgBase B.M_X card_bdlIterated0_le_32.1
      let G1 := hierStepPkgBDLPrimal B h_inv_B G0
      let G2 := hierStepPkgBDLDual (dualBundled B1) h_inv_B1 G1
      hierStepPkgResetRoot G2 card_bdlIterated1_le_nine_sq.1
  | k + 1 =>
      let B := bdlIteratedBundled (k + 1)
      let h_inv_B := hasBDLConeInvariants_bdlIteratedBundled (k + 1)
      let B1 := bdlRandomStepX B
      let h_inv_B1 := hasBDLConeInvariants_dualBundled B1
        (hasBDLConeInvariants_bdlRandomStepX B h_inv_B)
      let G1 := hierStepPkgBDLPrimal B h_inv_B (primalHierPkg k)
      hierStepPkgBDLDual (dualBundled B1) h_inv_B1 G1

/-- Primal step helper for the dual Z-check sector from `bdlRandomStepX (bdlIteratedBundled k)`
    to `bdlIteratedBundled (k + 1)`, resetting the root set at `k = 0`. -/
def dualStepMidHierPkg : (k : ℕ) →
    HierStepPkg (bdlRandomStepX (bdlIteratedBundled k)).M_Z →
    HierStepPkg (bdlIteratedBundled (k + 1)).M_Z
  | 0, G_prev =>
      let B := bdlIteratedBundled 0
      let B1 := bdlRandomStepX B
      let h_inv_B1 := hasBDLConeInvariants_dualBundled B1
        (hasBDLConeInvariants_bdlRandomStepX B (hasBDLConeInvariants_bdlIteratedBundled 0))
      hierStepPkgResetRoot
        (hierStepPkgBDLPrimal (dualBundled B1) h_inv_B1 G_prev)
        card_bdlIterated1_le_nine_sq.2
  | m + 1, G_prev =>
      let B := bdlIteratedBundled (m + 1)
      let B1 := bdlRandomStepX B
      let h_inv_B1 := hasBDLConeInvariants_dualBundled B1
        (hasBDLConeInvariants_bdlRandomStepX B (hasBDLConeInvariants_bdlIteratedBundled (m + 1)))
      hierStepPkgBDLPrimal (dualBundled B1) h_inv_B1 G_prev

/-- Multiscale hierarchical check graph package for the dual Z-check sector at odd half-step `2k+1`. -/
def dualHalfHierPkg : (k : ℕ) → HierStepPkg (bdlRandomStepX (bdlIteratedBundled k)).M_Z
  | 0 =>
      let B0 := bdlIteratedBundled 0
      let h_inv_B0 := hasBDLConeInvariants_bdlIteratedBundled 0
      hierStepPkgBDLDual B0 h_inv_B0 (hierStepPkgBase B0.M_Z card_bdlIterated0_le_32.2)
  | k + 1 =>
      let B_mid := bdlIteratedBundled (k + 1)
      let h_inv_mid := hasBDLConeInvariants_bdlIteratedBundled (k + 1)
      hierStepPkgBDLDual B_mid h_inv_mid (dualStepMidHierPkg k (dualHalfHierPkg k))

/-- Multiscale hierarchical check graph package for the dual Z-check sector at level `k`. -/
def dualHierPkg (k : ℕ) : HierStepPkg (bdlIteratedBundled (k + 1)).M_Z :=
  dualStepMidHierPkg k (dualHalfHierPkg k)

/-- Multiscale step adjacency across a primal step (matching `PrimalMultiscaleAdj`). -/
def PrimalStepAdjAux {Q M_Z M_X : Type}
    [Fintype Q] [DecidableEq Q] [Fintype M_Z] [DecidableEq M_Z] [Fintype M_X] [DecidableEq M_X]
    (pcode : CSSCode3D Q M_Z M_X) (M : ℕ)
    (Conn0 : M_X → M_X → Prop)
    (c0 : M_X → ZMod 2) (c1 : BDLStepXMX pcode M → ZMod 2)
    (a b : BDLStepXMX pcode M) : Prop :=
  c1 a ≠ 0 ∧ c1 b ≠ 0 ∧
  (stepXMXOwnerX pcode M a = stepXMXOwnerX pcode M b ∨
    (c0 (stepXMXOwnerX pcode M a) ≠ 0 ∧
     c0 (stepXMXOwnerX pcode M b) ≠ 0 ∧
     Conn0 (stepXMXOwnerX pcode M a) (stepXMXOwnerX pcode M b)))

/-- Multiscale step adjacency across a dual step (matching `DualMultiscaleAdj`). -/
def DualStepAdjAux {Q M_Z M_X : Type}
    [Fintype Q] [DecidableEq Q] [Fintype M_Z] [DecidableEq M_Z] [Fintype M_X] [DecidableEq M_X]
    (pcode : CSSCode3D Q M_Z M_X) (M : ℕ)
    (Conn0 : M_Z → M_Z → Prop)
    (c0 : M_Z → ZMod 2) (c1 : BDLStepXMZ pcode M → ZMod 2)
    (a b : BDLStepXMZ pcode M) : Prop :=
  c1 a ≠ 0 ∧ c1 b ≠ 0 ∧
  ((c1 a ≠ 0 ∧ c1 b ≠ 0 ∧
      ∃ z0 : M_Z, a ∈ fineTwoHopPool pcode M {z0} ∧ b ∈ fineTwoHopPool pcode M {z0}) ∨
    ∃ z_a z_b : M_Z,
      c0 z_a ≠ 0 ∧ c0 z_b ≠ 0 ∧ Conn0 z_a z_b ∧
      a ∈ fineTwoHopPool pcode M {z_a} ∧ b ∈ fineTwoHopPool pcode M {z_b})

/-- Base-level (`k = 0`) witness lift for `primalHierPkg 0`. -/
lemma primalHierPkg_base_lift
    {c0 : (bdlIteratedBundled 0).M_X → ZMod 2}
    {c1 : (bdlRandomStepX (bdlIteratedBundled 0)).M_X → ZMod 2}
    {c2 : (bdlIteratedBundled 1).M_X → ZMod 2}
    (hc2_ne : c2 ≠ 0)
    (h_syn1 : coarseSyndromeStepXMX (bdlPerturbedOfBundled (bdlIteratedBundled 0)) bdlSubdivPred c1 = c0)
    (h_wt1 : syndromeWeightNat c0 ≤ syndromeWeightNat c1)
    (h_syn2 : rxCleanedCoarseSyndrome
      (bdlPerturbedOfBundled (dualBundled (bdlRandomStepX (bdlIteratedBundled 0)))) bdlSubdivPred c2 = c1)
    (h_wt2 : 27 * syndromeWeightNat c1 ≤ 16 * syndromeWeightNat c2) :
    let B := bdlIteratedBundled 0
    let B1 := bdlRandomStepX B
    let Conn0 : B.M_X → B.M_X → Prop := fun a b => c0 a ≠ 0 ∧ c0 b ≠ 0
    let Conn1 : B1.M_X → B1.M_X → Prop :=
      Relation.ReflTransGen (PrimalStepAdjAux (bdlPerturbedOfBundled B) bdlSubdivPred Conn0 c0 c1)
    let Conn2 := Relation.ReflTransGen
      (DualStepAdjAux (bdlPerturbedOfBundled (dualBundled B1)) bdlSubdivPred Conn1 c1 c2)
    ∃ C_hat : Finset (primalHierPkg 0).V,
      IsHierClusterWitness (primalHierPkg 0) Conn2 43 c2 C_hat ∧
      (C_hat ∩ (primalHierPkg 0).R).Nonempty := by
  let B := bdlIteratedBundled 0
  let h_inv_B := hasBDLConeInvariants_bdlIteratedBundled 0
  let B1 := bdlRandomStepX B
  let h_inv_B1 := hasBDLConeInvariants_dualBundled B1
    (hasBDLConeInvariants_bdlRandomStepX B h_inv_B)
  let Conn0 : B.M_X → B.M_X → Prop := fun a b => c0 a ≠ 0 ∧ c0 b ≠ 0
  let Conn1 : B1.M_X → B1.M_X → Prop :=
    Relation.ReflTransGen (PrimalStepAdjAux (bdlPerturbedOfBundled B) bdlSubdivPred Conn0 c0 c1)
  have hw0 := isHierClusterWitness_base card_bdlIterated0_le_32.1 c0
  have hw1 := (isHierClusterWitness_bdlPrimal B h_inv_B _ hw0 h_syn1 h_wt1
    (PrimalStepAdjAux (bdlPerturbedOfBundled B) bdlSubdivPred Conn0 c0 c1)
    (fun _ _ h => h)).1
  have hw2 := (isHierClusterWitness_bdlDual (dualBundled B1) h_inv_B1 _ (by decide : 22 ≤ 54)
    hw1 h_syn2 h_wt2
    (DualStepAdjAux (bdlPerturbedOfBundled (dualBundled B1)) bdlSubdivPred Conn1 c1 c2)
    (fun _ _ h => ⟨h.1, h.2.1, h.2.2.imp (fun h2 => h2.2.2) id⟩)).1
  exact ⟨_, isHierClusterWitness_resetRoot _ card_bdlIterated1_le_nine_sq.1 hw2 hc2_ne⟩

/-- Inductive-step (`k + 1`) witness lift for `primalHierPkg (k + 1)`. -/
lemma primalHierPkg_succ_lift (k : ℕ)
    {Conn0 : (bdlIteratedBundled (k + 1)).M_X → (bdlIteratedBundled (k + 1)).M_X → Prop}
    {c0 : (bdlIteratedBundled (k + 1)).M_X → ZMod 2}
    {c1 : (bdlRandomStepX (bdlIteratedBundled (k + 1))).M_X → ZMod 2}
    {c2 : (bdlIteratedBundled (k + 2)).M_X → ZMod 2}
    {C_hat_0 : Finset (primalHierPkg k).V}
    (hw0 : IsHierClusterWitness (primalHierPkg k) Conn0 43 c0 C_hat_0)
    (hR0 : (C_hat_0 ∩ (primalHierPkg k).R).Nonempty)
    (h_syn1 : coarseSyndromeStepXMX (bdlPerturbedOfBundled (bdlIteratedBundled (k + 1))) bdlSubdivPred c1 = c0)
    (h_wt1 : syndromeWeightNat c0 ≤ syndromeWeightNat c1)
    (h_syn2 : rxCleanedCoarseSyndrome
      (bdlPerturbedOfBundled (dualBundled (bdlRandomStepX (bdlIteratedBundled (k + 1))))) bdlSubdivPred c2 = c1)
    (h_wt2 : 27 * syndromeWeightNat c1 ≤ 16 * syndromeWeightNat c2) :
    let B := bdlIteratedBundled (k + 1)
    let B1 := bdlRandomStepX B
    let Conn1 : B1.M_X → B1.M_X → Prop :=
      Relation.ReflTransGen (PrimalStepAdjAux (bdlPerturbedOfBundled B) bdlSubdivPred Conn0 c0 c1)
    let Conn2 := Relation.ReflTransGen
      (DualStepAdjAux (bdlPerturbedOfBundled (dualBundled B1)) bdlSubdivPred Conn1 c1 c2)
    ∃ C_hat : Finset (primalHierPkg (k + 1)).V,
      IsHierClusterWitness (primalHierPkg (k + 1)) Conn2 43 c2 C_hat ∧
      (C_hat ∩ (primalHierPkg (k + 1)).R).Nonempty := by
  let B := bdlIteratedBundled (k + 1)
  let h_inv_B := hasBDLConeInvariants_bdlIteratedBundled (k + 1)
  let B1 := bdlRandomStepX B
  let h_inv_B1 := hasBDLConeInvariants_dualBundled B1
    (hasBDLConeInvariants_bdlRandomStepX B h_inv_B)
  let Conn1 : B1.M_X → B1.M_X → Prop :=
    Relation.ReflTransGen (PrimalStepAdjAux (bdlPerturbedOfBundled B) bdlSubdivPred Conn0 c0 c1)
  have h1 := isHierClusterWitness_bdlPrimal B h_inv_B (primalHierPkg k) hw0 h_syn1 h_wt1
    (PrimalStepAdjAux (bdlPerturbedOfBundled B) bdlSubdivPred Conn0 c0 c1)
    (fun _ _ h => h)
  have h2 := isHierClusterWitness_bdlDual (dualBundled B1) h_inv_B1 _ (by decide : 54 ≤ 54)
    h1.1 h_syn2 h_wt2
    (DualStepAdjAux (bdlPerturbedOfBundled (dualBundled B1)) bdlSubdivPred Conn1 c1 c2)
    (fun _ _ h => ⟨h.1, h.2.1, h.2.2.imp (fun h2 => h2.2.2) id⟩)
  exact ⟨_, h2.1, h2.2 (h1.2 hR0)⟩

/-- Witness lift across `dualStepMidHierPkg k`. -/
lemma dualStepMidHierPkg_lift (k : ℕ)
    (G_prev : HierStepPkg (bdlRandomStepX (bdlIteratedBundled k)).M_Z)
    {Conn_prev : (bdlRandomStepX (bdlIteratedBundled k)).M_Z →
      (bdlRandomStepX (bdlIteratedBundled k)).M_Z → Prop}
    {c_prev : (bdlRandomStepX (bdlIteratedBundled k)).M_Z → ZMod 2}
    {c_mid : (bdlIteratedBundled (k + 1)).M_Z → ZMod 2}
    {C_hat_prev : Finset G_prev.V}
    (hw_prev : IsHierClusterWitness G_prev Conn_prev 43 c_prev C_hat_prev)
    (h_R_prev : 0 < k → (C_hat_prev ∩ G_prev.R).Nonempty)
    (h_mid_ne : k = 0 → c_mid ≠ 0)
    (h_syn1 : coarseSyndromeStepXMX
      (bdlPerturbedOfBundled (dualBundled (bdlRandomStepX (bdlIteratedBundled k))))
      bdlSubdivPred c_mid = c_prev)
    (h_wt1 : syndromeWeightNat c_prev ≤ syndromeWeightNat c_mid) :
    ∃ C_hat_mid : Finset (dualStepMidHierPkg k G_prev).V,
      IsHierClusterWitness (dualStepMidHierPkg k G_prev)
        (Relation.ReflTransGen (PrimalStepAdjAux
          (bdlPerturbedOfBundled (dualBundled (bdlRandomStepX (bdlIteratedBundled k))))
          bdlSubdivPred Conn_prev c_prev c_mid))
        54 c_mid C_hat_mid ∧
      (C_hat_mid ∩ (dualStepMidHierPkg k G_prev).R).Nonempty := by
  cases k with
  | zero =>
    let B := bdlIteratedBundled 0
    let B1 := bdlRandomStepX B
    let h_inv_B1 := hasBDLConeInvariants_dualBundled B1
      (hasBDLConeInvariants_bdlRandomStepX B (hasBDLConeInvariants_bdlIteratedBundled 0))
    have h1 := isHierClusterWitness_bdlPrimal (dualBundled B1) h_inv_B1 G_prev hw_prev
      h_syn1 h_wt1
      (PrimalStepAdjAux (bdlPerturbedOfBundled (dualBundled B1)) bdlSubdivPred
        Conn_prev c_prev c_mid)
      (fun _ _ h => h)
    exact ⟨_, isHierClusterWitness_resetRoot _ card_bdlIterated1_le_nine_sq.2 h1.1 (h_mid_ne rfl)⟩
  | succ m =>
    let B := bdlIteratedBundled (m + 1)
    let B1 := bdlRandomStepX B
    let h_inv_B1 := hasBDLConeInvariants_dualBundled B1
      (hasBDLConeInvariants_bdlRandomStepX B (hasBDLConeInvariants_bdlIteratedBundled (m + 1)))
    have h1 := isHierClusterWitness_bdlPrimal (dualBundled B1) h_inv_B1 G_prev hw_prev
      h_syn1 h_wt1
      (PrimalStepAdjAux (bdlPerturbedOfBundled (dualBundled B1)) bdlSubdivPred
        Conn_prev c_prev c_mid)
      (fun _ _ h => h)
    exact ⟨_, h1.1, h1.2 (h_R_prev (Nat.succ_pos m))⟩

/-- Base-level (`k = 0`) witness lift for `dualHalfHierPkg 0`. -/
lemma dualHalfHierPkg_base_lift
    {c0 : (bdlIteratedBundled 0).M_Z → ZMod 2}
    {c1 : (bdlRandomStepX (bdlIteratedBundled 0)).M_Z → ZMod 2}
    (h_syn : rxCleanedCoarseSyndrome (bdlPerturbedOfBundled (bdlIteratedBundled 0)) bdlSubdivPred c1 = c0)
    (h_wt : 27 * syndromeWeightNat c0 ≤ 16 * syndromeWeightNat c1) :
    let B0 := bdlIteratedBundled 0
    let Conn0 : B0.M_Z → B0.M_Z → Prop := fun a b => c0 a ≠ 0 ∧ c0 b ≠ 0
    let Conn1 := Relation.ReflTransGen
      (DualStepAdjAux (bdlPerturbedOfBundled B0) bdlSubdivPred Conn0 c0 c1)
    ∃ C_hat : Finset (dualHalfHierPkg 0).V,
      IsHierClusterWitness (dualHalfHierPkg 0) Conn1 43 c1 C_hat ∧
      (0 < 0 → (C_hat ∩ (dualHalfHierPkg 0).R).Nonempty) := by
  let B0 := bdlIteratedBundled 0
  let h_inv_B0 := hasBDLConeInvariants_bdlIteratedBundled 0
  let Conn0 : B0.M_Z → B0.M_Z → Prop := fun a b => c0 a ≠ 0 ∧ c0 b ≠ 0
  have hw0 := isHierClusterWitness_base card_bdlIterated0_le_32.2 c0
  have h1 := isHierClusterWitness_bdlDual B0 h_inv_B0 _ (by decide : 11 ≤ 54)
    hw0 h_syn h_wt
    (DualStepAdjAux (bdlPerturbedOfBundled B0) bdlSubdivPred Conn0 c0 c1)
    (fun _ _ h => ⟨h.1, h.2.1, h.2.2.imp (fun h2 => h2.2.2) id⟩)
  exact ⟨_, h1.1, fun h_pos => by omega⟩

/-- Inductive-step (`k + 1`) witness lift for `dualHalfHierPkg (k + 1)`. -/
lemma dualHalfHierPkg_succ_lift (k : ℕ)
    {Conn_prev : (bdlRandomStepX (bdlIteratedBundled k)).M_Z →
      (bdlRandomStepX (bdlIteratedBundled k)).M_Z → Prop}
    {c_prev : (bdlRandomStepX (bdlIteratedBundled k)).M_Z → ZMod 2}
    {c_mid : (bdlIteratedBundled (k + 1)).M_Z → ZMod 2}
    {c_top : (bdlRandomStepX (bdlIteratedBundled (k + 1))).M_Z → ZMod 2}
    {C_hat_prev : Finset (dualHalfHierPkg k).V}
    (hw_prev : IsHierClusterWitness (dualHalfHierPkg k) Conn_prev 43 c_prev C_hat_prev)
    (hR_prev : 0 < k → (C_hat_prev ∩ (dualHalfHierPkg k).R).Nonempty)
    (hc_prev_ne : c_prev ≠ 0)
    (h_syn1 : coarseSyndromeStepXMX
      (bdlPerturbedOfBundled (dualBundled (bdlRandomStepX (bdlIteratedBundled k))))
      bdlSubdivPred c_mid = c_prev)
    (h_wt1 : syndromeWeightNat c_prev ≤ syndromeWeightNat c_mid)
    (h_syn2 : rxCleanedCoarseSyndrome
      (bdlPerturbedOfBundled (bdlIteratedBundled (k + 1))) bdlSubdivPred c_top = c_mid)
    (h_wt2 : 27 * syndromeWeightNat c_mid ≤ 16 * syndromeWeightNat c_top) :
    let B_half := bdlRandomStepX (bdlIteratedBundled k)
    let B_mid := bdlIteratedBundled (k + 1)
    let Conn_mid := Relation.ReflTransGen
      (PrimalStepAdjAux (bdlPerturbedOfBundled (dualBundled B_half)) bdlSubdivPred
        Conn_prev c_prev c_mid)
    let Conn_top := Relation.ReflTransGen
      (DualStepAdjAux (bdlPerturbedOfBundled B_mid) bdlSubdivPred Conn_mid c_mid c_top)
    ∃ C_hat_top : Finset (dualHalfHierPkg (k + 1)).V,
      IsHierClusterWitness (dualHalfHierPkg (k + 1)) Conn_top 43 c_top C_hat_top ∧
      (0 < k + 1 → (C_hat_top ∩ (dualHalfHierPkg (k + 1)).R).Nonempty) := by
  let B_half := bdlRandomStepX (bdlIteratedBundled k)
  let B_mid := bdlIteratedBundled (k + 1)
  let h_inv_mid := hasBDLConeInvariants_bdlIteratedBundled (k + 1)
  have hc_mid_ne : c_mid ≠ 0 := by
    intro h_zero
    obtain ⟨x0, hx0⟩ := Function.ne_iff.mp hc_prev_ne
    rw [← h_syn1] at hx0
    obtain ⟨a, _, ha⟩ := exists_active_in_fiber_of_coarseSyndromeStepXMX_ne_zero
      (bdlPerturbedOfBundled (dualBundled B_half)) bdlSubdivPred c_mid x0 hx0
    exact ha (congr_fun h_zero a)
  obtain ⟨C_hat_mid, hw_mid, hR_mid⟩ := dualStepMidHierPkg_lift k (dualHalfHierPkg k)
    hw_prev hR_prev (fun _ => hc_mid_ne) h_syn1 h_wt1
  let Conn_mid := Relation.ReflTransGen
    (PrimalStepAdjAux (bdlPerturbedOfBundled (dualBundled B_half)) bdlSubdivPred
      Conn_prev c_prev c_mid)
  have h2 := isHierClusterWitness_bdlDual B_mid h_inv_mid _ (by decide : 54 ≤ 54)
    hw_mid h_syn2 h_wt2
    (DualStepAdjAux (bdlPerturbedOfBundled B_mid) bdlSubdivPred Conn_mid c_mid c_top)
    (fun _ _ h => ⟨h.1, h.2.1, h.2.2.imp (fun h2 => h2.2.2) id⟩)
  exact ⟨_, h2.1, fun _ => h2.2 hR_mid⟩

end BDLDecoder
end WeldedHierarchy

end
