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

import Proofs.Step1LLLDensity.DominantCramerCascade

/-!
# Discrete Product-Grid Conditional Bad-Vertex Lovasz Local Lemma

Proves finite product-grid Lovasz Local Lemma existence theorems (`exists_good_assignment_of_cylinder_lll` and `exists_good_assignment_of_conditional_bad_vertices_lll`) via inductive cylinder counting over finite configuration spaces. Shows that uniform bounds on single-vertex bad-parameter multiplicity, candidate set size, and support-overlap degree guarantee the existence of a globally valid grid assignment avoiding all bad events.

## References

* Part I, Section 2.2 (`subsec:step1-lll`), Proposition 2.4 (`prop:step1-lll`)
-/

noncomputable section
open scoped Classical BigOperators
namespace WeldedHierarchy

/-! ## 1. Constructive Telescoping Lovász Local Lemma on Cylinder Events -/

/-- **Pure Natural-Number Telescoping Lovász Local Lemma (`exists_good_assignment_of_cylinder_lll`)**:
    For any finite family of bad cylinder events `Bad : T → Finset (V → α)` where `Bad t` depends only on
    `support t : Finset V`, has local dependency degree `≤ Γ` (`(univ.filter (¬ Disjoint (support t0) (support ·))).card ≤ Γ`),
    and satisfies `(Bad t).card * (4 * (Γ + 1)) ≤ univ.card`, there exists a global assignment `ω : V → α`
    avoiding `Bad t` for all `t : T` simultaneously (with zero dependence on `Fintype.card T` or `Fintype.card V`). -/
lemma exists_good_assignment_of_cylinder_lll {T V α : Type*}
    [Fintype T] [DecidableEq T] [Fintype V] [DecidableEq V] [Fintype α] [DecidableEq α] [Nonempty α]
    (support : T → Finset V) (Bad : T → Finset (V → α)) (Γ : ℕ)
    (h_cyl : ∀ (t : T) (ω1 ω2 : V → α), (∀ x ∈ support t, ω1 x = ω2 x) → (ω1 ∈ Bad t ↔ ω2 ∈ Bad t))
    (h_dep : ∀ t0 : T, (Finset.univ.filter (fun t : T => ¬ Disjoint (support t0) (support t))).card ≤ Γ)
    (h_prob : ∀ t0 : T, (Bad t0).card * (4 * (Γ + 1)) ≤ (Finset.univ : Finset (V → α)).card) :
    ∃ ω : V → α, ∀ t : T, ω ∉ Bad t := by
  -- Step 1: Establish initial algebraic and geometric reductions for `exists_good_assignment_of_cylinder_lll`
  let Good : Finset T → Finset (V → α) := fun E =>
    Finset.univ.filter (fun ω : V → α => ∀ t ∈ E, ω ∉ Bad t)
  have h_mono : ∀ {A B : Finset T}, A ⊆ B → (Good B).card ≤ (Good A).card := by
    intro A B hAB
    refine Finset.card_le_card (fun ω hω => ?_)
    rw [Finset.mem_filter] at hω ⊢
    exact ⟨hω.1, fun t ht => hω.2 t (hAB ht)⟩
  have h_univ_pos : 0 < (Finset.univ : Finset (V → α)).card := Finset.card_pos.mpr ⟨fun _ => Classical.arbitrary α, Finset.mem_univ _⟩
  have h_step_all : ∀ n : ℕ, ∀ S : Finset T, S.card = n → ∀ t0 : T,
      ((Good S).card - (Good (insert t0 S)).card) * (2 * (Γ + 1)) ≤ (Good S).card := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro S hS_card t0
      let Nhd : Finset T := S.filter (fun t : T => ¬ Disjoint (support t0) (support t))
      let S' : Finset T := S \ Nhd
      have h_union : S' ∪ Nhd = S := Finset.sdiff_union_of_subset (Finset.filter_subset _ S)
      have hNhd_card : Nhd.card ≤ Γ := by
        refine le_trans (Finset.card_le_card (fun t ht => ?_)) (h_dep t0)
        rw [Finset.mem_filter] at ht ⊢
        exact ⟨Finset.mem_univ t, ht.2⟩
      have h_tele : ((Good S').card - (Good S).card) * (2 * (Γ + 1)) ≤ Nhd.card * (Good S').card := by
        rw [← h_union]
        refine sub_mul_le_card_mul_of_insert_step (fun A => (Good A).card) S' Nhd (2 * (Γ + 1)) (Good S').card ?_
        intro A t hS'A hA_sub ht_Nhd ht_not_A
        have hA_ssub : A ⊂ S := by
          rw [h_union] at hA_sub
          exact Finset.ssubset_iff_subset_ne.mpr ⟨hA_sub, fun h_eq => ht_not_A (h_eq ▸ (Finset.mem_filter.mp ht_Nhd).1)⟩
        have hA_lt : A.card < n := hS_card ▸ Finset.card_lt_card hA_ssub
        exact le_trans (ih A.card hA_lt A rfl t) (h_mono hS'A)
      have hS'_le_two : (Good S').card ≤ 2 * (Good S).card := by
        have h1 : ((Good S').card - (Good S).card) * (2 * (Γ + 1)) ≤ (Γ + 1) * (Good S').card :=
          le_trans h_tele (Nat.mul_le_mul_right _ (le_trans hNhd_card (Nat.le_succ Γ)))
        have h2 : (Good S).card ≤ (Good S').card := h_mono Finset.sdiff_subset
        have h1_mul : ((Good S').card - (Good S).card) * 2 * (Γ + 1) ≤ (Good S').card * (Γ + 1) := by
          linarith [h1]
        have h1_div : ((Good S').card - (Good S).card) * 2 ≤ (Good S').card :=
          Nat.le_of_mul_le_mul_right h1_mul (Nat.succ_pos Γ)
        omega
      have h_diff_le : (Good S).card - (Good (insert t0 S)).card ≤
          (Finset.univ.filter (fun ω : V → α => ω ∈ Bad t0 ∧ ∀ t ∈ S', ω ∉ Bad t)).card := by
        have h_sdiff : Good S \ Good (insert t0 S) ⊆
            Finset.univ.filter (fun ω : V → α => ω ∈ Bad t0 ∧ ∀ t ∈ S', ω ∉ Bad t) := by
          intro ω hω
          rw [Finset.mem_sdiff, Finset.mem_filter, Finset.mem_filter] at hω
          rw [Finset.mem_filter]
          refine ⟨Finset.mem_univ ω, ?_, fun t ht => hω.1.2 t (Finset.sdiff_subset ht)⟩
          by_contra h_not_bad
          exact hω.2 ⟨Finset.mem_univ ω, fun t ht => by
            rcases Finset.mem_insert.mp ht with rfl | htS
            -- Step 2: Complete the main case analysis and bound assembly for `exists_good_assignment_of_cylinder_lll`
            · exact h_not_bad
            · exact hω.1.2 t htS⟩
        exact le_trans (Nat.sub_le_iff_le_add.mpr (by
          have h_sub_good : Good (insert t0 S) ⊆ Good S := by
            intro a ha
            rw [Finset.mem_filter] at ha ⊢
            exact ⟨Finset.mem_univ a, fun t ht => ha.2 t (Finset.mem_insert_of_mem ht)⟩
          have h_add := Finset.card_sdiff_add_card_eq_card h_sub_good
          omega)) (Finset.card_le_card h_sdiff)
      have h_cyl_S' : (Finset.univ.filter (fun ω : V → α => ω ∈ Bad t0 ∧ ∀ t ∈ S', ω ∉ Bad t)).card *
          (Finset.univ : Finset (V → α)).card = (Bad t0).card * (Good S').card := by
        have h_eq_bad : Finset.univ.filter (fun ω : V → α => ω ∈ Bad t0) = Bad t0 := by
          ext ω; simp
        have h_ind := card_filter_and_mul_card_univ_eq_of_cylinder (support t0)
          (fun ω => ω ∈ Bad t0) (fun ω => ∀ t ∈ S', ω ∉ Bad t)
          (fun ω1 ω2 h => h_cyl t0 ω1 ω2 h)
          (fun ω1 ω2 h => by
            refine forall_congr' (fun t => imp_congr_right (fun ht => not_congr (h_cyl t ω1 ω2 ?_)))
            intro x hx
            -- Step 3: Conclude final cardinality and norm estimates for `exists_good_assignment_of_cylinder_lll`
            have h_disj : Disjoint (support t0) (support t) := by
              rw [Finset.mem_sdiff, Finset.mem_filter] at ht
              by_contra h_nd
              exact ht.2 ⟨ht.1, h_nd⟩
            exact h x (Finset.disjoint_right.mp h_disj hx))
        rw [h_eq_bad] at h_ind
        exact h_ind
      have h_mul_le : ((Good S).card - (Good (insert t0 S)).card) * (2 * (Γ + 1)) * (Finset.univ : Finset (V → α)).card ≤
          (Good S).card * (Finset.univ : Finset (V → α)).card := by
        calc ((Good S).card - (Good (insert t0 S)).card) * (2 * (Γ + 1)) * (Finset.univ : Finset (V → α)).card
          _ ≤ (Finset.univ.filter (fun ω : V → α => ω ∈ Bad t0 ∧ ∀ t ∈ S', ω ∉ Bad t)).card *
                (2 * (Γ + 1)) * (Finset.univ : Finset (V → α)).card :=
            Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ h_diff_le)
          _ = ((Finset.univ.filter (fun ω : V → α => ω ∈ Bad t0 ∧ ∀ t ∈ S', ω ∉ Bad t)).card *
                (Finset.univ : Finset (V → α)).card) * (2 * (Γ + 1)) := by ring
          _ = (Bad t0).card * (Good S').card * (2 * (Γ + 1)) := by rw [h_cyl_S']
          _ ≤ (Bad t0).card * (2 * (Good S).card) * (2 * (Γ + 1)) :=
            Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ hS'_le_two)
          _ = ((Bad t0).card * (4 * (Γ + 1))) * (Good S).card := by ring
          _ ≤ (Finset.univ : Finset (V → α)).card * (Good S).card :=
            Nat.mul_le_mul_right _ (h_prob t0)
          _ = (Good S).card * (Finset.univ : Finset (V → α)).card := Nat.mul_comm _ _
      exact Nat.le_of_mul_le_mul_right h_mul_le h_univ_pos
  have h_pos_all : ∀ E : Finset T, 0 < (Good E).card := by
    intro E
    induction E using Finset.induction_on with
    | empty =>
      have h_eq : Good ∅ = Finset.univ := by ext ω; simp [Good]
      rw [h_eq]; exact h_univ_pos
    | @insert t0 E ht0 ih =>
      have h_step := h_step_all E.card E rfl t0
      have h_two : ((Good E).card - (Good (insert t0 E)).card) * 2 ≤ (Good E).card :=
        le_trans (Nat.mul_le_mul_left _ (by omega : 2 ≤ 2 * (Γ + 1))) h_step
      omega
  obtain ⟨ω, hω⟩ := Finset.card_pos.mp (h_pos_all Finset.univ)
  exact ⟨ω, fun t => (Finset.mem_filter.mp hω).2 t (Finset.mem_univ t)⟩

/-! ## 2. Coordinate-Swap Involution Fiber Bounds -/

/-- **Single-Coordinate Swap Involution Fiber Bound (`card_filter_badSet_and_mul_card_le`)**:
    If `P1 : (V → α) → Prop` and `badSet : (V → α) → Finset α` do not depend on `ω x0`,
    and `(badSet ω).card ≤ K` for all `ω`, then
    `(univ.filter (fun ω => ω x0 ∈ badSet ω ∧ P1 ω)).card * univ.card ≤ (univ.filter P1).card * K`. -/
lemma card_filter_badSet_and_mul_card_le {V α : Type*} [Fintype V] [DecidableEq V] [Fintype α] [DecidableEq α]
    (x0 : V) (K : ℕ) (badSet : (V → α) → Finset α) (P1 : (V → α) → Prop) [DecidablePred P1]
    (h_bad_indep : ∀ ω1 ω2 : V → α, (∀ x ≠ x0, ω1 x = ω2 x) → badSet ω1 = badSet ω2)
    (h_P1_indep : ∀ ω1 ω2 : V → α, (∀ x ≠ x0, ω1 x = ω2 x) → (P1 ω1 ↔ P1 ω2))
    (h_bad_card : ∀ ω : V → α, (badSet ω).card ≤ K) :
    (Finset.univ.filter (fun ω : V → α => ω x0 ∈ badSet ω ∧ P1 ω)).card * (Finset.univ : Finset α).card ≤
      (Finset.univ.filter P1).card * K := by
  -- Step 1: Establish initial algebraic and geometric reductions for `card_filter_badSet_and_mul_card_le`
  let S_lhs : Finset ((V → α) × α) :=
    (Finset.univ.filter (fun ω : V → α => ω x0 ∈ badSet ω ∧ P1 ω)) ×ˢ (Finset.univ : Finset α)
  let S_rhs : Finset ((V → α) × α) :=
    (Finset.univ.filter P1).biUnion (fun ω' => (badSet ω').map ⟨fun i => (ω', i), fun _ _ h => (Prod.mk.injEq _ _ _ _).mp h |>.2⟩)
  let swapAt : (V → α) × α → (V → α) × α :=
    fun p => (Function.update p.1 x0 p.2, p.1 x0)
  have h_invo : ∀ p : (V → α) × α, swapAt (swapAt p) = p := by
    intro ⟨ω, j⟩
    dsimp [swapAt]
    ext x
    · by_cases hx : x = x0
      · subst hx; simp
      · simp [hx]
    · simp
  have h_le_card : S_lhs.card ≤ S_rhs.card := by
    refine Finset.card_le_card_of_injOn swapAt ?_ ?_
    -- Step 2: Complete the main case analysis and bound assembly for `card_filter_badSet_and_mul_card_le`
    · intro ⟨ω, j⟩ hp
      simp only [S_lhs, Finset.mem_coe, Finset.mem_product, Finset.mem_filter, Finset.mem_univ, true_and, and_true] at hp
      simp only [S_rhs, swapAt, Finset.mem_coe, Finset.mem_biUnion, Finset.mem_filter, Finset.mem_univ, true_and,
                 Finset.mem_map, Function.Embedding.coeFn_mk]
      have h_agree : ∀ x ≠ x0, Function.update ω x0 j x = ω x := fun x hx => Function.update_of_ne hx j ω
      refine ⟨Function.update ω x0 j, (h_P1_indep _ ω h_agree).mpr hp.2, ω x0, ?_, rfl⟩
      rw [h_bad_indep _ ω h_agree]
      exact hp.1
    · intro p1 _ p2 _ h_eq
      rw [← h_invo p1, ← h_invo p2, h_eq]
  have h_rhs_le : S_rhs.card ≤ (Finset.univ.filter P1).card * K := by
    calc S_rhs.card
      _ ≤ ∑ ω' ∈ Finset.univ.filter P1, ((badSet ω').map ⟨fun i => (ω', i), fun _ _ h => (Prod.mk.injEq _ _ _ _).mp h |>.2⟩).card :=
        Finset.card_biUnion_le
      _ = ∑ ω' ∈ Finset.univ.filter P1, (badSet ω').card := by simp
      _ ≤ ∑ _ω' ∈ Finset.univ.filter P1, K := Finset.sum_le_sum (fun ω' _ => h_bad_card ω')
      _ = (Finset.univ.filter P1).card * K := by simp
  rw [Finset.card_product] at h_le_card
  exact le_trans h_le_card h_rhs_le

/-- **Conditional-Fiber Product Bound (`card_filter_forall_mem_badSet_mul_pow_le`)**:
    For any subset `Y : Finset V`, if for every `x ∈ Y`, `badSet x ω : Finset α` has cardinality `≤ K`
    and does not depend on `ω|_Y` (`(∀ v ∉ Y, ω1 v = ω2 v) → badSet x ω1 = badSet x ω2`), then
    `(univ.filter (fun ω => ∀ x ∈ Y, ω x ∈ badSet x ω)).card * (Fintype.card α) ^ Y.card ≤ univ.card * K ^ Y.card`. -/
lemma card_filter_forall_mem_badSet_mul_pow_le {V α : Type*} [Fintype V] [DecidableEq V] [Fintype α] [DecidableEq α]
    (K : ℕ) (badSet : V → (V → α) → Finset α)
    (h_card : ∀ (x : V) (ω : V → α), (badSet x ω).card ≤ K)
    (Y : Finset V)
    (h_indep : ∀ x ∈ Y, ∀ ω1 ω2 : V → α, (∀ v ∉ Y, ω1 v = ω2 v) → badSet x ω1 = badSet x ω2) :
    (Finset.univ.filter (fun ω : V → α => ∀ x ∈ Y, ω x ∈ badSet x ω)).card * (Fintype.card α) ^ Y.card ≤
      (Finset.univ : Finset (V → α)).card * K ^ Y.card := by
  -- Step 1: Establish initial algebraic and geometric reductions for `card_filter_forall_mem_badSet_mul_pow_le`
  induction Y using Finset.induction_on with
  | empty =>
    simp
  | @insert x0 Y hx0 ih =>
    have h_indep_Y : ∀ x ∈ Y, ∀ ω1 ω2 : V → α, (∀ v ∉ Y, ω1 v = ω2 v) → badSet x ω1 = badSet x ω2 := by
      intro x hx ω1 ω2 h_eq
      exact h_indep x (Finset.mem_insert_of_mem hx) ω1 ω2 (fun v hv => h_eq v (fun hvY => hv (Finset.mem_insert_of_mem hvY)))
    have h_ih := ih h_indep_Y
    let P1 : (V → α) → Prop := fun ω => ∀ x ∈ Y, ω x ∈ badSet x ω
    have h_eq_filter : Finset.univ.filter (fun ω : V → α => ∀ x ∈ insert x0 Y, ω x ∈ badSet x ω) =
        Finset.univ.filter (fun ω : V → α => ω x0 ∈ badSet x0 ω ∧ P1 ω) := by
      ext ω; simp [P1]
    have h_x0_indep : ∀ ω1 ω2 : V → α, (∀ v ≠ x0, ω1 v = ω2 v) → badSet x0 ω1 = badSet x0 ω2 := by
      intro ω1 ω2 h_eq
      -- Step 2: Complete the main case analysis and bound assembly for `card_filter_forall_mem_badSet_mul_pow_le`
      exact h_indep x0 (Finset.mem_insert_self x0 Y) ω1 ω2 (fun v hv => h_eq v (fun h_eq_x0 => hv (h_eq_x0 ▸ Finset.mem_insert_self x0 Y)))
    have h_P1_indep : ∀ ω1 ω2 : V → α, (∀ v ≠ x0, ω1 v = ω2 v) → (P1 ω1 ↔ P1 ω2) := by
      intro ω1 ω2 h_eq
      refine forall_congr' (fun x => imp_congr_right (fun hx => ?_))
      have hx_ne : x ≠ x0 := fun h => hx0 (h ▸ hx)
      have h_b : badSet x ω1 = badSet x ω2 :=
        h_indep x (Finset.mem_insert_of_mem hx) ω1 ω2 (fun v hv => h_eq v (fun h_eq_x0 => hv (h_eq_x0 ▸ Finset.mem_insert_self x0 Y)))
      rw [h_eq x hx_ne, h_b]
    have h_step := card_filter_badSet_and_mul_card_le x0 K (badSet x0) P1 h_x0_indep h_P1_indep (h_card x0)
    rw [Finset.card_univ] at h_step
    rw [h_eq_filter, Finset.card_insert_of_notMem hx0, Nat.pow_succ, Nat.pow_succ]
    calc (Finset.univ.filter (fun ω : V → α => ω x0 ∈ badSet x0 ω ∧ P1 ω)).card * ((Fintype.card α) ^ Y.card * Fintype.card α)
      _ = ((Finset.univ.filter (fun ω : V → α => ω x0 ∈ badSet x0 ω ∧ P1 ω)).card * Fintype.card α) * (Fintype.card α) ^ Y.card := by ring
      _ ≤ ((Finset.univ.filter P1).card * K) * (Fintype.card α) ^ Y.card := Nat.mul_le_mul_right _ h_step
      _ = ((Finset.univ.filter P1).card * (Fintype.card α) ^ Y.card) * K := by ring
      _ ≤ ((Finset.univ : Finset (V → α)).card * K ^ Y.card) * K := Nat.mul_le_mul_right K h_ih
      _ = (Finset.univ : Finset (V → α)).card * (K ^ Y.card * K) := by ring

/-! ## 3. Conditional Bad-Vertex Lovász Local Lemma -/

/-- **Conditional-Fiber Bad-Vertex Multiplicity LLL (`exists_good_assignment_of_conditional_bad_vertices_lll`)**:
    If every event `t : T` has total support `support t : Finset V`, candidate subset `candV t ⊆ support t` of size `≤ L`,
    and conditional bad-index sets `badSet t x ω : Finset (Fin (N + 1))` of size `≤ K` that depend only on `ω|_(support t \ candV t)`,
    then whenever `((K * L) ^ (M + 1)) * (4 * (Γ + 1)) ≤ (N + 1) ^ (M + 1)`, there exists `ω : V → Fin (N + 1)`
    such that every `t : T` has at most `M` bad vertices in `candV t`. -/
lemma exists_good_assignment_of_conditional_bad_vertices_lll {T V : Type*}
    [Fintype T] [DecidableEq T] [Fintype V] [DecidableEq V]
    {N K L M Γ : ℕ}
    (support : T → Finset V)
    (candV : T → Finset V)
    (badSet : T → V → (V → Fin (N + 1)) → Finset (Fin (N + 1)))
    (h_sub : ∀ t : T, candV t ⊆ support t)
    (h_cand : ∀ t : T, (candV t).card ≤ L)
    (h_bad_card : ∀ (t : T) (x : V) (ω : V → Fin (N + 1)), (badSet t x ω).card ≤ K)
    (h_bad_cyl : ∀ (t : T) (x : V) (ω1 ω2 : V → Fin (N + 1)),
      (∀ v ∈ support t, ω1 v = ω2 v) → badSet t x ω1 = badSet t x ω2)
    (h_bad_indep : ∀ (t : T) (x : V), x ∈ candV t → ∀ ω1 ω2 : V → Fin (N + 1),
      (∀ v ∉ candV t, ω1 v = ω2 v) → badSet t x ω1 = badSet t x ω2)
    (h_dep : ∀ t0 : T, (Finset.univ.filter (fun t : T => ¬ Disjoint (support t0) (support t))).card ≤ Γ)
    (h_num : ((K * L) ^ (M + 1)) * (4 * (Γ + 1)) ≤ (N + 1) ^ (M + 1)) :
    ∃ ω : V → Fin (N + 1), ∀ t : T,
      ((candV t).filter (fun x : V => ω x ∈ badSet t x ω)).card ≤ M := by
  -- Step 1: Establish initial algebraic and geometric reductions for `exists_good_assignment_of_conditional_bad_vertices_lll`
  let BadAssign : T → Finset V → Finset (V → Fin (N + 1)) := fun t Y =>
    Finset.univ.filter (fun ω : V → Fin (N + 1) => ∀ x ∈ Y, ω x ∈ badSet t x ω)
  let Bad : T → Finset (V → Fin (N + 1)) := fun t =>
    ((candV t).powersetCard (M + 1)).biUnion (fun Y => BadAssign t Y)
  have h_cyl : ∀ (t : T) (ω1 ω2 : V → Fin (N + 1)), (∀ v ∈ support t, ω1 v = ω2 v) →
      (ω1 ∈ Bad t ↔ ω2 ∈ Bad t) := by
    intro t ω1 ω2 h_eq
    simp only [Bad, BadAssign, Finset.mem_biUnion, Finset.mem_powersetCard, Finset.mem_filter, Finset.mem_univ, true_and]
    refine exists_congr (fun Y => and_congr_right (fun hY => forall_congr' (fun x => imp_congr_right (fun hx => ?_))))
    rw [h_eq x (h_sub t (hY.1 hx)), h_bad_cyl t x ω1 ω2 h_eq]
  have h_prob : ∀ t0 : T, (Bad t0).card * (4 * (Γ + 1)) ≤ (Finset.univ : Finset (V → Fin (N + 1))).card := by
    intro t0
    have h_pos : 0 < (N + 1) ^ (M + 1) := by positivity
    have h_pi_le : ∀ Y ∈ (candV t0).powersetCard (M + 1),
        (BadAssign t0 Y).card * (N + 1) ^ (M + 1) ≤ (Finset.univ : Finset (V → Fin (N + 1))).card * K ^ (M + 1) := by
      intro Y hY
      rw [Finset.mem_powersetCard] at hY
      have h_c := card_filter_forall_mem_badSet_mul_pow_le K (badSet t0) (h_bad_card t0) Y
        (fun x hx ω1 ω2 h_eq => h_bad_indep t0 x (hY.1 hx) ω1 ω2 (fun v hv => h_eq v (fun hvY => hv (hY.1 hvY))))
      rw [Fintype.card_fin, hY.2] at h_c
      exact h_c
    have h_pow_card : ((candV t0).powersetCard (M + 1)).card ≤ L ^ (M + 1) := by
      -- Step 2: Complete the main case analysis and bound assembly for `exists_good_assignment_of_conditional_bad_vertices_lll`
      rw [Finset.card_powersetCard]
      exact le_trans (Nat.choose_le_pow (candV t0).card (M + 1)) (Nat.pow_le_pow_left (h_cand t0) (M + 1))
    have h_bad_mul : (Bad t0).card * (N + 1) ^ (M + 1) ≤
        (Finset.univ : Finset (V → Fin (N + 1))).card * (K * L) ^ (M + 1) := by
      calc (Bad t0).card * (N + 1) ^ (M + 1)
        _ ≤ (∑ Y ∈ (candV t0).powersetCard (M + 1), (BadAssign t0 Y).card) * (N + 1) ^ (M + 1) :=
          Nat.mul_le_mul_right _ Finset.card_biUnion_le
        _ = ∑ Y ∈ (candV t0).powersetCard (M + 1), (BadAssign t0 Y).card * (N + 1) ^ (M + 1) :=
          Finset.sum_mul _ _ _
        _ ≤ ∑ _Y ∈ (candV t0).powersetCard (M + 1), (Finset.univ : Finset (V → Fin (N + 1))).card * K ^ (M + 1) :=
          Finset.sum_le_sum h_pi_le
        _ = ((candV t0).powersetCard (M + 1)).card * ((Finset.univ : Finset (V → Fin (N + 1))).card * K ^ (M + 1)) := by simp
        _ ≤ L ^ (M + 1) * ((Finset.univ : Finset (V → Fin (N + 1))).card * K ^ (M + 1)) :=
          Nat.mul_le_mul_right _ h_pow_card
        _ = (Finset.univ : Finset (V → Fin (N + 1))).card * (K ^ (M + 1) * L ^ (M + 1)) := by ring
        _ = (Finset.univ : Finset (V → Fin (N + 1))).card * (K * L) ^ (M + 1) := by rw [← Nat.mul_pow]
    have h_tot : ((Bad t0).card * (4 * (Γ + 1))) * (N + 1) ^ (M + 1) ≤
        (Finset.univ : Finset (V → Fin (N + 1))).card * (N + 1) ^ (M + 1) := by
      calc ((Bad t0).card * (4 * (Γ + 1))) * (N + 1) ^ (M + 1)
        _ = ((Bad t0).card * (N + 1) ^ (M + 1)) * (4 * (Γ + 1)) := mul_right_comm _ _ _
        _ ≤ ((Finset.univ : Finset (V → Fin (N + 1))).card * (K * L) ^ (M + 1)) * (4 * (Γ + 1)) :=
          Nat.mul_le_mul_right _ h_bad_mul
        _ = (Finset.univ : Finset (V → Fin (N + 1))).card * (((K * L) ^ (M + 1)) * (4 * (Γ + 1))) := mul_assoc _ _ _
        _ ≤ (Finset.univ : Finset (V → Fin (N + 1))).card * (N + 1) ^ (M + 1) :=
          Nat.mul_le_mul_left _ h_num
    exact Nat.le_of_mul_le_mul_right h_tot h_pos
  obtain ⟨ω, h_good⟩ := exists_good_assignment_of_cylinder_lll support Bad Γ h_cyl h_dep h_prob
  refine ⟨ω, ?_⟩
  intro t
  by_contra h_gt
  have h_le : M + 1 ≤ ((candV t).filter (fun x : V => ω x ∈ badSet t x ω)).card :=
    Nat.succ_le_of_lt (not_le.mp h_gt)
  obtain ⟨Y, hY_sub, hY_card⟩ := Finset.exists_subset_card_eq h_le
  have hY_pow : Y ∈ (candV t).powersetCard (M + 1) := by
    rw [Finset.mem_powersetCard]
    exact ⟨Finset.Subset.trans hY_sub (Finset.filter_subset _ _), hY_card⟩
  have h_in_bad : ω ∈ BadAssign t Y := by
    rw [Finset.mem_filter]
    exact ⟨Finset.mem_univ ω, fun x hx => (Finset.mem_filter.mp (hY_sub hx)).2⟩
  exact h_good t (Finset.mem_biUnion.mpr ⟨Y, hY_pow, h_in_bad⟩)

end WeldedHierarchy
