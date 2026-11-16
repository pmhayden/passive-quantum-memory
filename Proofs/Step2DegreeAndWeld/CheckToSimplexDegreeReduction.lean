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

import Proofs.Step1LLLDensity.Step1LLLMainSynthesis

/-!
# Check-Degree Overlap Invariants and Reduction to Bounded 2-Simplex Degree

Defines check-qubit degree invariants `HasBoundedCheckDegree` and `HasBoundedCheckDegreeOverlap`, and proves `hasBoundedSimplexDegreeD_32_of_hasBoundedCheckDegreeOverlap` reducing 2-simplex vertex degree 32 to check weights at most 8, qubit degrees at most 4, and shared-check overlap at most 2. Verifies the seed base case and duality invariance, bounds qubit `X`-degree (`card_filter_bdlStepXCheckX_mX_le`) and star-qubit `Z`-degree (`card_filter_bdlDeltaQ1_qQ_le_two`), and provides binary indicator cardinality helpers.

## References

* Part I, Section 2.1 (`subsec:css-complexes`), Definition 2.1 (`def:3d-css-complex`), Lemma 2.3 (`lem:seed-code`)
* Part I, Section 2.3 (`subsec:step2-mapping-cone`), Definition 2.5 (`def:three-layer-mapping-cone`), Proposition 2.6 (`prop:mapping-cone-invariants`)
-/

noncomputable section
open scoped Classical BigOperators
namespace WeldedHierarchy

/-! ## 1. Check Degree to 2-Simplex Degree Reduction -/

/-- Bounded check and qubit incidence degrees `(dX, dZ, dQX, dQZ)`. -/
def HasBoundedCheckDegree (B : BundledCSSCode3D) (dX dZ dQX dQZ : ℕ) : Prop :=
  (∀ x : B.M_X, (Finset.univ.filter (fun q : B.Q => B.code.checkX x q ≠ 0)).card ≤ dX) ∧
  (∀ z : B.M_Z, (Finset.univ.filter (fun q : B.Q => B.code.checkZ z q ≠ 0)).card ≤ dZ) ∧
  (∀ q : B.Q, (Finset.univ.filter (fun x : B.M_X => B.code.checkX x q ≠ 0)).card ≤ dQX) ∧
  (∀ q : B.Q, (Finset.univ.filter (fun z : B.M_Z => B.code.checkZ z q ≠ 0)).card ≤ dQZ)

/-- Swaps $(d_X, d_Z)$ and $(d_{QX}, d_{QZ})$ under CSS code duality `dualBundled`. -/
lemma dualBundled_preserves_bounded_check_degree (B : BundledCSSCode3D) {dX dZ dQX dQZ : ℕ}
    (h : HasBoundedCheckDegree B dX dZ dQX dQZ) :
    HasBoundedCheckDegree (dualBundled B) dZ dX dQZ dQX :=
  ⟨h.2.1, h.1, h.2.2.2, h.2.2.1⟩

/-- **Check Degree to 2-Simplex Degree Reduction (Part I, Section 2.1 (`subsec:css-complexes`), Definition 2.1 (`def:3d-css-complex`))**:
    If a 3D CSS code has check degrees bounded by $(d_X, d_Z, d_{QX}, d_{QZ})$ with
    $d_X d_{QZ} \le D$, $d_{QX} d_{QZ} \le D$, and $d_Z d_{QX} \le D$, then its active
    2-simplex incidence degree is bounded by $D$ (`HasBoundedSimplexDegreeD B D`). -/
lemma hasBoundedSimplexDegreeD_of_hasBoundedCheckDegree (B : BundledCSSCode3D)
    {dX dZ dQX dQZ D : ℕ}
    (h : HasBoundedCheckDegree B dX dZ dQX dQZ)
    (hX : dX * dQZ ≤ D) (hQ : dQX * dQZ ≤ D) (hZ : dZ * dQX ≤ D) :
    HasBoundedSimplexDegreeD B D := by
  refine ⟨?_, ?_, ?_⟩
  -- Step 1: Bound the number of active 2-simplices incident to any X-check x by dX * dQZ ≤ D.
  · intro x
    let T : Finset (B.Q × B.M_Z) :=
      (Finset.univ.filter (fun q : B.Q => B.code.checkX x q ≠ 0)).biUnion
        (fun q => (Finset.univ.filter (fun z : B.M_Z => B.code.checkZ z q ≠ 0)).image (fun z => (q, z)))
    have h_maps : Set.MapsTo (fun s : ActiveSimplex2 B.code => s.val.2)
        (↑(Finset.univ.filter (fun s : ActiveSimplex2 B.code => s.val.1 = x)) : Set (ActiveSimplex2 B.code))
        (↑T : Set (B.Q × B.M_Z)) := by
      intro s hs
      rw [Finset.mem_coe, Finset.mem_filter] at hs
      rw [Finset.mem_coe]
      dsimp [T]
      rw [Finset.mem_biUnion]
      refine ⟨s.val.2.1, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hs.2 ▸ s.property.1⟩, ?_⟩
      rw [Finset.mem_image]
      exact ⟨s.val.2.2, Finset.mem_filter.mpr ⟨Finset.mem_univ _, s.property.2⟩, rfl⟩
    have h_inj : Set.InjOn (fun s : ActiveSimplex2 B.code => s.val.2)
        (↑(Finset.univ.filter (fun s : ActiveSimplex2 B.code => s.val.1 = x)) : Set (ActiveSimplex2 B.code)) := by
      intro s1 hs1 s2 hs2 h_eq
      rw [Finset.mem_coe, Finset.mem_filter] at hs1 hs2
      exact Subtype.ext (Prod.ext (hs1.2.trans hs2.2.symm) h_eq)
    have h_card : (Finset.univ.filter (fun s : ActiveSimplex2 B.code => s.val.1 = x)).card ≤ T.card :=
      Finset.card_le_card_of_injOn _ h_maps h_inj
    have h_T_le : T.card ≤ dX * dQZ := by
      calc T.card
        _ ≤ ∑ q ∈ Finset.univ.filter (fun q : B.Q => B.code.checkX x q ≠ 0),
              ((Finset.univ.filter (fun z : B.M_Z => B.code.checkZ z q ≠ 0)).image (fun z => (q, z))).card :=
          Finset.card_biUnion_le
        _ ≤ ∑ _q ∈ Finset.univ.filter (fun q : B.Q => B.code.checkX x q ≠ 0), dQZ := by
          apply Finset.sum_le_sum
          intro q _
          exact Finset.card_image_le.trans (h.2.2.2 q)
        _ = (Finset.univ.filter (fun q : B.Q => B.code.checkX x q ≠ 0)).card * dQZ := by
          rw [Finset.sum_const, smul_eq_mul]
        _ ≤ dX * dQZ := Nat.mul_le_mul_right dQZ (h.1 x)
    exact h_card.trans (h_T_le.trans hX)
  -- Step 2: Bound the number of active 2-simplices incident to any qubit q by dQX * dQZ ≤ D.
  · intro q
    let T : Finset (B.M_X × B.M_Z) :=
      (Finset.univ.filter (fun x : B.M_X => B.code.checkX x q ≠ 0)) ×ˢ
      (Finset.univ.filter (fun z : B.M_Z => B.code.checkZ z q ≠ 0))
    have h_maps : Set.MapsTo (fun s : ActiveSimplex2 B.code => (s.val.1, s.val.2.2))
        (↑(Finset.univ.filter (fun s : ActiveSimplex2 B.code => s.val.2.1 = q)) : Set (ActiveSimplex2 B.code))
        (↑T : Set (B.M_X × B.M_Z)) := by
      intro s hs
      rw [Finset.mem_coe, Finset.mem_filter] at hs
      rw [Finset.mem_coe, Finset.mem_product, Finset.mem_filter, Finset.mem_filter]
      exact ⟨⟨Finset.mem_univ _, hs.2 ▸ s.property.1⟩, ⟨Finset.mem_univ _, hs.2 ▸ s.property.2⟩⟩
    have h_inj : Set.InjOn (fun s : ActiveSimplex2 B.code => (s.val.1, s.val.2.2))
        (↑(Finset.univ.filter (fun s : ActiveSimplex2 B.code => s.val.2.1 = q)) : Set (ActiveSimplex2 B.code)) := by
      intro s1 hs1 s2 hs2 h_eq
      rw [Finset.mem_coe, Finset.mem_filter] at hs1 hs2
      injection h_eq with hx hz
      exact Subtype.ext (Prod.ext hx (Prod.ext (hs1.2.trans hs2.2.symm) hz))
    have h_card : (Finset.univ.filter (fun s : ActiveSimplex2 B.code => s.val.2.1 = q)).card ≤ T.card :=
      Finset.card_le_card_of_injOn _ h_maps h_inj
    have h_T_le : T.card ≤ dQX * dQZ := by
      rw [Finset.card_product]
      exact Nat.mul_le_mul (h.2.2.1 q) (h.2.2.2 q)
    exact h_card.trans (h_T_le.trans hQ)
  -- Step 3: Bound the number of active 2-simplices incident to any Z-check z by dZ * dQX ≤ D.
  · intro z
    let T : Finset (B.Q × B.M_X) :=
      (Finset.univ.filter (fun q : B.Q => B.code.checkZ z q ≠ 0)).biUnion
        (fun q => (Finset.univ.filter (fun x : B.M_X => B.code.checkX x q ≠ 0)).image (fun x => (q, x)))
    have h_maps : Set.MapsTo (fun s : ActiveSimplex2 B.code => (s.val.2.1, s.val.1))
        (↑(Finset.univ.filter (fun s : ActiveSimplex2 B.code => s.val.2.2 = z)) : Set (ActiveSimplex2 B.code))
        (↑T : Set (B.Q × B.M_X)) := by
      intro s hs
      rw [Finset.mem_coe, Finset.mem_filter] at hs
      rw [Finset.mem_coe]
      dsimp [T]
      rw [Finset.mem_biUnion]
      refine ⟨s.val.2.1, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hs.2 ▸ s.property.2⟩, ?_⟩
      rw [Finset.mem_image]
      exact ⟨s.val.1, Finset.mem_filter.mpr ⟨Finset.mem_univ _, s.property.1⟩, rfl⟩
    have h_inj : Set.InjOn (fun s : ActiveSimplex2 B.code => (s.val.2.1, s.val.1))
        (↑(Finset.univ.filter (fun s : ActiveSimplex2 B.code => s.val.2.2 = z)) : Set (ActiveSimplex2 B.code)) := by
      intro s1 hs1 s2 hs2 h_eq
      rw [Finset.mem_coe, Finset.mem_filter] at hs1 hs2
      injection h_eq with hq hx
      exact Subtype.ext (Prod.ext hx (Prod.ext hq (hs1.2.trans hs2.2.symm)))
    have h_card : (Finset.univ.filter (fun s : ActiveSimplex2 B.code => s.val.2.2 = z)).card ≤ T.card :=
      Finset.card_le_card_of_injOn _ h_maps h_inj
    have h_T_le : T.card ≤ dZ * dQX := by
      calc T.card
        _ ≤ ∑ q ∈ Finset.univ.filter (fun q : B.Q => B.code.checkZ z q ≠ 0),
              ((Finset.univ.filter (fun x : B.M_X => B.code.checkX x q ≠ 0)).image (fun x => (q, x))).card :=
          Finset.card_biUnion_le
        _ ≤ ∑ _q ∈ Finset.univ.filter (fun q : B.Q => B.code.checkZ z q ≠ 0), dQX := by
          apply Finset.sum_le_sum
          intro q _
          exact Finset.card_image_le.trans (h.2.2.1 q)
        _ = (Finset.univ.filter (fun q : B.Q => B.code.checkZ z q ≠ 0)).card * dQX := by
          rw [Finset.sum_const, smul_eq_mul]
        _ ≤ dZ * dQX := Nat.mul_le_mul_right dQX (h.2.1 z)
    exact h_card.trans (h_T_le.trans hZ)

/-! ## 2. Cylinder Qubit X-Degree & BDLCQ2 Z-Check Weight Bounds -/

lemma card_filter_two_indicators_le_two {α : Type*} [Fintype α] [DecidableEq α] (a1 a2 : α)
    [∀ x, Decidable (x = a1)] [∀ x, Decidable (x = a2)] :
    (Finset.univ.filter (fun x : α =>
      ((if x = a1 then (1 : ZMod 2) else 0) + (if x = a2 then (1 : ZMod 2) else 0)) ≠ 0)).card ≤ 2 := by
  have h_sub : Finset.univ.filter (fun x : α =>
      ((if x = a1 then (1 : ZMod 2) else 0) + (if x = a2 then (1 : ZMod 2) else 0)) ≠ 0) ⊆ {a1, a2} := by
    intro x hx
    rw [Finset.mem_filter] at hx
    rw [Finset.mem_insert, Finset.mem_singleton]
    by_contra h_not
    push_neg at h_not
    apply hx.2
    rw [if_neg h_not.1, if_neg h_not.2, add_zero]
  exact (Finset.card_le_card h_sub).trans (Finset.card_le_two)

/-- Shows that any qubit $q_X \in \mathrm{BDLCX1}(pcode, M)$ participates in at most $2$
    checks via the coboundary map `bdlDeltaX0`. -/
lemma card_filter_bdlDeltaX0_mX_le_two {Q M_Z M_X : Type}
    [Fintype Q] [DecidableEq Q] [Fintype M_Z] [DecidableEq M_Z] [Fintype M_X] [DecidableEq M_X]
    (pcode : CSSCode3D Q M_Z M_X) (M : ℕ) (qX : BDLCX1 pcode M) :
    (Finset.univ.filter (fun mX : BDLStepXMX pcode M => bdlDeltaX0 pcode M mX qX ≠ 0)).card ≤ 2 := by
  rcases qX with ⟨sv, b⟩ | ⟨⟨seg, b⟩ | xv⟩
  · dsimp [bdlDeltaX0]
    split_ifs with hr0
    · exact card_filter_two_indicators_le_two _ _
    · exact card_filter_two_indicators_le_two _ _
  · dsimp [bdlDeltaX0]
    exact card_filter_two_indicators_le_two _ _
  · dsimp [bdlDeltaX0]
    exact card_filter_two_indicators_le_two _ _

/-- Projects any $X$-check $m_X \in \mathrm{BDLStepXMX}(pcode, M)$ to its parent coarse $X$-check in $M_X$. -/
def stepXMXOwnerX0 {Q M_Z M_X : Type}
    [Fintype Q] [DecidableEq Q] [Fintype M_Z] [DecidableEq M_Z] [Fintype M_X] [DecidableEq M_X]
    (pcode : CSSCode3D Q M_Z M_X) (M : ℕ) : BDLStepXMX pcode M → M_X
  | Sum.inl (x, _) => x
  | Sum.inr (sv, _) => sv.val.1.val.1

/-- Shows that the number of $X$-checks coupled to $q_Q \in \mathrm{BDLCQ1}(pcode, M)$ via
    `bdlGXQ0` is at most the coarse $X$-check degree of `xq0OwnerQ pcode M qQ.1`. -/
lemma card_filter_bdlGXQ0_mX_le {Q M_Z M_X : Type}
    [Fintype Q] [DecidableEq Q] [Fintype M_Z] [DecidableEq M_Z] [Fintype M_X] [DecidableEq M_X]
    (pcode : CSSCode3D Q M_Z M_X) (M : ℕ) (qQ : BDLCQ1 pcode M) :
    (Finset.univ.filter (fun mX : BDLStepXMX pcode M => bdlGXQ0 pcode M mX qQ ≠ 0)).card ≤
      (Finset.univ.filter (fun x : M_X => pcode.checkX x (xq0OwnerQ pcode M qQ.1) ≠ 0)).card := by
  apply Finset.card_le_card_of_injOn (stepXMXOwnerX0 pcode M)
  · intro mX hmX
    rw [Finset.mem_coe, Finset.mem_filter] at hmX ⊢
    refine ⟨Finset.mem_univ _, ?_⟩
    rcases mX with ⟨x, b⟩ | ⟨sv, b⟩
    · dsimp [bdlGXQ0] at hmX
      exact False.elim (hmX.2 rfl)
    · dsimp [bdlGXQ0, stepXMXOwnerX0] at hmX ⊢
      split_ifs at hmX with h_cond
      · exact hmX.2
      · exact False.elim (hmX.2 rfl)
  · intro mX1 hmX1 mX2 hmX2 h_eq
    rw [Finset.mem_coe, Finset.mem_filter] at hmX1 hmX2
    rcases mX1 with ⟨x1, b1⟩ | ⟨sv1, b1⟩
    · dsimp [bdlGXQ0] at hmX1; exact False.elim (hmX1.2 rfl)
    · rcases mX2 with ⟨x2, b2⟩ | ⟨sv2, b2⟩
      · dsimp [bdlGXQ0] at hmX2; exact False.elim (hmX2.2 rfl)
      · dsimp [bdlGXQ0, stepXMXOwnerX0] at hmX1 hmX2 h_eq
        split_ifs at hmX1 with hc1
        · split_ifs at hmX2 with hc2
          · rcases hc1 with ⟨hr1, hv1, rfl⟩
            rcases hc2 with ⟨hr2, hv2, rfl⟩
            congr 1
            apply Prod.ext
            · exact Subtype.ext (Prod.ext (Subtype.ext (Prod.ext h_eq (hv1.trans hv2.symm))) (hr1.trans hr2.symm))
            · rfl
          · exact False.elim (hmX2.2 rfl)
        · exact False.elim (hmX1.2 rfl)

/-- Bounds the $X$-check degree of any qubit $q \in \mathrm{BDLStepXQ}(pcode, M)$ by $\max(2, d_{QX})$. -/
lemma card_filter_bdlStepXCheckX_mX_le {Q M_Z M_X : Type}
    [Fintype Q] [DecidableEq Q] [Fintype M_Z] [DecidableEq M_Z] [Fintype M_X] [DecidableEq M_X]
    (pcode : CSSCode3D Q M_Z M_X) (M : ℕ) {dQX : ℕ}
    (hdQX : ∀ q : Q, (Finset.univ.filter (fun x : M_X => pcode.checkX x q ≠ 0)).card ≤ dQX)
    (q : BDLStepXQ pcode M) :
    (Finset.univ.filter (fun mX : BDLStepXMX pcode M => bdlStepXCheckX pcode M mX q ≠ 0)).card ≤ max 2 dQX := by
  rcases q with qX | qQ
  · exact (card_filter_bdlDeltaX0_mX_le_two pcode M qX).trans (Nat.le_max_left 2 dQX)
  · exact (card_filter_bdlGXQ0_mX_le pcode M qQ).trans
      ((hdQX (xq0OwnerQ pcode M qQ.1)).trans (Nat.le_max_right 2 dQX))

/-- Congruence lemma for `Finset.card` of filtered `Finset.univ` under pointwise logical equivalence. -/
lemma card_filter_iff {α : Type*} [Fintype α] (P Q_pred : α → Prop) [DecidablePred P] [DecidablePred Q_pred]
    (h : ∀ x, P x ↔ Q_pred x) :
    (Finset.univ.filter P).card = (Finset.univ.filter Q_pred).card := by
  congr 1; ext x; simp [h x]

/-- If the sum of two $\mathbb{Z}_2$ indicator terms is non-zero, at least one of the propositions holds. -/
lemma add_ite_one_ne_zero_imp' {P Q_prop : Prop} [Decidable P] [Decidable Q_prop]
    (h : (if P then (1 : ZMod 2) else 0) + (if Q_prop then (1 : ZMod 2) else 0) ≠ 0) :
    P ∨ Q_prop := by
  by_cases hP : P
  · exact Or.inl hP
  · by_cases hQ : Q_prop
    · exact Or.inr hQ
    · rw [if_neg hP, if_neg hQ, add_zero] at h; exact False.elim (h rfl)

/-- Shows that any $Z$-check $m_{ZQ} \in \mathrm{BDLCQ2}(pcode, M)$ has support of size at
    most $2$ on `BDLCQ1` under `bdlDeltaQ1`. -/
lemma card_filter_bdlDeltaQ1_qQ_le_two {Q M_Z M_X : Type}
    [Fintype Q] [DecidableEq Q] [Fintype M_Z] [DecidableEq M_Z] [Fintype M_X] [DecidableEq M_X]
    (pcode : CSSCode3D Q M_Z M_X) (M : ℕ) (mZQ : BDLCQ2 pcode M) :
    (Finset.univ.filter (fun qQ : BDLCQ1 pcode M => bdlDeltaQ1 pcode M mZQ qQ ≠ 0)).card ≤ 2 := by
  rcases mZQ with ⟨eZ, k, bZ⟩ | ⟨eZ, v⟩
  · have h_sub : Finset.univ.filter (fun qQ : BDLCQ1 pcode M =>
        bdlDeltaQ1 pcode M (Sum.inl (eZ, k, bZ)) qQ ≠ 0) ⊆
        {(armStart pcode M eZ k, bZ), (armEnd pcode M eZ k, bZ)} := by
      intro qQ hqQ
      rw [Finset.mem_filter] at hqQ
      rw [Finset.mem_insert, Finset.mem_singleton]
      unfold bdlDeltaQ1 at hqQ
      exact add_ite_one_ne_zero_imp' hqQ.2
    exact (Finset.card_le_card h_sub).trans Finset.card_le_two
  · have h_sub : Finset.univ.filter (fun qQ : BDLCQ1 pcode M =>
        bdlDeltaQ1 pcode M (Sum.inr (eZ, v)) qQ ≠ 0) ⊆
        {(Sum.inr (Sum.inr eZ), 0), (Sum.inr (Sum.inr eZ), v.succ)} := by
      intro qQ hqQ
      rw [Finset.mem_filter] at hqQ
      rw [Finset.mem_insert, Finset.mem_singleton]
      unfold bdlDeltaQ1 at hqQ
      exact add_ite_one_ne_zero_imp' hqQ.2
    exact (Finset.card_le_card h_sub).trans Finset.card_le_two

/-! ## 3. Check-Overlap Invariant & Indicator Filter Cardinality Helpers -/

/-- Bounded check and qubit incidence degrees `(dX, dZ, dQX, dQZ) = (8, 8, 4, 4)` together with
    check-pair overlap `I_{x, z} ≤ 2` (Part I, Section 2.3 (`subsec:step2-mapping-cone`), Proposition 2.6 (`prop:mapping-cone-invariants`); Balasubramanian–Davydova–Lin (2026), Lemma 3.11). -/
def HasBoundedCheckDegreeOverlap (B : BundledCSSCode3D) : Prop :=
  HasBoundedCheckDegree B 8 8 4 4 ∧
  ∀ (x : B.M_X) (z : B.M_Z),
    (Finset.univ.filter (fun q : B.Q => B.code.checkX x q ≠ 0 ∧ B.code.checkZ z q ≠ 0)).card ≤ 2

/-- Specializes `hasBoundedSimplexDegreeD_of_hasBoundedCheckDegree` to deduce
    `HasBoundedSimplexDegreeD B 32` from `HasBoundedCheckDegreeOverlap B` ($8 \times 4 = 32$). -/
lemma hasBoundedSimplexDegreeD_32_of_hasBoundedCheckDegreeOverlap (B : BundledCSSCode3D)
    (h : HasBoundedCheckDegreeOverlap B) :
    HasBoundedSimplexDegreeD B 32 :=
  hasBoundedSimplexDegreeD_of_hasBoundedCheckDegree B h.1 (by omega) (by omega) (by omega)

/-- Verifies by finite decision that the 5-qubit surface seed code satisfies `HasBoundedCheckDegreeOverlap`. -/
lemma hasBoundedCheckDegreeOverlap_surfaceSeed :
    HasBoundedCheckDegreeOverlap bdlSurfaceSeedBundled := by
  refine ⟨⟨?_, ?_, ?_, ?_⟩, ?_⟩
  · intro x; fin_cases x <;> decide
  · intro z; fin_cases z <;> decide
  · intro q; fin_cases q <;> decide
  · intro q; fin_cases q <;> decide
  · intro x z; fin_cases x <;> fin_cases z <;> decide

/-- Proves that `HasBoundedCheckDegreeOverlap` is symmetric and preserved under `dualBundled`. -/
lemma dualBundled_preserves_bounded_check_degree_overlap (B : BundledCSSCode3D)
    (h : HasBoundedCheckDegreeOverlap B) :
    HasBoundedCheckDegreeOverlap (dualBundled B) := by
  refine ⟨dualBundled_preserves_bounded_check_degree B h.1, ?_⟩
  intro z x
  change (Finset.univ.filter (fun q : B.Q => B.code.checkZ z q ≠ 0 ∧ B.code.checkX x q ≠ 0)).card ≤ 2
  rw [card_filter_iff _ (fun q : B.Q => B.code.checkX x q ≠ 0 ∧ B.code.checkZ z q ≠ 0) (fun _ => and_comm)]
  exact h.2 x z

/-- Shows that `(Finset.univ.filter P).card = 0` whenever $P(x)$ is false for all $x$. -/
lemma card_filter_eq_zero_of_imp_false {α : Type*} [Fintype α] (P : α → Prop) [DecidablePred P]
    (h : ∀ x : α, ¬ P x) :
    (Finset.univ.filter P).card = 0 := by
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro x _
  exact h x

/-- Shows that `(Finset.univ.filter P).card ≤ 1` whenever $P$ has at most one witness. -/
lemma card_filter_le_one_of_unique {α : Type*} [Fintype α] (P : α → Prop) [DecidablePred P]
    (h : ∀ x : α, P x → ∀ y : α, P y → x = y) :
    (Finset.univ.filter P).card ≤ 1 := by
  rw [Finset.card_le_one]
  intro x hx y hy
  rw [Finset.mem_filter] at hx hy
  exact h x hx.2 y hy.2

/-- Bounds `(Finset.univ.filter P).card ≤ (Finset.univ.filter Q_pred).card` when $f$ maps
    $\{x \mid P(x)\}$ injectively into $\{y \mid Q_{\mathrm{pred}}(y)\}$. -/
lemma card_filter_le_of_injOn_filter {α β : Type*} [Fintype α] [Fintype β]
    (P : α → Prop) [DecidablePred P] (Q_pred : β → Prop) [DecidablePred Q_pred]
    (f : α → β)
    (h_maps : ∀ x : α, P x → Q_pred (f x))
    (h_inj : ∀ x : α, P x → ∀ y : α, P y → f x = f y → x = y) :
    (Finset.univ.filter P).card ≤ (Finset.univ.filter Q_pred).card := by
  apply Finset.card_le_card_of_injOn f
  · intro x hx
    rw [Finset.mem_coe, Finset.mem_filter] at hx ⊢
    exact ⟨Finset.mem_univ _, h_maps x hx.2⟩
  · intro x hx y hy h_eq
    rw [Finset.mem_coe, Finset.mem_filter] at hx hy
    exact h_inj x hx.2 y hy.2 h_eq

/-- Decomposes the filtered cardinality over a sum type $\alpha \oplus \beta$ with explicit
    `DecidablePred` instances. -/
lemma card_filter_sum_eq' {α β : Type} [Fintype α] [Fintype β]
    (P : α ⊕ β → Prop) [DecidablePred P]
    [DecidablePred (fun a : α => P (Sum.inl a))]
    [DecidablePred (fun b : β => P (Sum.inr b))] :
    (Finset.univ.filter P).card =
      (Finset.univ.filter (fun a : α => P (Sum.inl a))).card +
      (Finset.univ.filter (fun b : β => P (Sum.inr b))).card := by
  classical
  convert card_filter_sum_eq P

/-- Subadditivity of filtered cardinality: if $P(x) \implies P_1(x) \lor P_2(x)$, then
    $|\{x \mid P(x)\}| \le |\{x \mid P_1(x)\}| + |\{x \mid P_2(x)\}|$. -/
lemma card_filter_le_add_of_or {α : Type*} [Fintype α] [DecidableEq α]
    (P P1 P2 : α → Prop) [DecidablePred P] [DecidablePred P1] [DecidablePred P2]
    (h : ∀ x : α, P x → P1 x ∨ P2 x) :
    (Finset.univ.filter P).card ≤
      (Finset.univ.filter P1).card + (Finset.univ.filter P2).card := by
  have h_sub : Finset.univ.filter P ⊆ Finset.univ.filter P1 ∪ Finset.univ.filter P2 := by
    intro x hx
    rw [Finset.mem_filter] at hx
    rw [Finset.mem_union, Finset.mem_filter, Finset.mem_filter]
    rcases h x hx.2 with h1 | h2
    · exact Or.inl ⟨hx.1, h1⟩
    · exact Or.inr ⟨hx.1, h2⟩
  exact (Finset.card_le_card h_sub).trans (Finset.card_union_le _ _)

/-- In $\mathbb{Z}_2$, if $a + b \ne 0$, then $a \ne 0$ or $b \ne 0$. -/
lemma add_ne_zero_imp {a b : ZMod 2} (h : a + b ≠ 0) : a ≠ 0 ∨ b ≠ 0 := by
  by_contra h_not
  push_neg at h_not
  rw [h_not.1, h_not.2, add_zero] at h
  exact h rfl

/-- If `(if P then (1 : ZMod 2) else 0) ≠ 0`, then $P$ holds. -/
lemma ite_one_ne_zero_imp {P : Prop} [Decidable P]
    (h : (if P then (1 : ZMod 2) else 0) ≠ 0) : P := by
  by_contra h_not
  exact h (if_neg h_not)

/-- If the sum of two $\mathbb{Z}_2$ indicator expressions is non-zero, at least one condition holds. -/
lemma add_ite_one_ne_zero_imp {P1 P2 : Prop} [Decidable P1] [Decidable P2]
    (h : ((if P1 then (1 : ZMod 2) else 0) + (if P2 then (1 : ZMod 2) else 0)) ≠ 0) :
    P1 ∨ P2 := by
  by_contra h_not
  push_neg at h_not
  rw [if_neg h_not.1, if_neg h_not.2, add_zero] at h
  exact h rfl

/-- Shows that the support of a sum of three $\mathbb{Z}_2$ point indicators has cardinality at most $3$. -/
lemma card_filter_three_indicators_le_three {α : Type*} [Fintype α] [DecidableEq α] (a1 a2 a3 : α)
    {d1 : ∀ x, Decidable (x = a1)} {d2 : ∀ x, Decidable (x = a2)} {d3 : ∀ x, Decidable (x = a3)}
    {dp : DecidablePred (fun x : α =>
      ((@ite (ZMod 2) (x = a1) (d1 x) 1 0 +
        @ite (ZMod 2) (x = a2) (d2 x) 1 0 +
        @ite (ZMod 2) (x = a3) (d3 x) 1 0) ≠ 0))} :
    (@Finset.filter α (fun x : α =>
      ((@ite (ZMod 2) (x = a1) (d1 x) 1 0 +
        @ite (ZMod 2) (x = a2) (d2 x) 1 0 +
        @ite (ZMod 2) (x = a3) (d3 x) 1 0) ≠ 0)) dp Finset.univ).card ≤ 3 := by
  have h_sub : @Finset.filter α (fun x : α =>
      ((@ite (ZMod 2) (x = a1) (d1 x) 1 0 +
        @ite (ZMod 2) (x = a2) (d2 x) 1 0 +
        @ite (ZMod 2) (x = a3) (d3 x) 1 0) ≠ 0)) dp Finset.univ ⊆ {a1, a2, a3} := by
    intro x hx
    rw [Finset.mem_filter] at hx
    simp only [Finset.mem_insert, Finset.mem_singleton]
    rcases add_ne_zero_imp hx.2 with h12 | h3
    · rcases add_ite_one_ne_zero_imp h12 with h1 | h2
      · exact Or.inl h1
      · exact Or.inr (Or.inl h2)
    · exact Or.inr (Or.inr (ite_one_ne_zero_imp h3))
  calc (@Finset.filter α _ dp Finset.univ).card
    _ ≤ ({a1, a2, a3} : Finset α).card := Finset.card_le_card h_sub
    _ ≤ ({a2, a3} : Finset α).card + 1 := Finset.card_insert_le a1 {a2, a3}
    _ ≤ ({a3} : Finset α).card + 1 + 1 := Nat.add_le_add_right (Finset.card_insert_le a2 {a3}) 1
    _ = 3 := by simp

/-- Shows that the support of a sum of four $\mathbb{Z}_2$ point indicators has cardinality at most $4$. -/
lemma card_filter_four_indicators_le_four {α : Type*} [Fintype α] [DecidableEq α] (a1 a2 a3 a4 : α)
    {d1 : ∀ x, Decidable (x = a1)} {d2 : ∀ x, Decidable (x = a2)}
    {d3 : ∀ x, Decidable (x = a3)} {d4 : ∀ x, Decidable (x = a4)}
    {dp : DecidablePred (fun x : α =>
      ((@ite (ZMod 2) (x = a1) (d1 x) 1 0 +
        @ite (ZMod 2) (x = a2) (d2 x) 1 0 +
        @ite (ZMod 2) (x = a3) (d3 x) 1 0 +
        @ite (ZMod 2) (x = a4) (d4 x) 1 0) ≠ 0))} :
    (@Finset.filter α (fun x : α =>
      ((@ite (ZMod 2) (x = a1) (d1 x) 1 0 +
        @ite (ZMod 2) (x = a2) (d2 x) 1 0 +
        @ite (ZMod 2) (x = a3) (d3 x) 1 0 +
        @ite (ZMod 2) (x = a4) (d4 x) 1 0) ≠ 0)) dp Finset.univ).card ≤ 4 := by
  have h_sub : @Finset.filter α (fun x : α =>
      ((@ite (ZMod 2) (x = a1) (d1 x) 1 0 +
        @ite (ZMod 2) (x = a2) (d2 x) 1 0 +
        @ite (ZMod 2) (x = a3) (d3 x) 1 0 +
        @ite (ZMod 2) (x = a4) (d4 x) 1 0) ≠ 0)) dp Finset.univ ⊆ {a1, a2, a3, a4} := by
    intro x hx
    rw [Finset.mem_filter] at hx
    simp only [Finset.mem_insert, Finset.mem_singleton]
    rcases add_ne_zero_imp hx.2 with h123 | h4
    · rcases add_ne_zero_imp h123 with h12 | h3
      · rcases add_ite_one_ne_zero_imp h12 with h1 | h2
        · exact Or.inl h1
        · exact Or.inr (Or.inl h2)
      · exact Or.inr (Or.inr (Or.inl (ite_one_ne_zero_imp h3)))
    · exact Or.inr (Or.inr (Or.inr (ite_one_ne_zero_imp h4)))
  calc (@Finset.filter α _ dp Finset.univ).card
    _ ≤ ({a1, a2, a3, a4} : Finset α).card := Finset.card_le_card h_sub
    _ ≤ ({a2, a3, a4} : Finset α).card + 1 := Finset.card_insert_le a1 {a2, a3, a4}
    _ ≤ ({a3, a4} : Finset α).card + 1 + 1 := Nat.add_le_add_right (Finset.card_insert_le a2 {a3, a4}) 1
    _ ≤ ({a4} : Finset α).card + 1 + 1 + 1 :=
      Nat.add_le_add_right (Nat.add_le_add_right (Finset.card_insert_le a3 {a4}) 1) 1
    _ = 4 := by simp

end WeldedHierarchy
