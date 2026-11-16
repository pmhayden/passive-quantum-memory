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

import Proofs.Step1LLLDensity.CandidateVertexSupportBounds

/-!
# Step-1 LLL Bad-Event Dependency Graph Degree and Numerical Threshold

Defines the combined Step-1 bad-event index type `LLLEvent`, activity predicate `LLLEventActive`, local-box vertex support `lllSupport`, candidate vertex set `lllCandV`, and single-vertex bad-choice predicate `LLLRawBad`. Bounds candidate set cardinality (`card_lllCandV_le`), single-vertex update multiplicity (`card_LLLRawBad_update_le_deg`), and dependency-graph degree (`card_lllSupport_not_disjoint_le`), and verifies the asymmetric LLL numerical inequality (`lll_numerical_condition_32_54`) for simplex degree 32.

## References

* Part I, Section 2.2 (`subsec:step1-lll`), Proposition 2.4 (`prop:step1-lll`), Equation (2) (`eq:archimedes-slab-bound`)
-/

noncomputable section
open scoped Classical BigOperators
namespace WeldedHierarchy
/-! ## 1. LLL Event Sum Type, Support, Candidate Sets, and Conditional Bad Predicate -/
/-- Index type `ActiveSimplex2 B.code` for Stage-1 LLL events. -/
abbrev S1Idx (B : BundledCSSCode3D) := ActiveSimplex2 B.code
/-- Index type of simplex pairs for Stage-2A and Stage-2B LLL events. -/
abbrev S2Idx (B : BundledCSSCode3D) := ActiveSimplex2 B.code × ActiveSimplex2 B.code
/-- Index type of simplex triples for Stage-3A, Stage-3B, and Stage-3C LLL events. -/
abbrev S3Idx (B : BundledCSSCode3D) := ActiveSimplex2 B.code × ActiveSimplex2 B.code × ActiveSimplex2 B.code
/-- Sum type indexing all 9 families of bad events in the Step-1 Lovász Local Lemma. -/
abbrev LLLEvent (B : BundledCSSCode3D) : Type :=
  (B.Q ⊕ B.M_Z ⊕ B.M_X) ⊕
  (S1Idx B ⊕ (S2Idx B ⊕ S2Idx B) ⊕ (S3Idx B ⊕ S3Idx B ⊕ S3Idx B))
/-- Anchor 3D position `p0` of an LLL event `t : LLLEvent B`. -/
def lllEventAnchorPos (B : BundledCSSCode3D) : LLLEvent B → Point3D
  | Sum.inl (Sum.inl q0) => B.code.posQ q0
  | Sum.inl (Sum.inr (Sum.inl z0)) => B.code.posZ z0
  | Sum.inl (Sum.inr (Sum.inr x0)) => B.code.posX x0
  | Sum.inr (Sum.inl s1) => B.code.posQ s1.val.2.1
  | Sum.inr (Sum.inr (Sum.inl (Sum.inl p))) => B.code.posQ p.1.val.2.1
  | Sum.inr (Sum.inr (Sum.inl (Sum.inr p))) => B.code.posQ p.1.val.2.1
  | Sum.inr (Sum.inr (Sum.inr (Sum.inl p))) => B.code.posQ p.1.val.2.1
  | Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl p)))) => B.code.posQ p.1.val.2.1
  | Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr p)))) => B.code.posQ p.1.val.2.1
/-- Activity predicate restricting multi-simplex LLL events to local-box simplex tuples. -/
def LLLEventActive (B : BundledCSSCode3D) : LLLEvent B → Prop
  | Sum.inl _ => True
  | Sum.inr (Sum.inl _) => True
  | Sum.inr (Sum.inr (Sum.inl (Sum.inl p))) => SimplexInLocalBox B p.1 p.2
  | Sum.inr (Sum.inr (Sum.inl (Sum.inr p))) => SimplexInLocalBox B p.1 p.2
  | Sum.inr (Sum.inr (Sum.inr (Sum.inl p))) => SimplexInLocalBox B p.1 p.2.1 ∧ SimplexInLocalBox B p.1 p.2.2
  | Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl p)))) => SimplexInLocalBox B p.1 p.2.1 ∧ SimplexInLocalBox B p.1 p.2.2
  | Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr p)))) => SimplexInLocalBox B p.1 p.2.1 ∧ SimplexInLocalBox B p.1 p.2.2
/-- Classical decidability instance for `lllEventActive B`. -/
instance instDecidablePredLLLEventActive (B : BundledCSSCode3D) : DecidablePred (LLLEventActive B) := by
  intro t; rcases t with ⟨q | z | x⟩ | ⟨s1 | ⟨p | p⟩ | ⟨p | p | p⟩⟩ <;> dsimp [LLLEventActive] <;> infer_instance
/-- Variable support `localBoxSupport B (lllEventAnchorPos B t)` of an LLL event `t`. -/
def lllSupport (B : BundledCSSCode3D) (t : LLLEvent B) : Finset (LLLVertex B) :=
  if LLLEventActive B t then localBoxSupport B (lllEventAnchorPos B t) else ∅
/-- Candidate vertex subset `lllCandV B t ⊆ lllSupport B t` tested by conditional bad-vertex LLL. -/
def lllCandV (B : BundledCSSCode3D) : LLLEvent B → Finset (LLLVertex B)
  | Sum.inl (Sum.inl q0) => (candQ B (B.code.posQ q0)).erase (Sum.inl q0)
  | Sum.inl (Sum.inr (Sum.inl z0)) => (candZ B (B.code.posZ z0)).erase (Sum.inr (Sum.inl z0))
  | Sum.inl (Sum.inr (Sum.inr x0)) => (candX B (B.code.posX x0)).erase (Sum.inr (Sum.inr x0))
  | Sum.inr (Sum.inl s1) => (candX B (B.code.posQ s1.val.2.1)).erase (Sum.inr (Sum.inr s1.val.1))
  | Sum.inr (Sum.inr (Sum.inl (Sum.inl p))) =>
      if SimplexInLocalBox B p.1 p.2 then
        ((candX B (B.code.posQ p.1.val.2.1)).erase (Sum.inr (Sum.inr p.1.val.1))).erase (Sum.inr (Sum.inr p.2.val.1))
      else ∅
  | Sum.inr (Sum.inr (Sum.inl (Sum.inr p))) =>
      if SimplexInLocalBox B p.1 p.2 then
        ((candQ B (B.code.posQ p.1.val.2.1)).erase (Sum.inl p.1.val.2.1)).erase (Sum.inl p.2.val.2.1)
      else ∅
  | Sum.inr (Sum.inr (Sum.inr (Sum.inl p))) =>
      if SimplexInLocalBox B p.1 p.2.1 ∧ SimplexInLocalBox B p.1 p.2.2 then
        (((candX B (B.code.posQ p.1.val.2.1)).erase (Sum.inr (Sum.inr p.1.val.1))).erase (Sum.inr (Sum.inr p.2.1.val.1))).erase (Sum.inr (Sum.inr p.2.2.val.1))
      else ∅
  | Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl p)))) =>
      if SimplexInLocalBox B p.1 p.2.1 ∧ SimplexInLocalBox B p.1 p.2.2 then
        (((candQ B (B.code.posQ p.1.val.2.1)).erase (Sum.inl p.1.val.2.1)).erase (Sum.inl p.2.1.val.2.1)).erase (Sum.inl p.2.2.val.2.1)
      else ∅
  | Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr p)))) =>
      if SimplexInLocalBox B p.1 p.2.1 ∧ SimplexInLocalBox B p.1 p.2.2 then
        (((candZ B (B.code.posQ p.1.val.2.1)).erase (Sum.inr (Sum.inl p.1.val.2.2))).erase (Sum.inr (Sum.inl p.2.1.val.2.2))).erase (Sum.inr (Sum.inl p.2.2.val.2.2))
      else ∅
/-- Conditional bad predicate `lllRawBad B t v ω` for candidate vertex `v` in event `t`. -/
def LLLRawBad (B : BundledCSSCode3D) :
    -- Step 1: Establish initial algebraic and geometric reductions for `LLLRawBad`
    LLLEvent B → LLLVertex B → (LLLVertex B → Fin (lllGridN + 1)) → Prop
  | Sum.inl (Sum.inl q0), Sum.inl q, ω =>
      q ≠ q0 ∧ distSq3D ((lllPCode B ω).posQ q0) ((lllPCode B ω).posQ q) ≤ 4
  | Sum.inl (Sum.inl _), Sum.inr _, _ => False
  | Sum.inl (Sum.inr (Sum.inl z0)), Sum.inr (Sum.inl z), ω =>
      z ≠ z0 ∧ distSq3D ((lllPCode B ω).posZ z0) ((lllPCode B ω).posZ z) ≤ 4
  | Sum.inl (Sum.inr (Sum.inl _)), Sum.inl _, _ => False
  | Sum.inl (Sum.inr (Sum.inl _)), Sum.inr (Sum.inr _), _ => False
  | Sum.inl (Sum.inr (Sum.inr x0)), Sum.inr (Sum.inr x), ω =>
      x ≠ x0 ∧ distSq3D ((lllPCode B ω).posX x0) ((lllPCode B ω).posX x) ≤ 4
  | Sum.inl (Sum.inr (Sum.inr _)), Sum.inl _, _ => False
  | Sum.inl (Sum.inr (Sum.inr _)), Sum.inr (Sum.inl _), _ => False
  | Sum.inr (Sum.inl s1), Sum.inr (Sum.inr x), ω =>
      ∃ u : ActiveSimplex2 B.code, u.val.1 = x ∧
        Stage1BadPts (lllSimplexPts B ω s1) (lllSimplexPts B ω u) (VertexDisjointSimplex2 s1.val u.val)
  | Sum.inr (Sum.inl _), _, _ => False
  | Sum.inr (Sum.inr (Sum.inl (Sum.inl p))), Sum.inr (Sum.inr x), ω =>
      ∃ u : ActiveSimplex2 B.code, u.val.1 = x ∧
        Stage2ABadPts (lllSimplexPts B ω p.1) (lllSimplexPts B ω p.2) (lllSimplexPts B ω u)
          (VertexDisjointSimplex2 p.1.val u.val ∧ VertexDisjointSimplex2 p.2.val u.val)
  -- Step 2: Complete the main case analysis and bound assembly for `LLLRawBad`
  | Sum.inr (Sum.inr (Sum.inl (Sum.inl _))), _, _ => False
  | Sum.inr (Sum.inr (Sum.inl (Sum.inr p))), Sum.inl q, ω =>
      ∃ u : ActiveSimplex2 B.code, u.val.2.1 = q ∧
        Stage2BBadPts (lllSimplexPts B ω p.1) (lllSimplexPts B ω p.2) (lllSimplexPts B ω u)
          (VertexDisjointSimplex2 p.1.val u.val ∧ VertexDisjointSimplex2 p.2.val u.val)
  | Sum.inr (Sum.inr (Sum.inl (Sum.inr _))), _, _ => False
  | Sum.inr (Sum.inr (Sum.inr (Sum.inl p))), Sum.inr (Sum.inr x), ω =>
      ∃ u : ActiveSimplex2 B.code, u.val.1 = x ∧
        Stage3ABadPts (lllSimplexPts B ω p.1) (lllSimplexPts B ω p.2.1) (lllSimplexPts B ω p.2.2) (lllSimplexPts B ω u)
          (VertexDisjointSimplex2 p.1.val u.val ∧ VertexDisjointSimplex2 p.2.1.val u.val ∧ VertexDisjointSimplex2 p.2.2.val u.val)
  | Sum.inr (Sum.inr (Sum.inr (Sum.inl _))), _, _ => False
  | Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl p)))), Sum.inl q, ω =>
      ∃ u : ActiveSimplex2 B.code, u.val.2.1 = q ∧
        Stage3BBadPts (lllSimplexPts B ω p.1) (lllSimplexPts B ω p.2.1) (lllSimplexPts B ω p.2.2) (lllSimplexPts B ω u)
          (VertexDisjointSimplex2 p.1.val u.val ∧ VertexDisjointSimplex2 p.2.1.val u.val ∧ VertexDisjointSimplex2 p.2.2.val u.val)
  | Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl _)))), _, _ => False
  | Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr p)))), Sum.inr (Sum.inl z), ω =>
      ∃ u : ActiveSimplex2 B.code, u.val.2.2 = z ∧
        Stage3CBadPts (lllSimplexPts B ω p.1) (lllSimplexPts B ω p.2.1) (lllSimplexPts B ω p.2.2) (lllSimplexPts B ω u)
          (VertexDisjointSimplex2 p.1.val u.val ∧ VertexDisjointSimplex2 p.2.1.val u.val ∧ VertexDisjointSimplex2 p.2.2.val u.val)
  | Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr _)))), _, _ => False
/-! ## 2. Candidate Set Size and Single-Vertex Conditional Bad Fiber Bound -/
/-- Classical decidability instance for `lllRawBad B t v`. -/
instance instDecidableLLLRawBad (B : BundledCSSCode3D) (t : LLLEvent B) (v : LLLVertex B)
    (ω : LLLVertex B → Fin (lllGridN + 1)) : Decidable (LLLRawBad B t v ω) := by
  rcases t with ⟨q0 | z0 | x0⟩ | ⟨s1 | ⟨p | p⟩ | ⟨p | p | p⟩⟩ <;>
    rcases v with q | ⟨z | x⟩ <;> dsimp [LLLRawBad] <;> infer_instance
/-- For every event `t`, `lllCandV B t` is a subset of `lllSupport B t`. -/
lemma lllCandV_subset_lllSupport (B : BundledCSSCode3D) (t : LLLEvent B) :
    lllCandV B t ⊆ lllSupport B t := by
  rcases t with ⟨q0 | z0 | x0⟩ | ⟨s1 | ⟨p | p⟩ | ⟨p | p | p⟩⟩ <;>
    dsimp [lllCandV, lllSupport, LLLEventActive, lllEventAnchorPos]
  · exact Finset.Subset.trans (Finset.erase_subset _ _) (candQ_subset_localBoxSupport B _)
  · exact Finset.Subset.trans (Finset.erase_subset _ _) (candZ_subset_localBoxSupport B _)
  · exact Finset.Subset.trans (Finset.erase_subset _ _) (candX_subset_localBoxSupport B _)
  · exact Finset.Subset.trans (Finset.erase_subset _ _) (candX_subset_localBoxSupport B _)
  · split_ifs
    · exact Finset.Subset.trans (Finset.erase_subset _ _) (Finset.Subset.trans (Finset.erase_subset _ _) (candX_subset_localBoxSupport B _))
    · exact Finset.Subset.refl _
  · split_ifs
    · exact Finset.Subset.trans (Finset.erase_subset _ _) (Finset.Subset.trans (Finset.erase_subset _ _) (candQ_subset_localBoxSupport B _))
    · exact Finset.Subset.refl _
  · split_ifs
    · exact Finset.Subset.trans (Finset.erase_subset _ _) (Finset.Subset.trans (Finset.erase_subset _ _) (Finset.Subset.trans (Finset.erase_subset _ _) (candX_subset_localBoxSupport B _)))
    · exact Finset.Subset.refl _
  · split_ifs
    · exact Finset.Subset.trans (Finset.erase_subset _ _) (Finset.Subset.trans (Finset.erase_subset _ _) (Finset.Subset.trans (Finset.erase_subset _ _) (candQ_subset_localBoxSupport B _)))
    · exact Finset.Subset.refl _
  · split_ifs
    · exact Finset.Subset.trans (Finset.erase_subset _ _) (Finset.Subset.trans (Finset.erase_subset _ _) (Finset.Subset.trans (Finset.erase_subset _ _) (candZ_subset_localBoxSupport B _)))
    · exact Finset.Subset.refl _
/-- Under `HasUnitBallDensityT B`, `(lllCandV B t).card ≤ 259242201 * bdlDensityTNat`. -/
lemma card_lllCandV_le (B : BundledCSSCode3D) (h_dens : HasUnitBallDensityT B) (t : LLLEvent B) :
    (lllCandV B t).card ≤ 259242201 * bdlDensityTNat := by
  rcases t with ⟨q0 | z0 | x0⟩ | ⟨s1 | ⟨p | p⟩ | ⟨p | p | p⟩⟩ <;>
    dsimp [lllCandV]
  · exact le_trans (Finset.card_erase_le) (card_candQ_le B h_dens _)
  · exact le_trans (Finset.card_erase_le) (card_candZ_le B h_dens _)
  · exact le_trans (Finset.card_erase_le) (card_candX_le B h_dens _)
  · exact le_trans (Finset.card_erase_le) (card_candX_le B h_dens _)
  · split_ifs
    · exact le_trans Finset.card_erase_le (le_trans Finset.card_erase_le (card_candX_le B h_dens _))
    · simp
  · split_ifs
    · exact le_trans Finset.card_erase_le (le_trans Finset.card_erase_le (card_candQ_le B h_dens _))
    · simp
  · split_ifs
    · exact le_trans Finset.card_erase_le (le_trans Finset.card_erase_le (le_trans Finset.card_erase_le (card_candX_le B h_dens _)))
    · simp
  · split_ifs
    · exact le_trans Finset.card_erase_le (le_trans Finset.card_erase_le (le_trans Finset.card_erase_le (card_candQ_le B h_dens _)))
    · simp
  · split_ifs
    · exact le_trans Finset.card_erase_le (le_trans Finset.card_erase_le (le_trans Finset.card_erase_le (card_candZ_le B h_dens _)))
    · simp
/-- Trivial upper bound `(univ.filter (fun _ => False)).card ≤ D`. -/
lemma card_filter_false_le {α : Type*} [Fintype α] {P : α → Prop} [DecidablePred P] {D : ℕ}
    (h_false : ∀ c, ¬ P c) : (Finset.univ.filter P).card ≤ D := by
  rw [Finset.filter_eq_empty_iff.mpr (fun c _ => h_false c)]
  simp
/-- Fiber cardinality bound `≤ D` when every bad parameter `c` is witnessed by a simplex in a family of size `≤ D`. -/
lemma card_filter_le_deg_of_exists_simplex {α U V : Type*} [Fintype α] [Fintype U] [DecidableEq U] [DecidableEq V]
    {D : ℕ} (P : α → Prop) [DecidablePred P]
    (f : U → V) (x : V)
    (h_inc : (Finset.univ.filter (fun u : U => f u = x)).card ≤ D)
    (Bad : U → α → Prop) [∀ u, DecidablePred (Bad u)]
    (h_imp : ∀ c : α, P c → ∃ u : U, f u = x ∧ Bad u c)
    (h_one : ∀ u : U, f u = x → (Finset.univ.filter (fun c : α => Bad u c)).card ≤ 1) :
    (Finset.univ.filter P).card ≤ D := by
  have h_sub : Finset.univ.filter P ⊆
      (Finset.univ.filter (fun u : U => f u = x)).biUnion (fun u => Finset.univ.filter (fun c : α => Bad u c)) := by
    intro c hc
    rw [Finset.mem_filter] at hc
    rcases h_imp c hc.2 with ⟨u, hfu, hbad⟩
    rw [Finset.mem_biUnion]
    exact ⟨u, Finset.mem_filter.mpr ⟨Finset.mem_univ u, hfu⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ c, hbad⟩⟩
  calc (Finset.univ.filter P).card
    _ ≤ ((Finset.univ.filter (fun u : U => f u = x)).biUnion (fun u => Finset.univ.filter (fun c : α => Bad u c))).card := Finset.card_le_card h_sub
    _ ≤ ∑ u ∈ Finset.univ.filter (fun u : U => f u = x), (Finset.univ.filter (fun c : α => Bad u c)).card := Finset.card_biUnion_le
    _ ≤ ∑ _u ∈ Finset.univ.filter (fun u : U => f u = x), 1 := by
        apply Finset.sum_le_sum
        intro u hu
        exact h_one u (Finset.mem_filter.mp hu).2
    _ = (Finset.univ.filter (fun u : U => f u = x)).card := by simp
    _ ≤ D := h_inc
/-- Varying a single candidate vertex `v` triggers `lllRawBad B t v` for at most `D` grid indices. -/
lemma card_LLLRawBad_update_le_deg (B : BundledCSSCode3D) {D : ℕ} (hD1 : 1 ≤ D)
    (h_deg : HasBoundedSimplexDegreeD B D)
    (t : LLLEvent B) (v : LLLVertex B) (ω0 : LLLVertex B → Fin (lllGridN + 1)) :
    (Finset.univ.filter (fun c : Fin (lllGridN + 1) => LLLRawBad B t v (Function.update ω0 v c))).card ≤ D := by
  -- Step 1: Establish initial algebraic and geometric reductions for `card_LLLRawBad_update_le_deg`
  rcases t with ⟨q0 | z0 | x0⟩ | ⟨s1 | ⟨p | p⟩ | ⟨p | p | p⟩⟩ <;>
    rcases v with q | ⟨z | x⟩ <;> try exact card_filter_false_le (fun _ h => h)
  · by_cases hne : q = q0
    · exact card_filter_false_le (fun _ h => h.1 hne)
    · have h_sub : Finset.univ.filter (fun c : Fin (lllGridN + 1) =>
          LLLRawBad B (Sum.inl (Sum.inl q0)) (Sum.inl q) (Function.update ω0 (Sum.inl q) c)) ⊆
          Finset.univ.filter (fun c : Fin (lllGridN + 1) =>
            distSq3D ((lllPCode B ω0).posQ q0)
              (fun a => (bdlLambda : ℝ) * B.code.posQ q a + rationalCap0 (lllGridParam c) a) ≤ 4) := by
        intro c hc
        rw [Finset.mem_filter] at hc ⊢
        refine ⟨hc.1, ?_⟩
        have hq0 : (lllPCode B (Function.update ω0 (Sum.inl q) c)).posQ q0 = (lllPCode B ω0).posQ q0 := by
          dsimp [lllPCode, bdlPerturbStep, lllTQ]
          rw [Function.update_of_ne (fun h => hne (Sum.inl.inj h.symm))]
        have hq_c : (lllPCode B (Function.update ω0 (Sum.inl q) c)).posQ q =
            fun a => (bdlLambda : ℝ) * B.code.posQ q a + rationalCap0 (lllGridParam c) a := by
          dsimp [lllPCode, bdlPerturbStep, lllTQ]
          rw [Function.update_self]
        rw [← hq0, ← hq_c]; exact hc.2.2
      exact le_trans (Finset.card_le_card h_sub)
        (le_trans (card_filter_lllGridParam_distSq_le_four_le_one _ _ rationalCap0 2 (fun _ => rfl)) hD1)
  · by_cases hne : z = z0
    · exact card_filter_false_le (fun _ h => h.1 hne)
    · have h_sub : Finset.univ.filter (fun c : Fin (lllGridN + 1) =>
          LLLRawBad B (Sum.inl (Sum.inr (Sum.inl z0))) (Sum.inr (Sum.inl z)) (Function.update ω0 (Sum.inr (Sum.inl z)) c)) ⊆
          Finset.univ.filter (fun c : Fin (lllGridN + 1) =>
            distSq3D ((lllPCode B ω0).posZ z0)
              (fun a => (bdlLambda : ℝ) * B.code.posZ z a + rationalCap1 (lllGridParam c) a) ≤ 4) := by
        intro c hc
        rw [Finset.mem_filter] at hc ⊢
        refine ⟨hc.1, ?_⟩
        have hz0 : (lllPCode B (Function.update ω0 (Sum.inr (Sum.inl z)) c)).posZ z0 = (lllPCode B ω0).posZ z0 := by
          dsimp [lllPCode, bdlPerturbStep, lllTZ]
          rw [Function.update_of_ne (fun h => hne (Sum.inl.inj (Sum.inr.inj h.symm)))]
        -- Step 2: Complete the main case analysis and bound assembly for `card_LLLRawBad_update_le_deg`
        have hz_c : (lllPCode B (Function.update ω0 (Sum.inr (Sum.inl z)) c)).posZ z =
            fun a => (bdlLambda : ℝ) * B.code.posZ z a + rationalCap1 (lllGridParam c) a := by
          dsimp [lllPCode, bdlPerturbStep, lllTZ]
          rw [Function.update_self]
        rw [← hz0, ← hz_c]; exact hc.2.2
      exact le_trans (Finset.card_le_card h_sub)
        (le_trans (card_filter_lllGridParam_distSq_le_four_le_one _ _ rationalCap1 0 (fun _ => rfl)) hD1)
  · by_cases hne : x = x0
    · exact card_filter_false_le (fun _ h => h.1 hne)
    · have h_sub : Finset.univ.filter (fun c : Fin (lllGridN + 1) =>
          LLLRawBad B (Sum.inl (Sum.inr (Sum.inr x0))) (Sum.inr (Sum.inr x)) (Function.update ω0 (Sum.inr (Sum.inr x)) c)) ⊆
          Finset.univ.filter (fun c : Fin (lllGridN + 1) =>
            distSq3D ((lllPCode B ω0).posX x0)
              (fun a => (bdlLambda : ℝ) * B.code.posX x a + rationalCap2 (lllGridParam c) a) ≤ 4) := by
        intro c hc
        rw [Finset.mem_filter] at hc ⊢
        refine ⟨hc.1, ?_⟩
        have hx0 : (lllPCode B (Function.update ω0 (Sum.inr (Sum.inr x)) c)).posX x0 = (lllPCode B ω0).posX x0 := by
          dsimp [lllPCode, bdlPerturbStep, lllTX]
          rw [Function.update_of_ne (fun h => hne (Sum.inr.inj (Sum.inr.inj h.symm)))]
        have hx_c : (lllPCode B (Function.update ω0 (Sum.inr (Sum.inr x)) c)).posX x =
            fun a => (bdlLambda : ℝ) * B.code.posX x a + rationalCap2 (lllGridParam c) a := by
          dsimp [lllPCode, bdlPerturbStep, lllTX]
          rw [Function.update_self]
        rw [← hx0, ← hx_c]; exact hc.2.2
      exact le_trans (Finset.card_le_card h_sub)
        (le_trans (card_filter_lllGridParam_distSq_le_four_le_one _ _ rationalCap2 1 (fun _ => rfl)) hD1)
  · exact card_filter_le_deg_of_exists_simplex _ (fun u : ActiveSimplex2 B.code => u.val.1) x (h_deg.1 x) _
      (fun _ h => h) (fun u hu => by subst hu; exact card_update_stage1BadPts_le_one B ω0 s1 u)
  · exact card_filter_le_deg_of_exists_simplex _ (fun u : ActiveSimplex2 B.code => u.val.1) x (h_deg.1 x) _
      (fun _ h => h) (fun u hu => by subst hu; exact card_update_stage2ABadPts_le_one B ω0 p.1 p.2 u)
  · exact card_filter_le_deg_of_exists_simplex _ (fun u : ActiveSimplex2 B.code => u.val.2.1) q (h_deg.2.1 q) _
      (fun _ h => h) (fun u hu => by subst hu; exact card_update_stage2BBadPts_le_one B ω0 p.1 p.2 u)
  · exact card_filter_le_deg_of_exists_simplex _ (fun u : ActiveSimplex2 B.code => u.val.1) x (h_deg.1 x) _
      (fun _ h => h) (fun u hu => by subst hu; exact card_update_stage3ABadPts_le_one B ω0 p.1 p.2.1 p.2.2 u)
  · exact card_filter_le_deg_of_exists_simplex _ (fun u : ActiveSimplex2 B.code => u.val.2.1) q (h_deg.2.1 q) _
      (fun _ h => h) (fun u hu => by subst hu; exact card_update_stage3BBadPts_le_one B ω0 p.1 p.2.1 p.2.2 u)
  · exact card_filter_le_deg_of_exists_simplex _ (fun u : ActiveSimplex2 B.code => u.val.2.2) z (h_deg.2.2 z) _
      (fun _ h => h) (fun u hu => by subst hu; exact card_update_stage3CBadPts_le_one B ω0 p.1 p.2.1 p.2.2 u)
/-! ## 3. Event Dependency Graph Degree Bound and Numerical LLL Threshold -/
/-- Cardinality of a filtered sum type `α ⊕ β` decomposes as the sum of filtered branch cardinalities. -/
lemma card_filter_sum_le {α β : Type*} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
    {C1 C2 : ℕ} (R : α ⊕ β → Prop) [DecidablePred R]
    (h1 : (Finset.univ.filter (fun a : α => R (Sum.inl a))).card ≤ C1)
    (h2 : (Finset.univ.filter (fun b : β => R (Sum.inr b))).card ≤ C2) :
    (Finset.univ.filter R).card ≤ C1 + C2 := by
  have h_sub : Finset.univ.filter R ⊆
      (Finset.univ.filter (fun a : α => R (Sum.inl a))).image Sum.inl ∪
      (Finset.univ.filter (fun b : β => R (Sum.inr b))).image Sum.inr := by
    intro x hx
    rw [Finset.mem_filter] at hx
    rcases x with a | b
    · exact Finset.mem_union_left _ (Finset.mem_image.mpr ⟨a, Finset.mem_filter.mpr ⟨Finset.mem_univ a, hx.2⟩, rfl⟩)
    · exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨b, Finset.mem_filter.mpr ⟨Finset.mem_univ b, hx.2⟩, rfl⟩)
  calc (Finset.univ.filter R).card
    _ ≤ ((Finset.univ.filter (fun a : α => R (Sum.inl a))).image Sum.inl ∪
         (Finset.univ.filter (fun b : β => R (Sum.inr b))).image Sum.inr).card :=
      Finset.card_le_card h_sub
    _ ≤ ((Finset.univ.filter (fun a : α => R (Sum.inl a))).image Sum.inl).card +
        ((Finset.univ.filter (fun b : β => R (Sum.inr b))).image Sum.inr).card :=
      Finset.card_union_le _ _
    _ ≤ (Finset.univ.filter (fun a : α => R (Sum.inl a))).card +
        (Finset.univ.filter (fun b : β => R (Sum.inr b))).card :=
      Nat.add_le_add Finset.card_image_le Finset.card_image_le
    _ ≤ C1 + C2 := Nat.add_le_add h1 h2
/-- Fiberwise product bound on `(univ.filter P).card` over `α × β`. -/
lemma card_filter_prod_le {α β : Type*} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
    {C1 C2 : ℕ} (P : α → Prop) [DecidablePred P] (Q : α → β → Prop) [∀ a, DecidablePred (Q a)]
    (h1 : (Finset.univ.filter P).card ≤ C1)
    (h2 : ∀ a, P a → (Finset.univ.filter (Q a)).card ≤ C2) :
    (Finset.univ.filter (fun p : α × β => P p.1 ∧ Q p.1 p.2)).card ≤ C1 * C2 := by
  have h_sub : Finset.univ.filter (fun p : α × β => P p.1 ∧ Q p.1 p.2) ⊆
      (Finset.univ.filter P).biUnion (fun a => (Finset.univ.filter (Q a)).image (fun b => (a, b))) := by
    intro ⟨a, b⟩ hp
    rw [Finset.mem_filter] at hp
    exact Finset.mem_biUnion.mpr ⟨a, Finset.mem_filter.mpr ⟨Finset.mem_univ a, hp.2.1⟩,
      Finset.mem_image.mpr ⟨b, Finset.mem_filter.mpr ⟨Finset.mem_univ b, hp.2.2⟩, rfl⟩⟩
  calc (Finset.univ.filter (fun p : α × β => P p.1 ∧ Q p.1 p.2)).card
    _ ≤ ((Finset.univ.filter P).biUnion (fun a => (Finset.univ.filter (Q a)).image (fun b => (a, b)))).card :=
      Finset.card_le_card h_sub
    _ ≤ ∑ a ∈ Finset.univ.filter P, ((Finset.univ.filter (Q a)).image (fun b => (a, b))).card :=
      Finset.card_biUnion_le
    _ ≤ ∑ _a ∈ Finset.univ.filter P, C2 := by
      apply Finset.sum_le_sum
      intro a ha
      exact le_trans Finset.card_image_le (h2 a (Finset.mem_filter.mp ha).2)
    _ = (Finset.univ.filter P).card * C2 := by simp
    _ ≤ C1 * C2 := Nat.mul_le_mul_right C2 h1
/-- Dependency degree bound: at most `2073937608 * bdlDensityTNat * (3 + D + 2 * D^2 * M + 3 * D^3 * M^2)` events overlap `t0`. -/
lemma card_lllSupport_not_disjoint_le (B : BundledCSSCode3D) {D : ℕ}
    (h_deg : HasBoundedSimplexDegreeD B D) (h_dens : HasUnitBallDensityT B)
    (t0 : LLLEvent B) :
    let L_vert := 259242201 * bdlDensityTNat
    let L_simp := D * L_vert
    (Finset.univ.filter (fun t : LLLEvent B => ¬ Disjoint (lllSupport B t0) (lllSupport B t))).card ≤
      8 * (3 * L_vert + L_simp + 2 * L_simp ^ 2 + 3 * L_simp ^ 3) := by
  -- Step 1: Establish initial algebraic and geometric reductions for `card_lllSupport_not_disjoint_le`
  intro L_vert L_simp
  let p0 := lllEventAnchorPos B t0
  have h_sub : Finset.univ.filter (fun t : LLLEvent B => ¬ Disjoint (lllSupport B t0) (lllSupport B t)) ⊆
      Finset.univ.filter (fun t : LLLEvent B => InLocalBoxDouble p0 (lllEventAnchorPos B t) ∧ LLLEventActive B t) := by
    intro t ht
    rw [Finset.mem_filter] at ht ⊢
    obtain ⟨v, hv0, hvt⟩ := Finset.not_disjoint_iff.mp ht.2
    dsimp [lllSupport] at hv0 hvt
    split_ifs at hv0 with ha0
    · split_ifs at hvt with hat
      · rw [localBoxSupport, Finset.mem_filter] at hv0 hvt
        exact ⟨Finset.mem_univ t, inLocalBoxDouble_of_inLocalBox_both p0 (lllEventAnchorPos B t) (lllVertexPos B v) hv0.2 hvt.2, hat⟩
      · simp at hvt
    · simp at hv0
  have h_q : (Finset.univ.filter (fun q : B.Q => InLocalBoxDouble p0 (B.code.posQ q) ∧ True)).card ≤ 8 * L_vert := by
    simpa using card_pos_in_local_box_double_le bdlDensityTNat B.code.posQ (fun x0 => (h_dens x0).1) p0
  have h_z : (Finset.univ.filter (fun z : B.M_Z => InLocalBoxDouble p0 (B.code.posZ z) ∧ True)).card ≤ 8 * L_vert := by
    simpa using card_pos_in_local_box_double_le bdlDensityTNat B.code.posZ (fun x0 => (h_dens x0).2.1) p0
  have h_x : (Finset.univ.filter (fun x : B.M_X => InLocalBoxDouble p0 (B.code.posX x) ∧ True)).card ≤ 8 * L_vert := by
    simpa using card_pos_in_local_box_double_le bdlDensityTNat B.code.posX (fun x0 => (h_dens x0).2.2) p0
  have h_s1_base : (Finset.univ.filter (fun s1 : ActiveSimplex2 B.code => InLocalBoxDouble p0 (B.code.posQ s1.val.2.1))).card ≤ 8 * L_simp := by
    have h1 := card_activeSimplex_posQ_filter_le B h_deg (InLocalBoxDouble p0)
      (card_pos_in_local_box_double_le bdlDensityTNat B.code.posQ (fun x0 => (h_dens x0).1) p0)
    dsimp [L_simp, L_vert]; linarith
  -- Step 2: Complete the main case analysis and bound assembly for `card_lllSupport_not_disjoint_le`
  have h_s1 : (Finset.univ.filter (fun s1 : S1Idx B => InLocalBoxDouble p0 (B.code.posQ s1.val.2.1) ∧ True)).card ≤ 8 * L_simp := by
    simpa using h_s1_base
  have h_loc_s : ∀ s1 : ActiveSimplex2 B.code,
      (Finset.univ.filter (fun s2 : ActiveSimplex2 B.code => SimplexInLocalBox B s1 s2)).card ≤ L_simp := by
    intro s1
    have h_sub_loc : Finset.univ.filter (fun s2 : ActiveSimplex2 B.code => SimplexInLocalBox B s1 s2) ⊆
        Finset.univ.filter (fun s2 : ActiveSimplex2 B.code => InLocalBox (B.code.posQ s1.val.2.1) (B.code.posQ s2.val.2.1)) := by
      intro s2 hs2; rw [Finset.mem_filter] at hs2 ⊢; exact ⟨hs2.1, hs2.2.2.1⟩
    exact le_trans (Finset.card_le_card h_sub_loc)
      (card_activeSimplex_posQ_filter_le B h_deg _
        (card_pos_in_local_box_le bdlDensityTNat B.code.posQ (fun x0 => (h_dens x0).1) (B.code.posQ s1.val.2.1)))
  have h_s2 : (Finset.univ.filter (fun p : S2Idx B => InLocalBoxDouble p0 (B.code.posQ p.1.val.2.1) ∧ SimplexInLocalBox B p.1 p.2)).card ≤
      (8 * L_simp) * L_simp :=
    card_filter_prod_le _ _ h_s1_base (fun s1 _ => h_loc_s s1)
  have h_s3 : (Finset.univ.filter (fun p : S3Idx B =>
      InLocalBoxDouble p0 (B.code.posQ p.1.val.2.1) ∧ (SimplexInLocalBox B p.1 p.2.1 ∧ SimplexInLocalBox B p.1 p.2.2))).card ≤
      (8 * L_simp) * (L_simp * L_simp) :=
    card_filter_prod_le _ _ h_s1_base (fun s1 _ =>
      card_filter_prod_le _ _ (h_loc_s s1) (fun _ _ => h_loc_s s1))
  have h_tot := card_filter_sum_le
    (fun t : LLLEvent B => InLocalBoxDouble p0 (lllEventAnchorPos B t) ∧ LLLEventActive B t)
    (card_filter_sum_le _ h_q (card_filter_sum_le _ h_z h_x))
    (card_filter_sum_le _ h_s1
      (card_filter_sum_le _ (card_filter_sum_le _ h_s2 h_s2)
        (card_filter_sum_le _ h_s3 (card_filter_sum_le _ h_s3 h_s3))))
  calc (Finset.univ.filter (fun t : LLLEvent B => ¬ Disjoint (lllSupport B t0) (lllSupport B t))).card
    _ ≤ (Finset.univ.filter (fun t : LLLEvent B => InLocalBoxDouble p0 (lllEventAnchorPos B t) ∧ LLLEventActive B t)).card :=
      Finset.card_le_card h_sub
    _ ≤ (8 * L_vert + (8 * L_vert + 8 * L_vert)) +
        (8 * L_simp + (((8 * L_simp) * L_simp + (8 * L_simp) * L_simp) +
         ((8 * L_simp) * (L_simp * L_simp) + ((8 * L_simp) * (L_simp * L_simp) + (8 * L_simp) * (L_simp * L_simp))))) := h_tot
    _ = 8 * (3 * L_vert + L_simp + 2 * L_simp ^ 2 + 3 * L_simp ^ 3) := by ring
/-- At most `D` active 2-simplices share a given X-check vertex `v`. -/
lemma card_activeSimplex_map_X_le_deg (B : BundledCSSCode3D) {D : ℕ}
    (h_deg : HasBoundedSimplexDegreeD B D) (v : LLLVertex B) :
    (Finset.univ.filter (fun u : ActiveSimplex2 B.code => (Sum.inr (Sum.inr u.val.1) : LLLVertex B) = v)).card ≤ D := by
  rcases v with q | ⟨z | x⟩
  · simp
  · simp
  · have h_eq : Finset.univ.filter (fun u : ActiveSimplex2 B.code => (Sum.inr (Sum.inr u.val.1) : LLLVertex B) = Sum.inr (Sum.inr x)) =
        Finset.univ.filter (fun u : ActiveSimplex2 B.code => u.val.1 = x) := by
      ext u; simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨fun h => Sum.inr.inj (Sum.inr.inj h), fun h => by rw [h]⟩
    rw [h_eq]; exact h_deg.1 x
/-- At most `D` active 2-simplices share a given qubit vertex `v`. -/
lemma card_activeSimplex_map_Q_le_deg (B : BundledCSSCode3D) {D : ℕ}
    (h_deg : HasBoundedSimplexDegreeD B D) (v : LLLVertex B) :
    (Finset.univ.filter (fun u : ActiveSimplex2 B.code => (Sum.inl u.val.2.1 : LLLVertex B) = v)).card ≤ D := by
  rcases v with q | ⟨z | x⟩
  · have h_eq : Finset.univ.filter (fun u : ActiveSimplex2 B.code => (Sum.inl u.val.2.1 : LLLVertex B) = Sum.inl q) =
        Finset.univ.filter (fun u : ActiveSimplex2 B.code => u.val.2.1 = q) := by
      ext u; simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨fun h => Sum.inl.inj h, fun h => by rw [h]⟩
    rw [h_eq]; exact h_deg.2.1 q
  · simp
  · simp
/-- At most `D` active 2-simplices share a given Z-check vertex `v`. -/
lemma card_activeSimplex_map_Z_le_deg (B : BundledCSSCode3D) {D : ℕ}
    (h_deg : HasBoundedSimplexDegreeD B D) (v : LLLVertex B) :
    (Finset.univ.filter (fun u : ActiveSimplex2 B.code => (Sum.inr (Sum.inl u.val.2.2) : LLLVertex B) = v)).card ≤ D := by
  rcases v with q | ⟨z | x⟩
  · simp
  · have h_eq : Finset.univ.filter (fun u : ActiveSimplex2 B.code => (Sum.inr (Sum.inl u.val.2.2) : LLLVertex B) = Sum.inr (Sum.inl z)) =
        Finset.univ.filter (fun u : ActiveSimplex2 B.code => u.val.2.2 = z) := by
      ext u; simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨fun h => Sum.inl.inj (Sum.inr.inj h), fun h => by rw [h]⟩
    rw [h_eq]; exact h_deg.2.2 z
  · simp
/-- All three vertices of a simplex `s` with `SimplexInLocalBox B s1 s` lie in `localBoxSupport B (posQ s1)`. -/
lemma lllSimplexPts_mem_localBoxSupport (B : BundledCSSCode3D) (s1 s : ActiveSimplex2 B.code)
    (hs : SimplexInLocalBox B s1 s) :
    (Sum.inr (Sum.inr s.val.1) : LLLVertex B) ∈ localBoxSupport B (B.code.posQ s1.val.2.1) ∧
    (Sum.inl s.val.2.1 : LLLVertex B) ∈ localBoxSupport B (B.code.posQ s1.val.2.1) ∧
    (Sum.inr (Sum.inl s.val.2.2) : LLLVertex B) ∈ localBoxSupport B (B.code.posQ s1.val.2.1) :=
  ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, hs.1⟩,
   Finset.mem_filter.mpr ⟨Finset.mem_univ _, hs.2.1⟩,
   Finset.mem_filter.mpr ⟨Finset.mem_univ _, hs.2.2⟩⟩
/-- Verification of the numerical LLL threshold inequality for `D = 32` and `K = 54`. -/
lemma lll_numerical_condition_32_54 :
    let K := 32
    let L := 259242201 * bdlDensityTNat
    let L_simp := 32 * L
    let Γ := 8 * (3 * L + L_simp + 2 * L_simp ^ 2 + 3 * L_simp ^ 3)
    ((K * L) ^ (54 + 1)) * (4 * (Γ + 1)) ≤ (lllGridN + 1) ^ (54 + 1) := by
  dsimp [bdlDensityTNat, lllGridN]
  norm_num
/-- Coordinate bounds on `ptsNormal (lllSimplexPts B ω s)` under `HasInteractionRange8 B`. -/
lemma perturbed_simplex_normal_bounds (B : BundledCSSCode3D) (h8 : HasInteractionRange8 B)
    (tQ : B.Q → ℝ) (tZ : B.M_Z → ℝ) (tX : B.M_X → ℝ) (s : ActiveSimplex2 B.code)
    (htQ : 0 ≤ tQ s.val.2.1 ∧ tQ s.val.2.1 ≤ 1 / 1000)
    (htZ : 0 ≤ tZ s.val.2.2 ∧ tZ s.val.2.2 ≤ 1 / 1000)
    (htX : 0 ≤ tX s.val.1 ∧ tX s.val.1 ≤ 1 / 1000) :
    let pcode := bdlPerturbStep B.code bdlLambda
      (fun q => rationalCap0 (tQ q)) (fun z => rationalCap1 (tZ z)) (fun x => rationalCap2 (tX x))
    let N := cross3D (sub3D (pcode.posQ s.val.2.1) (pcode.posX s.val.1))
                     (sub3D (pcode.posZ s.val.2.2) (pcode.posX s.val.1))
    (900000 * (bdlLambda : ℝ) ^ 2 ≤ N 0 ∧ N 0 ≤ 987000 * (bdlLambda : ℝ) ^ 2) ∧
    (900000 * (bdlLambda : ℝ) ^ 2 ≤ N 1 ∧ N 1 ≤ 987000 * (bdlLambda : ℝ) ^ 2) ∧
    (900000 * (bdlLambda : ℝ) ^ 2 ≤ N 2 ∧ N 2 ≤ 987000 * (bdlLambda : ℝ) ^ 2) := by
  obtain ⟨hCB2, hCB0, hCB1, hBA0, hBA1, hBA2⟩ :=
    perturbed_simplex_edge_bounds B h8 tQ tZ tX s htQ htZ htX
  obtain ⟨hN0_lo, hN1_lo, hN2_lo⟩ :=
    perturbed_simplex_normal_coord_ge_900000_lambda_sq B h8 tQ tZ tX s htQ htZ htX
  let pcode := bdlPerturbStep B.code bdlLambda
    (fun q => rationalCap0 (tQ q)) (fun z => rationalCap1 (tZ z)) (fun x => rationalCap2 (tX x))
  let A := pcode.posX s.val.1
  let B_pt := pcode.posQ s.val.2.1
  let C := pcode.posZ s.val.2.2
  have hN0 : cross3D (sub3D B_pt A) (sub3D C A) 0 =
      (B_pt 1 - A 1) * (C 2 - B_pt 2) - (B_pt 2 - A 2) * (C 1 - B_pt 1) := by
    dsimp [cross3D, sub3D]; ring
  have hN1 : cross3D (sub3D B_pt A) (sub3D C A) 1 =
      (B_pt 2 - A 2) * (C 0 - B_pt 0) - (B_pt 0 - A 0) * (C 2 - B_pt 2) := by
    dsimp [cross3D, sub3D]; ring
  have hN2 : cross3D (sub3D B_pt A) (sub3D C A) 2 =
      (B_pt 0 - A 0) * (C 1 - B_pt 1) - (B_pt 1 - A 1) * (C 0 - B_pt 0) := by
    dsimp [cross3D, sub3D]; ring
  have hL : (0 : ℝ) < bdlLambda := by dsimp [bdlLambda]; norm_num
  refine ⟨⟨hN0_lo, by rw [hN0]; nlinarith⟩,
          ⟨hN1_lo, by rw [hN1]; nlinarith⟩,
          ⟨hN2_lo, by rw [hN2]; nlinarith⟩⟩
/-- Point-triple formulation of the Stage-3 dominant Cramer type trichotomy (`Stage3ABadPts ∨ Stage3BBadPts ∨ Stage3CBadPts`). -/
lemma stage3_dominant_type_trichotomy_pts (B : BundledCSSCode3D) (h8 : HasInteractionRange8 B)
    (ω : LLLVertex B → Fin (lllGridN + 1))
    (s1 s2 s3 u : ActiveSimplex2 B.code)
    (hd : VertexDisjointSimplex2 s1.val u.val ∧ VertexDisjointSimplex2 s2.val u.val ∧ VertexDisjointSimplex2 s3.val u.val)
    (hD4 : (bdlLambda : ℝ) ^ 2 < |- det3D (ptsNormal (lllSimplexPts B ω s1)) (ptsNormal (lllSimplexPts B ω s2)) (ptsNormal (lllSimplexPts B ω s3))|)
    (h_dom : FourSimplicesDominantCramerCompatible (lllPCode B ω) s1 s2 s3 u) :
    Stage3ABadPts (lllSimplexPts B ω s1) (lllSimplexPts B ω s2) (lllSimplexPts B ω s3) (lllSimplexPts B ω u)
      (VertexDisjointSimplex2 s1.val u.val ∧ VertexDisjointSimplex2 s2.val u.val ∧ VertexDisjointSimplex2 s3.val u.val) ∨
    Stage3BBadPts (lllSimplexPts B ω s1) (lllSimplexPts B ω s2) (lllSimplexPts B ω s3) (lllSimplexPts B ω u)
      (VertexDisjointSimplex2 s1.val u.val ∧ VertexDisjointSimplex2 s2.val u.val ∧ VertexDisjointSimplex2 s3.val u.val) ∨
    Stage3CBadPts (lllSimplexPts B ω s1) (lllSimplexPts B ω s2) (lllSimplexPts B ω s3) (lllSimplexPts B ω u)
      (VertexDisjointSimplex2 s1.val u.val ∧ VertexDisjointSimplex2 s2.val u.val ∧ VertexDisjointSimplex2 s3.val u.val) := by
  -- Step 1: Establish initial algebraic and geometric reductions for `stage3_dominant_type_trichotomy_pts`
  have htQ : ∀ q, 0 ≤ lllTQ B ω q ∧ lllTQ B ω q ≤ 1 / 1000 := fun q => lllGridParam_bounds (ω (Sum.inl q))
  have htZ : ∀ z, 0 ≤ lllTZ B ω z ∧ lllTZ B ω z ≤ 1 / 1000 := fun z => lllGridParam_bounds (ω (Sum.inr (Sum.inl z)))
  have htX : ∀ x, 0 ≤ lllTX B ω x ∧ lllTX B ω x ≤ 1 / 1000 := fun x => lllGridParam_bounds (ω (Sum.inr (Sum.inr x)))
  have h_trich := stage3_dominant_type_trichotomy B h8 (lllTQ B ω) (lllTZ B ω) (lllTX B ω) htQ htZ htX s1 s2 s3 u h_dom
  let pts1 := lllSimplexPts B ω s1
  let pts2 := lllSimplexPts B ω s2
  let pts3 := lllSimplexPts B ω s3
  let ptsU := lllSimplexPts B ω u
  -- Step 2: Complete the main case analysis and bound assembly for `stage3_dominant_type_trichotomy_pts`
  let N1 := ptsNormal pts1; let b1 := ptsRhs pts1
  let N2 := ptsNormal pts2; let b2 := ptsRhs pts2
  let N3 := ptsNormal pts3; let b3 := ptsRhs pts3
  let D4 := - det3D N1 N2 N3
  have hV_eq : ∀ P : Point3D,
      (fun a => b1 * cross3D N2 N3 a - b2 * cross3D N1 N3 a + b3 * cross3D N1 N2 a + D4 * P a) =
      (fun a => (dot3D pts1.1 N1 * cross3D N2 N3 a - dot3D pts2.1 N2 * cross3D N1 N3 a + dot3D pts3.1 N3 * cross3D N1 N2 a) + D4 * P a) := by
    intro P; funext a; dsimp [b1, b2, b3, ptsRhs, dot3D]; ring
  rcases h_trich with hA | hB | hC
  · left
    refine ⟨hd, ⟨hD4, ?_⟩, h_dom⟩
    rw [hV_eq ptsU.2.1]; exact hA
  · right; left
    refine ⟨hd, ⟨hD4, ?_⟩, h_dom⟩
    rw [hV_eq ptsU.2.2]; exact hB
  · right; right
    refine ⟨hd, ⟨hD4, ?_⟩, h_dom⟩
    rw [hV_eq ptsU.1]; exact hC

end WeldedHierarchy
