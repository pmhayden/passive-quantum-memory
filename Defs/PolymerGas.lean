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

import Defs.KMSAndGibbs
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Fin.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic

/-!
# Abstract Polymer Gas Partition Functions and Kotecký–Preiss Convergence Condition

Defines compatible finite polymer configurations (`IsCompatiblePolymerSet`), polymer gas partition functions (`polymerPartitionZ`), pinned polymer sums (`polymerPinnedSum`), and the abstract Kotecký–Preiss cluster expansion convergence criterion (`SatisfiesKoteckyPreissCondition`), together with partition-function positivity (`polymerPartitionZ_pos`), monotonicity (`polymerPartitionZ_mono`), and the finite Cauchy–Schwarz inequality (`fintype_sum_mul_le_sqrt_mul_sqrt`).

## References

* Part II, Sections 3.4–3.5 (`subsec:cluster-primer`, `subsec:worldline-expansion`), Proposition 3.10 (`prop:tube-local-ursell-erasure`)
* Part II, Section 6.2 (`subsec:kms-gronwall`), Theorem 6.2 (`thm:kms-gronwall-bare`)
-/

noncomputable section

open scoped Classical BigOperators

/-!
## 1. Abstract Finite-Volume Polymer Gas and Kotecký–Preiss Condition
-/

/-- Compatibility of a finite polymer configuration $\mathcal{G} \subseteq \Gamma$: all distinct
    polymers $\gamma_1 \neq \gamma_2$ in $\mathcal{G}$ are pairwise compatible ($\gamma_1 \sim \gamma_2$)
    (Kotecký–Preiss (1986); Part II, Section 3.5 (`subsec:worldline-expansion`),
    Proposition 3.10 (`prop:tube-local-ursell-erasure`)). -/
def IsCompatiblePolymerSet {Polymer : Type*} (compat : Polymer → Polymer → Prop)
    (G : Finset Polymer) : Prop :=
  ∀ γ₁ ∈ G, ∀ γ₂ ∈ G, γ₁ ≠ γ₂ → compat γ₁ γ₂

/-- The empty polymer set $\emptyset$ is vacuously compatible. -/
lemma isCompatiblePolymerSet_empty {Polymer : Type*} (compat : Polymer → Polymer → Prop) :
    IsCompatiblePolymerSet compat ∅ := by
  intro γ₁ hγ₁
  exact False.elim (Finset.notMem_empty γ₁ hγ₁)

/-- Compatibility is hereditary under subset inclusion $\mathcal{G}_1 \subseteq \mathcal{G}_2$. -/
lemma IsCompatiblePolymerSet.mono {Polymer : Type*} {compat : Polymer → Polymer → Prop}
    {G₁ G₂ : Finset Polymer} (h_sub : G₁ ⊆ G₂) (hG₂ : IsCompatiblePolymerSet compat G₂) :
    IsCompatiblePolymerSet compat G₁ := by
  intro γ₁ h₁ γ₂ h₂ hne
  exact hG₂ γ₁ (h_sub h₁) γ₂ (h_sub h₂) hne

/-- Finite polymer gas partition function
    $$Z_{\mathrm{poly}}(\Lambda) := \sum_{\substack{\mathcal{G} \subseteq \Lambda \\ \mathcal{G}\text{ compatible}}} \prod_{\gamma \in \mathcal{G}} w(\gamma)$$
    over a finite polymer pool $\Lambda \subseteq \Gamma$ (Kotecký–Preiss (1986);
    Part II, Proposition 3.10 (`prop:tube-local-ursell-erasure`), Equation (63) (`eq:ursell-partition-sigma`)). -/
def polymerPartitionZ {Polymer : Type*} [DecidableEq Polymer]
    (compat : Polymer → Polymer → Prop) (w : Polymer → ℝ) (Λ : Finset Polymer) : ℝ :=
  ∑ G ∈ Λ.powerset.filter (IsCompatiblePolymerSet compat), ∏ γ ∈ G, w γ

/-- Pinned polymer configuration sum
    $$Z_{\mathrm{pin}}(\Lambda; \mathcal{G}_{\mathrm{pin}}) := \sum_{\substack{\mathcal{G} \subseteq \Lambda\text{ compatible} \\ \mathcal{G}_{\mathrm{pin}} \subseteq \mathcal{G}}} \prod_{\gamma \in \mathcal{G}} w(\gamma)$$
    containing a pinned polymer set $\mathcal{G}_{\mathrm{pin}} \subseteq \Lambda$
    (Kotecký–Preiss (1986); Part II, Section 5.1 (`subsec:direct-worldline-synthesis`),
    Theorem 5.1 (`thm:direct-worldline-intact-cluster-erasure`)). -/
def polymerPinnedSum {Polymer : Type*} [DecidableEq Polymer]
    (compat : Polymer → Polymer → Prop) (w : Polymer → ℝ) (Λ G_pin : Finset Polymer) : ℝ :=
  ∑ G ∈ (Λ.powerset.filter (IsCompatiblePolymerSet compat)).filter (fun G => G_pin ⊆ G),
    ∏ γ ∈ G, w γ

/-- **Abstract Kotecký–Preiss Cluster Expansion Condition (Kotecký–Preiss (1986); Part II, Proposition 3.10 (`prop:tube-local-ursell-erasure`), Equation (64) (`eq:touching-ursell-bound`))**:
    A symmetric, irreflexive compatibility relation $\sim$ (`compat`) and non-negative polymer
    activity/size/decay functions $w, a, d : \mathrm{Polymer} \to \mathbb{R}_{\ge 0}$ satisfy the
    Kotecký–Preiss convergence criterion
    $$\sum_{\gamma' \not\sim \gamma} w(\gamma') \exp\bigl(a(\gamma') + d(\gamma')\bigr) \le a(\gamma)$$
    for every polymer $\gamma$. -/
def SatisfiesKoteckyPreissCondition {Polymer : Type*} [Fintype Polymer] [DecidableEq Polymer]
    (compat : Polymer → Polymer → Prop) (w a d : Polymer → ℝ) : Prop :=
  (∀ γ₁ γ₂ : Polymer, compat γ₁ γ₂ → compat γ₂ γ₁) ∧
  (∀ γ : Polymer, ¬compat γ γ) ∧
  (∀ γ : Polymer, 0 ≤ w γ ∧ 0 ≤ a γ ∧ 0 ≤ d γ) ∧
  (∀ γ : Polymer,
    (∑ γ' ∈ Finset.univ.filter (fun γ' => ¬compat γ γ'), w γ' * Real.exp (a γ' + d γ')) ≤ a γ)

/-- Strict positivity $Z_{\mathrm{poly}}(\Lambda) > 0$ for non-negative polymer weights $w(\gamma) \ge 0$. -/
theorem polymerPartitionZ_pos {Polymer : Type*} [DecidableEq Polymer]
    (compat : Polymer → Polymer → Prop) {w : Polymer → ℝ}
    (hw : ∀ γ : Polymer, 0 ≤ w γ) (Λ : Finset Polymer) :
    0 < polymerPartitionZ compat w Λ := by
  unfold polymerPartitionZ
  have h_mem : (∅ : Finset Polymer) ∈ Λ.powerset.filter (IsCompatiblePolymerSet compat) :=
    Finset.mem_filter.mpr ⟨Finset.empty_mem_powerset Λ, isCompatiblePolymerSet_empty compat⟩
  have h_le : (1 : ℝ) ≤ ∑ G ∈ Λ.powerset.filter (IsCompatiblePolymerSet compat), ∏ γ ∈ G, w γ := by
    calc (1 : ℝ)
      _ = ∏ γ ∈ (∅ : Finset Polymer), w γ := Finset.prod_empty.symm
      _ ≤ ∑ G ∈ Λ.powerset.filter (IsCompatiblePolymerSet compat), ∏ γ ∈ G, w γ :=
        Finset.single_le_sum (f := fun G : Finset Polymer => ∏ γ ∈ G, w γ)
          (fun G _ => Finset.prod_nonneg (fun γ _ => hw γ)) h_mem
  linarith

/-- Monotonicity $Z_{\mathrm{poly}}(\Lambda_1) \le Z_{\mathrm{poly}}(\Lambda_2)$ for $\Lambda_1 \subseteq \Lambda_2$
    when $w(\gamma) \ge 0$. -/
theorem polymerPartitionZ_mono {Polymer : Type*} [DecidableEq Polymer]
    (compat : Polymer → Polymer → Prop) {w : Polymer → ℝ}
    (hw : ∀ γ : Polymer, 0 ≤ w γ) {Λ₁ Λ₂ : Finset Polymer} (h_sub : Λ₁ ⊆ Λ₂) :
    polymerPartitionZ compat w Λ₁ ≤ polymerPartitionZ compat w Λ₂ := by
  unfold polymerPartitionZ
  refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun G _ _ => Finset.prod_nonneg (fun γ _ => hw γ))
  intro G hG
  rcases Finset.mem_filter.mp hG with ⟨hG_pow, hG_compat⟩
  exact Finset.mem_filter.mpr
    ⟨Finset.mem_powerset.mpr (Finset.Subset.trans (Finset.mem_powerset.mp hG_pow) h_sub), hG_compat⟩

/-!
## 2. Finite Cauchy–Schwarz Inequality
-/

/-- Finite Cauchy–Schwarz inequality on any `Fintype`:
    $$\sum_{i} u(i) v(i) \le \sqrt{\sum_i u(i)^2} \sqrt{\sum_i v(i)^2}.$$ -/
lemma fintype_sum_mul_le_sqrt_mul_sqrt {ι : Type*} [Fintype ι]
    (u v : ι → ℝ) :
    (∑ i : ι, u i * v i) ≤
      Real.sqrt (∑ i : ι, (u i) ^ 2) * Real.sqrt (∑ i : ι, (v i) ^ 2) := by
  set U := ∑ i : ι, (u i) ^ 2
  set V := ∑ i : ι, (v i) ^ 2
  set S := ∑ i : ι, u i * v i
  have hU : 0 ≤ U := Finset.sum_nonneg fun i _ => sq_nonneg (u i)
  have hV : 0 ≤ V := Finset.sum_nonneg fun i _ => sq_nonneg (v i)
  by_cases hS : S ≤ 0
  · exact le_trans hS (by positivity)
  · push_neg at hS
    have h_quad : ∀ x y : ℝ, 0 ≤ ∑ i : ι, (x * u i - y * v i) ^ 2 :=
      fun x y => Finset.sum_nonneg fun i _ => sq_nonneg (x * u i - y * v i)
    have h_expand : ∀ x y : ℝ,
        (∑ i : ι, (x * u i - y * v i) ^ 2) = x ^ 2 * U - 2 * x * y * S + y ^ 2 * V := by
      intro x y
      have h_pt : ∀ i : ι,
          (x * u i - y * v i) ^ 2 =
            x ^ 2 * (u i) ^ 2 + (-(2 * x * y) * (u i * v i) + y ^ 2 * (v i) ^ 2) := by
        intro i; ring
      simp_rw [h_pt]
      rw [Finset.sum_add_distrib, Finset.sum_add_distrib,
        ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum]
      dsimp [U, V, S]
      ring
    have h_disc := h_quad V S
    rw [h_expand V S] at h_disc
    have h_factor : V ^ 2 * U - 2 * V * S * S + S ^ 2 * V = V * (U * V - S ^ 2) := by ring
    rw [h_factor] at h_disc
    have hV_pos : 0 < V := by
      by_contra! hV_nonpos
      have hV_zero : V = 0 := le_antisymm hV_nonpos hV
      let y₀ := (U + 1) / (2 * S)
      have h_bad := h_quad 1 y₀
      rw [h_expand 1 y₀, hV_zero] at h_bad
      have h_eq : 1 ^ 2 * U - 2 * 1 * y₀ * S + y₀ ^ 2 * 0 = -1 := by
        dsimp [y₀]
        field_simp [ne_of_gt hS]
        ring
      linarith
    have h_S_sq_le : S ^ 2 ≤ U * V := by
      by_contra! h_gt
      have : V * (U * V - S ^ 2) < 0 := mul_neg_of_pos_of_neg hV_pos (by linarith)
      linarith
    have h_rhs_sq : (Real.sqrt U * Real.sqrt V) ^ 2 = U * V := by
      rw [mul_pow, Real.sq_sqrt hU, Real.sq_sqrt hV]
    calc S
      _ = Real.sqrt (S ^ 2) := (Real.sqrt_sq (le_of_lt hS)).symm
      _ ≤ Real.sqrt ((Real.sqrt U * Real.sqrt V) ^ 2) := by
        rw [h_rhs_sq]
        exact Real.sqrt_le_sqrt h_S_sq_le
      _ = Real.sqrt U * Real.sqrt V := Real.sqrt_sq (by positivity)
