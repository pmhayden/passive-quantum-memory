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

import Proofs.DirectWorldlineCluster.WorldlineDysonUrsellSpanning

/-!
# Discrete Exponential Convolution and Worldline Mayer–Ursell Cluster Logarithm Identity

Develops the combinatorics of connected-component peeling and discrete exponential convolution (`uConv`) relating Mayer partition weights to connected Ursell cluster weights (`mayerLenSum_recurrence`, `tsum_mayer_eq_exp_tsum_ursell`). Applies this convergent series logarithm to establish the exact worldline Mayer–Ursell exponential-logarithm cluster identity (`worldline_mayer_ursell_cluster_log_identity`).

## References

* Part II, Section 3.5 (`subsec:worldline-expansion`), Proposition 3.10 (`prop:tube-local-ursell-erasure`)
* Kotecký–Preiss (1986), Cluster expansion for abstract polymer models
-/

noncomputable section

open scoped Classical BigOperators InnerProduct ComplexConjugate
open Filter Topology Asymptotics ContinuousLinearMap KMSPinchedGibbs PerturbedThermalBarrier
open SpacetimeWorldlineKP

set_option linter.unusedVariables false
set_option maxRecDepth 200000
set_option maxHeartbeats 1600000

namespace DirectWorldlineCluster

local notation "SiteCSS[" L ", " q_code "]" => UniformSite3D L (CodeSlotConfig q_code)
local notation "ℋ_CSS[" L ", " q_code "]" => ManyBodyHilbertSpace (SiteCSS[L, q_code])
local notation "ℬ_CSS[" L ", " q_code "]" => ℋ_CSS[L, q_code] →L[ℂ] ℋ_CSS[L, q_code]
local notation "IdxCSS[" L ", " q_code ", " m_max "]" => StaticCSSCheckIdx L q_code m_max
local notation "SysCSS[" L ", " q_code ", " m_max "]" =>
  IndexedCommutingProjectorHamiltonian 3 L (SiteCSS[L, q_code]) (IdxCSS[L, q_code, m_max])

/-! ### Discrete Exponential Convolution and Mayer–Ursell Recurrence -/

/-- Discrete $k$-fold convolution of a sequence $U : \mathbb{N} \to \mathbb{R}$ supported on $m \ge 1$. -/
def uConv (U : ℕ → ℝ) : ℕ → ℕ → ℝ
  | 0, 0 => 1
  | 0, _ + 1 => 0
  | k + 1, n => ∑ m ∈ Finset.Icc 1 n, U m * uConv U k (n - m)

lemma uConv_zero_zero (U : ℕ → ℝ) : uConv U 0 0 = 1 := rfl
lemma uConv_zero_succ (U : ℕ → ℝ) (n : ℕ) : uConv U 0 (n + 1) = 0 := rfl
lemma uConv_zero_eq_ite (U : ℕ → ℝ) (n : ℕ) : uConv U 0 n = if n = 0 then 1 else 0 := by cases n <;> rfl
lemma uConv_succ (U : ℕ → ℝ) (k n : ℕ) :
    uConv U (k + 1) n = ∑ m ∈ Finset.Icc 1 n, U m * uConv U k (n - m) := rfl

attribute [irreducible] uConv

lemma uConv_eq_zero_of_lt (U : ℕ → ℝ) (k : ℕ) : ∀ n, n < k → uConv U k n = 0 := by
  induction' k with k ih
  · intro n h; omega
  · intro n h; rw [uConv_succ]; apply Finset.sum_eq_zero; intro m hm
    rw [Finset.mem_Icc] at hm; rw [ih (n - m) (by omega), mul_zero]

lemma uConv_nonneg {U : ℕ → ℝ} (hU : ∀ m, 0 ≤ U m) (k : ℕ) : ∀ n, 0 ≤ uConv U k n := by
  induction' k with k ih
  · intro n; rw [uConv_zero_eq_ite]; split_ifs <;> norm_num
  · intro n; rw [uConv_succ]; exact Finset.sum_nonneg fun m _ => mul_nonneg (hU m) (ih (n - m))

lemma abs_uConv_le_uConv_abs (U : ℕ → ℝ) (k : ℕ) :
    ∀ n, |uConv U k n| ≤ uConv (fun m => |U m|) k n := by
  induction' k with k ih
  · intro n; rw [uConv_zero_eq_ite, uConv_zero_eq_ite]; split_ifs <;> norm_num
  · intro n; rw [uConv_succ, uConv_succ]
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun m _ => ?_)
    rw [abs_mul]; exact mul_le_mul_of_nonneg_left (ih (n - m)) (abs_nonneg _)

lemma uConv_one (U : ℕ → ℝ) (n : ℕ) : uConv U 1 n = if 1 ≤ n then U n else 0 := by
  rw [uConv_succ]; split_ifs with hn
  · rw [Finset.sum_eq_single n]
    · simp [uConv_zero_zero]
    · intro m hm hmn; rw [Finset.mem_Icc] at hm
      obtain ⟨d, hd⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n - m ≠ 0)
      rw [hd, uConv_zero_succ, mul_zero]
    · intro hnot; exfalso; exact hnot (Finset.mem_Icc.mpr ⟨hn, le_rfl⟩)
  · rw [Finset.Icc_eq_empty_of_lt (by omega), Finset.sum_empty]

lemma double_sum_Icc_swap (f : ℕ → ℕ → ℝ) (n : ℕ) :
    (∑ m₁ ∈ Finset.Icc 1 n, ∑ m₂ ∈ Finset.Icc 1 (n - m₁), f m₁ m₂) =
      ∑ m₂ ∈ Finset.Icc 1 n, ∑ m₁ ∈ Finset.Icc 1 (n - m₂), f m₁ m₂ := by
  have hL : ∀ m₁ ∈ Finset.Icc 1 n, (∑ m₂ ∈ Finset.Icc 1 (n - m₁), f m₁ m₂) =
      ∑ m₂ ∈ Finset.Icc 1 n, if m₁ + m₂ ≤ n then f m₁ m₂ else 0 := fun m₁ _ => by
    rw [← Finset.sum_filter]; refine Finset.sum_congr ?_ (fun _ _ => rfl)
    ext m₂; simp only [Finset.mem_Icc, Finset.mem_filter]; omega
  have hR : ∀ m₂ ∈ Finset.Icc 1 n, (∑ m₁ ∈ Finset.Icc 1 (n - m₂), f m₁ m₂) =
      ∑ m₁ ∈ Finset.Icc 1 n, if m₁ + m₂ ≤ n then f m₁ m₂ else 0 := fun m₂ _ => by
    rw [← Finset.sum_filter]; refine Finset.sum_congr ?_ (fun _ _ => rfl)
    ext m₁; simp only [Finset.mem_Icc, Finset.mem_filter]; omega
  rw [Finset.sum_congr rfl hL, Finset.sum_congr rfl hR, Finset.sum_comm]

lemma mul_uConv_succ_eq (U : ℕ → ℝ) (k : ℕ) :
    ∀ (n : ℕ), (n : ℝ) * uConv U (k + 1) n =
      ((k + 1 : ℕ) : ℝ) * ∑ m ∈ Finset.Icc 1 n, (m : ℝ) * U m * uConv U k (n - m) := by
  induction' k with k ih
  · intro n; rw [uConv_one]; split_ifs with hn
    · rw [Nat.cast_one, one_mul, Finset.sum_eq_single n]
      · simp [uConv_zero_zero]
      · intro m hm hmn; rw [Finset.mem_Icc] at hm
        obtain ⟨d, hd⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n - m ≠ 0)
        rw [hd, uConv_zero_succ, mul_zero]
      · intro hnot; exfalso; exact hnot (Finset.mem_Icc.mpr ⟨hn, le_rfl⟩)
    · rw [Finset.Icc_eq_empty_of_lt (by omega), Finset.sum_empty, mul_zero, mul_zero]
  · intro n
    have h_split : (n : ℝ) * uConv U (k + 2) n =
        (∑ m₁ ∈ Finset.Icc 1 n, (m₁ : ℝ) * U m₁ * uConv U (k + 1) (n - m₁)) +
        ∑ m₁ ∈ Finset.Icc 1 n, U m₁ * (((n - m₁ : ℕ) : ℝ) * uConv U (k + 1) (n - m₁)) := by
      rw [uConv_succ, Finset.mul_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun m₁ hm₁ => ?_
      rw [Finset.mem_Icc] at hm₁
      have h_cast : (n : ℝ) = (m₁ : ℝ) + ((n - m₁ : ℕ) : ℝ) := by
        exact_mod_cast (Nat.add_sub_of_le hm₁.2).symm
      rw [h_cast]; ring
    have h_ih : (∑ m₁ ∈ Finset.Icc 1 n, U m₁ * (((n - m₁ : ℕ) : ℝ) * uConv U (k + 1) (n - m₁))) =
        ((k + 1 : ℕ) : ℝ) * ∑ m₂ ∈ Finset.Icc 1 n, (m₂ : ℝ) * U m₂ * uConv U (k + 1) (n - m₂) := by
      have h1 : (∑ m₁ ∈ Finset.Icc 1 n, U m₁ * (((n - m₁ : ℕ) : ℝ) * uConv U (k + 1) (n - m₁))) =
          ((k + 1 : ℕ) : ℝ) * ∑ m₁ ∈ Finset.Icc 1 n, ∑ m₂ ∈ Finset.Icc 1 (n - m₁),
            U m₁ * ((m₂ : ℝ) * U m₂ * uConv U k (n - m₁ - m₂)) := by
        rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun m₁ _ => ?_
        rw [ih (n - m₁), ← mul_assoc, mul_comm (U m₁), mul_assoc, Finset.mul_sum]
      rw [h1, double_sum_Icc_swap]; congr 1; refine Finset.sum_congr rfl fun m₂ _ => ?_
      rw [uConv_succ, Finset.mul_sum]; refine Finset.sum_congr rfl fun m₁ _ => ?_
      rw [Nat.sub_right_comm n m₁ m₂]; ring
    rw [h_split, h_ih]; push_cast; ring

lemma eq_sum_uConv_of_recurrence {U Z : ℕ → ℝ} (hZ0 : Z 0 = 1)
    (hrec : ∀ (n : ℕ), 1 ≤ n → (n : ℝ) * Z n = ∑ m ∈ Finset.Icc 1 n, (m : ℝ) * U m * Z (n - m)) :
    ∀ (n : ℕ), Z n = ∑ k ∈ Finset.range (n + 1), ((k.factorial : ℝ)⁻¹) * uConv U k n := by
  intro n; induction' n using Nat.strong_induction_on with n ih
  rcases eq_or_ne n 0 with rfl | hn
  · simp [hZ0, uConv_zero_zero]
  · apply mul_left_cancel₀ (Nat.cast_ne_zero.mpr hn)
    rw [hrec n (Nat.one_le_iff_ne_zero.mpr hn)]
    have h_rhs : (n : ℝ) * (∑ k ∈ Finset.range (n + 1), ((k.factorial : ℝ)⁻¹) * uConv U k n) =
        ∑ k ∈ Finset.range n, (((k + 1).factorial : ℝ)⁻¹) * ((n : ℝ) * uConv U (k + 1) n) := by
      rw [Finset.sum_range_succ', uConv_zero_eq_ite]
      simp only [hn, ↓reduceIte, mul_zero, add_zero, Finset.mul_sum]
      exact Finset.sum_congr rfl fun k _ => by ring
    have h_step : (∑ k ∈ Finset.range n, (((k + 1).factorial : ℝ)⁻¹) * ((n : ℝ) * uConv U (k + 1) n)) =
        ∑ k ∈ Finset.range n, ∑ m ∈ Finset.Icc 1 n,
          (m : ℝ) * U m * (((k.factorial : ℝ)⁻¹) * uConv U k (n - m)) := by
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [mul_uConv_succ_eq U k n, Nat.factorial_succ, Nat.cast_mul, mul_inv_rev]
      have hk1 : ((k + 1 : ℕ) : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.succ_ne_zero k)
      rw [mul_assoc ((k.factorial : ℝ)⁻¹), ← mul_assoc (((k + 1 : ℕ) : ℝ)⁻¹),
        inv_mul_cancel₀ hk1, one_mul, Finset.mul_sum]
      exact Finset.sum_congr rfl fun m _ => by ring
    rw [h_rhs, h_step, Finset.sum_comm]; refine Finset.sum_congr rfl fun m hm => ?_
    rw [Finset.mem_Icc] at hm; rw [← Finset.mul_sum, ih (n - m) (by omega)]
    congr 1; apply Finset.sum_subset (Finset.range_mono (by omega : n - m + 1 ≤ n))
    intro k hk hnot; rw [Finset.mem_range] at hk hnot
    rw [uConv_eq_zero_of_lt U k (n - m) (by omega), mul_zero]

lemma uConv_succ_eq_sum_range {U : ℕ → ℝ} (hU0 : U 0 = 0) (k n : ℕ) :
    uConv U (k + 1) n = ∑ m ∈ Finset.range (n + 1), U m * uConv U k (n - m) := by
  rw [uConv_succ, Finset.sum_range_succ', hU0, zero_mul, add_zero]
  have h_Icc : Finset.Icc 1 n = (Finset.range n).map ⟨Nat.succ, Nat.succ_injective⟩ := by
    ext m; simp only [Finset.mem_Icc, Finset.mem_map, Finset.mem_range, Function.Embedding.coeFn_mk]
    exact ⟨fun hm => ⟨m - 1, by omega, by omega⟩, fun ⟨a, ha, h⟩ => by omega⟩
  rw [h_Icc, Finset.sum_map]; rfl

lemma summable_uncurry_of_nonneg {g : ℕ → ℕ → ℝ} (hg : ∀ k n, 0 ≤ g k n)
    (h_row : ∀ k, Summable (fun n => g k n)) (h_col : Summable (fun k => ∑' n, g k n)) :
    Summable (Function.uncurry g) := by
  refine summable_of_sum_le (c := ∑' k, ∑' n, g k n) (fun p => hg p.1 p.2) fun s => ?_
  calc (∑ p ∈ s, g p.1 p.2)
    _ ≤ ∑ p ∈ s.image Prod.fst ×ˢ s.image Prod.snd, g p.1 p.2 := by
        refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun p _ _ => hg p.1 p.2)
        exact fun p hp => Finset.mem_product.mpr ⟨Finset.mem_image_of_mem _ hp, Finset.mem_image_of_mem _ hp⟩
    _ = ∑ k ∈ s.image Prod.fst, ∑ n ∈ s.image Prod.snd, g k n := Finset.sum_product _ _ _
    _ ≤ ∑ k ∈ s.image Prod.fst, ∑' n, g k n :=
        Finset.sum_le_sum fun k _ => (h_row k).sum_le_tsum _ (fun n _ => hg k n)
    _ ≤ ∑' k, ∑' n, g k n := h_col.sum_le_tsum _ (fun k _ => tsum_nonneg (fun n => hg k n))

lemma summable_tsum_snd_of_nonneg {g : ℕ → ℕ → ℝ} (hg : ∀ k n, 0 ≤ g k n)
    (h_row : ∀ k, Summable (fun n => g k n)) (h_col_each : ∀ n, Summable (fun k => g k n))
    (h_col : Summable (fun k => ∑' n, g k n)) : Summable (fun n => ∑' k, g k n) := by
  refine summable_of_sum_le (c := ∑' k, ∑' n, g k n) (fun n => tsum_nonneg (fun k => hg k n)) fun s => ?_
  rw [(Summable.tsum_finsetSum (fun n _ => h_col_each n)).symm]
  exact Summable.tsum_le_tsum (fun k => (h_row k).sum_le_tsum s (fun n _ => hg k n))
    (summable_sum fun n _ => h_col_each n) h_col

lemma sum_range_ite_sub_eq (b : ℕ → ℝ) (m : ℕ) :
    ∀ N : ℕ, (∑ n ∈ Finset.range N, if m ≤ n then b (n - m) else 0) = ∑ d ∈ Finset.range (N - m), b d
  | 0 => by simp
  | N + 1 => by
    rw [Finset.sum_range_succ, sum_range_ite_sub_eq b m N]; split_ifs with h
    · rw [(by omega : N + 1 - m = (N - m) + 1), Finset.sum_range_succ]
    · rw [(by omega : N + 1 - m = N - m), add_zero]

lemma summable_cauchy_range_of_nonneg {a b : ℕ → ℝ} (ha : ∀ m, 0 ≤ a m) (hb : ∀ n, 0 ≤ b n)
    (ha_sum : Summable a) (hb_sum : Summable b) :
    Summable (fun n => ∑ m ∈ Finset.range (n + 1), a m * b (n - m)) := by
  refine summable_of_sum_range_le (c := (∑' m, a m) * (∑' d, b d))
    (fun n => Finset.sum_nonneg fun m _ => mul_nonneg (ha m) (hb (n - m))) (fun N => ?_)
  have h_rewrite : (∑ n ∈ Finset.range N, ∑ m ∈ Finset.range (n + 1), a m * b (n - m)) =
      ∑ m ∈ Finset.range N, a m * (∑ d ∈ Finset.range (N - m), b d) := by
    calc (∑ n ∈ Finset.range N, ∑ m ∈ Finset.range (n + 1), a m * b (n - m))
      _ = ∑ n ∈ Finset.range N, ∑ m ∈ Finset.range N, if m ≤ n then a m * b (n - m) else 0 := by
          refine Finset.sum_congr rfl fun n hn => ?_
          rw [Finset.mem_range] at hn; rw [← Finset.sum_filter]
          refine Finset.sum_congr ?_ (fun _ _ => rfl)
          ext m; simp only [Finset.mem_range, Finset.mem_filter]; omega
      _ = ∑ m ∈ Finset.range N, ∑ n ∈ Finset.range N, if m ≤ n then a m * b (n - m) else 0 := Finset.sum_comm
      _ = ∑ m ∈ Finset.range N, a m * (∑ n ∈ Finset.range N, if m ≤ n then b (n - m) else 0) := by
          refine Finset.sum_congr rfl fun m _ => ?_
          rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun n _ => by split_ifs <;> ring
      _ = ∑ m ∈ Finset.range N, a m * (∑ d ∈ Finset.range (N - m), b d) :=
          Finset.sum_congr rfl fun m _ => by rw [sum_range_ite_sub_eq]
  rw [h_rewrite]
  calc (∑ m ∈ Finset.range N, a m * (∑ d ∈ Finset.range (N - m), b d))
    _ ≤ ∑ m ∈ Finset.range N, a m * (∑' d, b d) :=
        Finset.sum_le_sum fun m _ => mul_le_mul_of_nonneg_left (hb_sum.sum_le_tsum _ (fun d _ => hb d)) (ha m)
    _ = (∑ m ∈ Finset.range N, a m) * (∑' d, b d) := (Finset.sum_mul _ _ _).symm
    _ ≤ (∑' m, a m) * (∑' d, b d) :=
        mul_le_mul_of_nonneg_right (ha_sum.sum_le_tsum _ (fun m _ => ha m)) (tsum_nonneg hb)

lemma summable_uConv_norm {U : ℕ → ℝ} (hU0 : U 0 = 0) (hU_abs : Summable (fun m => ‖U m‖)) (k : ℕ) :
    Summable (fun n => ‖uConv U k n‖) := by
  induction' k with k hk_sum
  · refine summable_of_ne_finset_zero (s := {0}) fun n hn => ?_
    rw [Finset.mem_singleton] at hn; rw [uConv_zero_eq_ite, if_neg hn, norm_zero]
  · have h_range : Summable (fun n => ∑ m ∈ Finset.range (n + 1), ‖U m‖ * ‖uConv U k (n - m)‖) :=
      summable_cauchy_range_of_nonneg (a := fun m => ‖U m‖) (b := fun n => ‖uConv U k n‖)
        (fun m => norm_nonneg (U m)) (fun n => norm_nonneg (uConv U k n)) hU_abs hk_sum
    refine h_range.of_nonneg_of_le (fun n => norm_nonneg (uConv U (k + 1) n)) (fun n => ?_)
    rw [uConv_succ_eq_sum_range hU0]
    exact (norm_sum_le _ _).trans (Finset.sum_le_sum fun m _ => by rw [norm_mul])

lemma tsum_uConv {U : ℕ → ℝ} (hU0 : U 0 = 0) (hU_abs : Summable (fun m => ‖U m‖)) (k : ℕ) :
    (∑' n, uConv U k n) = (∑' m, U m) ^ k := by
  induction' k with k hk_tsum
  · rw [pow_zero, tsum_eq_single 0]
    · exact uConv_zero_zero U
    · intro n hn; rw [uConv_zero_eq_ite, if_neg hn]
  · have h_cauchy : (∑' m, U m) * (∑' n, uConv U k n) =
        ∑' n, ∑ m ∈ Finset.range (n + 1), U m * uConv U k (n - m) :=
      tsum_mul_tsum_eq_tsum_sum_range_of_summable_norm (f := U) (g := uConv U k)
        hU_abs (summable_uConv_norm hU0 hU_abs k)
    rw [pow_succ', ← hk_tsum, h_cauchy]
    exact tsum_congr fun n => uConv_succ_eq_sum_range hU0 k n

lemma tsum_norm_uConv_le {U : ℕ → ℝ} (hU0 : U 0 = 0) (hU_abs : Summable (fun m => ‖U m‖)) (k : ℕ) :
    (∑' n, ‖uConv U k n‖) ≤ (∑' m, ‖U m‖) ^ k := by
  have hk_sum := summable_uConv_norm hU0 hU_abs k
  have hU_abs_norm : Summable (fun m => ‖‖U m‖‖) := by simpa using hU_abs
  have hU0_norm : ‖U 0‖ = 0 := by simp [hU0]
  rw [← tsum_uConv hU0_norm hU_abs_norm k]
  have h_abs_sum : Summable (fun n => uConv (fun m => ‖U m‖) k n) :=
    (summable_uConv_norm hU0_norm hU_abs_norm k).of_nonneg_of_le
      (fun n => uConv_nonneg (fun _ => norm_nonneg _) k n)
      (fun n => by rw [Real.norm_of_nonneg (uConv_nonneg (fun _ => norm_nonneg _) k n)])
  refine Summable.tsum_le_tsum (fun n => ?_) hk_sum h_abs_sum
  simpa [Real.norm_eq_abs] using abs_uConv_le_uConv_abs U k n

lemma summable_and_tsum_eq_exp_of_recurrence {U Z : ℕ → ℝ} (hU0 : U 0 = 0) (hZ0 : Z 0 = 1)
    (hU_abs : Summable (fun m => ‖U m‖))
    (hrec : ∀ (n : ℕ), 1 ≤ n → (n : ℝ) * Z n = ∑ m ∈ Finset.Icc 1 n, (m : ℝ) * U m * Z (n - m)) :
    Summable (fun n => ‖Z n‖) ∧ (∑' n, Z n) = Real.exp (∑' m, U m) := by
  have hZ_eq := eq_sum_uConv_of_recurrence hZ0 hrec
  have hZ_tsum : ∀ n, Z n = ∑' k, ((k.factorial : ℝ)⁻¹) * uConv U k n := fun n => by
    symm; rw [hZ_eq n]; refine tsum_eq_sum fun k hk => ?_
    rw [Finset.mem_range] at hk; rw [uConv_eq_zero_of_lt U k n (by omega), mul_zero]
  have h_row_sum : ∀ k, Summable (fun n => ‖((k.factorial : ℝ)⁻¹) * uConv U k n‖) := fun k => by
    simpa [norm_mul] using (summable_uConv_norm hU0 hU_abs k).mul_left ‖(k.factorial : ℝ)⁻¹‖
  have h_col_bound : Summable (fun k => ∑' n, ‖((k.factorial : ℝ)⁻¹) * uConv U k n‖) := by
    refine Summable.of_nonneg_of_le (fun k => tsum_nonneg fun _ => norm_nonneg _) (fun k => ?_)
      (Real.summable_pow_div_factorial (∑' m, ‖U m‖))
    have h_pos : 0 ≤ ((k.factorial : ℝ)⁻¹) := inv_nonneg.mpr (Nat.cast_nonneg _)
    calc (∑' n, ‖((k.factorial : ℝ)⁻¹) * uConv U k n‖)
      _ = ((k.factorial : ℝ)⁻¹) * ∑' n, ‖uConv U k n‖ := by
          rw [← tsum_mul_left]; exact tsum_congr fun n => by rw [norm_mul, Real.norm_of_nonneg h_pos]
      _ ≤ ((k.factorial : ℝ)⁻¹) * (∑' m, ‖U m‖) ^ k :=
          mul_le_mul_of_nonneg_left (tsum_norm_uConv_le hU0 hU_abs k) h_pos
      _ = ((∑' m, ‖U m‖) ^ k) / (k.factorial : ℝ) := by ring
  have h_prod : Summable (Function.uncurry fun k n => ((k.factorial : ℝ)⁻¹) * uConv U k n) :=
    (summable_uncurry_of_nonneg (fun _ _ => norm_nonneg _) h_row_sum h_col_bound).of_norm
  have h_col_each : ∀ n, Summable (fun k => ‖((k.factorial : ℝ)⁻¹) * uConv U k n‖) := fun n => by
    refine summable_of_ne_finset_zero (s := Finset.range (n + 1)) fun k hk => ?_
    rw [Finset.mem_range] at hk; rw [uConv_eq_zero_of_lt U k n (by omega), mul_zero, norm_zero]
  have hZ_norm : Summable (fun n => ‖Z n‖) := by
    refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun n => ?_)
      (summable_tsum_snd_of_nonneg (fun _ _ => norm_nonneg _) h_row_sum h_col_each h_col_bound)
    rw [hZ_tsum n]; exact norm_tsum_le_tsum_norm (h_col_each n)
  refine ⟨hZ_norm, ?_⟩
  calc (∑' n, Z n) = ∑' n, ∑' k, ((k.factorial : ℝ)⁻¹) * uConv U k n := tsum_congr hZ_tsum
    _ = ∑' k, ∑' n, ((k.factorial : ℝ)⁻¹) * uConv U k n :=
        Summable.tsum_comm' (f := fun k n => ((k.factorial : ℝ)⁻¹) * uConv U k n)
          h_prod (fun k => (h_row_sum k).of_norm) (fun n => (h_col_each n).of_norm)
    _ = ∑' k : ℕ, ((∑' m, U m) ^ k) / (k.factorial : ℝ) :=
        tsum_congr fun k => by rw [tsum_mul_left, tsum_uConv hU0 hU_abs k, div_eq_inv_mul]
    _ = Real.exp (∑' m, U m) := by rw [Real.exp_eq_exp_ℝ, NormedSpace.exp_eq_tsum_div]

/-! ### Order-Preserving Subclusters and Connected-Component Peeling of Vertex 0 -/

def subCluster {α : Type*} (K : List α) (S : Finset (Fin K.length)) : List α :=
  List.ofFn (fun i : Fin S.card => K.get (S.orderEmbOfFin rfl i))

@[simp] lemma length_subCluster {α : Type*} (K : List α) (S : Finset (Fin K.length)) :
    (subCluster K S).length = S.card := List.length_ofFn

lemma get_subCluster {α : Type*} (K : List α) (S : Finset (Fin K.length)) (i : Fin (subCluster K S).length) :
    (subCluster K S).get i = K.get (S.orderEmbOfFin rfl (i.cast (length_subCluster K S))) := by
  revert i; dsimp [subCluster]; intro i; simp; rfl

def subClusterVertEmb {α : Type*} (K : List α) (S : Finset (Fin K.length)) :
    Fin (subCluster K S).length ↪ Fin K.length :=
  (finCongr (length_subCluster K S)).toEmbedding.trans (S.orderEmbOfFin rfl).toEmbedding

@[simp] lemma subClusterVertEmb_apply {α : Type*} (K : List α) (S : Finset (Fin K.length))
    (i : Fin (subCluster K S).length) :
    subClusterVertEmb K S i = S.orderEmbOfFin rfl (i.cast (length_subCluster K S)) := rfl

lemma subClusterVertEmb_mem {α : Type*} (K : List α) (S : Finset (Fin K.length))
    (i : Fin (subCluster K S).length) : subClusterVertEmb K S i ∈ S := Finset.orderEmbOfFin_mem S rfl _

lemma subClusterVertEmb_surjOn {α : Type*} (K : List α) (S : Finset (Fin K.length))
    {v : Fin K.length} (hv : v ∈ S) : ∃ i : Fin (subCluster K S).length, subClusterVertEmb K S i = v := by
  have hmem : v ∈ Set.range (S.orderEmbOfFin rfl) := by rw [Finset.range_orderEmbOfFin]; exact hv
  rcases hmem with ⟨j, rfl⟩; exact ⟨j.cast (length_subCluster K S).symm, by simp⟩

lemma subClusterVertEmb_lt_iff {α : Type*} (K : List α) (S : Finset (Fin K.length))
    (i j : Fin (subCluster K S).length) :
    subClusterVertEmb K S i < subClusterVertEmb K S j ↔ i < j := by
  simp only [subClusterVertEmb_apply, OrderEmbedding.lt_iff_lt]; rfl

def subClusterEdgeEmb {α : Type*} (K : List α) (S : Finset (Fin K.length)) :
    (Fin (subCluster K S).length × Fin (subCluster K S).length) ↪ (Fin K.length × Fin K.length) :=
  Function.Embedding.prodMap (subClusterVertEmb K S) (subClusterVertEmb K S)

@[simp] lemma subClusterEdgeEmb_apply {α : Type*} (K : List α) (S : Finset (Fin K.length))
    (e : Fin (subCluster K S).length × Fin (subCluster K S).length) :
    subClusterEdgeEmb K S e = (subClusterVertEmb K S e.1, subClusterVertEmb K S e.2) := rfl

def clusterIncompatEdges {L q_code m_max : ℕ} [NeZero L]
    (sys : SysCSS[L, q_code, m_max]) (C_RCA : ℝ)
    (K : WorldlineUrsellCluster L q_code) : Finset (Fin K.length × Fin K.length) :=
  Finset.univ.filter (fun e => e.1 < e.2 ∧ PolymerClusterOverlap sys C_RCA K e.1 e.2)

lemma map_clusterIncompatEdges_subCluster {L q_code m_max : ℕ} [NeZero L]
    (sys : SysCSS[L, q_code, m_max]) (C_RCA : ℝ)
    (K : WorldlineUrsellCluster L q_code) (S : Finset (Fin K.length)) :
    (clusterIncompatEdges sys C_RCA (subCluster K S)).map (subClusterEdgeEmb K S) =
      (clusterIncompatEdges sys C_RCA K).filter (fun e => e.1 ∈ S ∧ e.2 ∈ S) := by
  ext ⟨u, v⟩
  simp only [clusterIncompatEdges, Finset.mem_map, Finset.mem_filter, Finset.mem_univ,
    true_and, subClusterEdgeEmb_apply, Prod.mk.injEq]
  simp only [PolymerClusterOverlap]
  constructor
  · rintro ⟨⟨i, j⟩, ⟨hij, hne, hinc⟩, rfl, rfl⟩
    rw [get_subCluster, get_subCluster] at hinc
    have hlt := (subClusterVertEmb_lt_iff K S i j).mpr hij
    exact ⟨⟨hlt, ne_of_lt hlt, hinc⟩, subClusterVertEmb_mem K S i, subClusterVertEmb_mem K S j⟩
  · rintro ⟨⟨huv, _, hinc⟩, hu, hv⟩
    obtain ⟨i, rfl⟩ := subClusterVertEmb_surjOn K S hu
    obtain ⟨j, rfl⟩ := subClusterVertEmb_surjOn K S hv
    have hij := (subClusterVertEmb_lt_iff K S i j).mp huv
    refine ⟨(i, j), ⟨hij, ne_of_lt hij, ?_⟩, rfl, rfl⟩
    simpa only [get_subCluster, subClusterVertEmb_apply] using hinc

lemma penroseAdj_map_subClusterEdgeEmb {α : Type*} (K : List α) (S : Finset (Fin K.length))
    (H : Finset (Fin (subCluster K S).length × Fin (subCluster K S).length))
    (i j : Fin (subCluster K S).length) :
    PenroseAdj (H.map (subClusterEdgeEmb K S)) (subClusterVertEmb K S i) (subClusterVertEmb K S j) ↔
      PenroseAdj H i j := by
  simp only [PenroseAdj, Finset.mem_map, subClusterEdgeEmb_apply, Prod.mk.injEq,
    (subClusterVertEmb K S).injective.eq_iff, Prod.exists]
  exact ⟨fun h => h.elim (fun ⟨_, _, hab, rfl, rfl⟩ => Or.inl hab) (fun ⟨_, _, hab, rfl, rfl⟩ => Or.inr hab),
    fun h => h.elim (fun hab => Or.inl ⟨i, j, hab, rfl, rfl⟩) (fun hba => Or.inr ⟨j, i, hba, rfl, rfl⟩)⟩

lemma reflTransGen_map_subClusterEdgeEmb_iff {α : Type*} (K : List α) (S : Finset (Fin K.length))
    (H : Finset (Fin (subCluster K S).length × Fin (subCluster K S).length))
    (i j : Fin (subCluster K S).length) :
    Relation.ReflTransGen
      (fun a b => a ∈ S ∧ b ∈ S ∧ PenroseAdj (H.map (subClusterEdgeEmb K S)) a b)
      (subClusterVertEmb K S i) (subClusterVertEmb K S j) ↔
    Relation.ReflTransGen
      (fun a b => a ∈ (Finset.univ : Finset (Fin (subCluster K S).length)) ∧
        b ∈ (Finset.univ : Finset (Fin (subCluster K S).length)) ∧ PenroseAdj H a b) i j := by
  constructor
  · intro h
    generalize hu : subClusterVertEmb K S i = u at h
    generalize hv : subClusterVertEmb K S j = v at h
    induction h generalizing i j with
    | refl =>
      subst hv; cases (subClusterVertEmb K S).injective hu; exact Relation.ReflTransGen.refl
    | tail hab hbc ih =>
      subst hv; obtain ⟨k, rfl⟩ := subClusterVertEmb_surjOn K S hbc.1
      exact Relation.ReflTransGen.tail (ih i k hu rfl)
        ⟨Finset.mem_univ k, Finset.mem_univ j, (penroseAdj_map_subClusterEdgeEmb K S H k j).mp hbc.2.2⟩
  · intro h
    induction h with
    | refl => exact Relation.ReflTransGen.refl
    | tail _ hbc ih =>
      exact Relation.ReflTransGen.tail ih ⟨subClusterVertEmb_mem K S _, subClusterVertEmb_mem K S _,
        (penroseAdj_map_subClusterEdgeEmb K S H _ _).mpr hbc.2.2⟩

lemma kpIsConnectedSubgraph_map_subClusterEdgeEmb_iff {α : Type*} (K : List α) (S : Finset (Fin K.length))
    (H : Finset (Fin (subCluster K S).length × Fin (subCluster K S).length)) :
    KPIsConnectedSubgraph (PenroseAdj (H.map (subClusterEdgeEmb K S))) S ↔
      KPIsConnectedSubgraph (PenroseAdj H) Finset.univ := by
  simp only [KPIsConnectedSubgraph]
  constructor
  · rintro ⟨⟨u₀, hu₀⟩, hconn⟩
    obtain ⟨i₀, rfl⟩ := subClusterVertEmb_surjOn K S hu₀
    refine ⟨⟨i₀, Finset.mem_univ i₀⟩, fun i _ j _ => ?_⟩
    exact (reflTransGen_map_subClusterEdgeEmb_iff K S H i j).mp
      (hconn _ (subClusterVertEmb_mem K S i) _ (subClusterVertEmb_mem K S j))
  · rintro ⟨⟨i₀, _⟩, hconn⟩
    refine ⟨⟨subClusterVertEmb K S i₀, subClusterVertEmb_mem K S i₀⟩, fun u hu v hv => ?_⟩
    obtain ⟨i, rfl⟩ := subClusterVertEmb_surjOn K S hu
    obtain ⟨j, rfl⟩ := subClusterVertEmb_surjOn K S hv
    exact (reflTransGen_map_subClusterEdgeEmb_iff K S H i j).mpr (hconn i (Finset.mem_univ i) j (Finset.mem_univ j))

def graphConnComp {n : ℕ} (G : Finset (Fin n × Fin n)) (r : Fin n) : Finset (Fin n) :=
  Finset.univ.filter (fun v => Relation.ReflTransGen (PenroseAdj G) r v)

lemma mem_graphConnComp_iff {n : ℕ} (G : Finset (Fin n × Fin n)) (r v : Fin n) :
    v ∈ graphConnComp G r ↔ Relation.ReflTransGen (PenroseAdj G) r v := by simp [graphConnComp]

lemma self_mem_graphConnComp {n : ℕ} (G : Finset (Fin n × Fin n)) (r : Fin n) :
    r ∈ graphConnComp G r := (mem_graphConnComp_iff G r r).mpr Relation.ReflTransGen.refl

lemma penroseAdj_filter_iff {n : ℕ} (G : Finset (Fin n × Fin n)) (S : Finset (Fin n)) (u v : Fin n) :
    PenroseAdj (G.filter (fun e => e.1 ∈ S ∧ e.2 ∈ S)) u v ↔ u ∈ S ∧ v ∈ S ∧ PenroseAdj G u v := by
  simp only [PenroseAdj, Finset.mem_filter]; tauto

lemma reflTransGen_symm_of_symm {α : Type*} {R : α → α → Prop}
    (hR : ∀ a b, R a b → R b a) {u v : α} (h : Relation.ReflTransGen R u v) :
    Relation.ReflTransGen R v u := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hbc ih => exact Relation.ReflTransGen.head (hR _ _ hbc) ih

lemma graphConnComp_eq_iff {n : ℕ} (G : Finset (Fin n × Fin n)) (r : Fin n)
    (S : Finset (Fin n)) (hr : r ∈ S) :
    graphConnComp G r = S ↔
      KPIsConnectedSubgraph (PenroseAdj (G.filter (fun e => e.1 ∈ S ∧ e.2 ∈ S))) S ∧
      ∀ e ∈ G, (e.1 ∈ S ∧ e.2 ∈ S) ∨ (e.1 ∈ Sᶜ ∧ e.2 ∈ Sᶜ) := by
  constructor
  · intro hGS; subst hGS
    refine ⟨⟨⟨r, self_mem_graphConnComp G r⟩, fun u hu v hv => ?_⟩, fun e he => ?_⟩
    · have hpath : ∀ w, Relation.ReflTransGen (PenroseAdj G) r w →
          Relation.ReflTransGen (fun a b => a ∈ graphConnComp G r ∧ b ∈ graphConnComp G r ∧
            PenroseAdj (G.filter (fun e => e.1 ∈ graphConnComp G r ∧ e.2 ∈ graphConnComp G r)) a b) r w := by
        intro w hw; induction hw with
        | refl => exact Relation.ReflTransGen.refl
        | tail hab hbc ih =>
          have hb := (mem_graphConnComp_iff G r _).mpr hab
          have hc := (mem_graphConnComp_iff G r _).mpr (Relation.ReflTransGen.tail hab hbc)
          exact Relation.ReflTransGen.tail ih ⟨hb, hc, (penroseAdj_filter_iff G (graphConnComp G r) _ _).mpr ⟨hb, hc, hbc⟩⟩
      exact Relation.ReflTransGen.trans
        (reflTransGen_symm_of_symm (fun a b hab => ⟨hab.2.1, hab.1, hab.2.2.symm⟩)
          (hpath u ((mem_graphConnComp_iff G r u).mp hu)))
        (hpath v ((mem_graphConnComp_iff G r v).mp hv))
    · by_cases he1 : e.1 ∈ graphConnComp G r
      · exact Or.inl ⟨he1, (mem_graphConnComp_iff G r e.2).mpr
          (Relation.ReflTransGen.tail ((mem_graphConnComp_iff G r e.1).mp he1) (Or.inl he))⟩
      · rw [Finset.mem_compl, Finset.mem_compl]
        exact Or.inr ⟨he1, fun he2 => he1 ((mem_graphConnComp_iff G r e.1).mpr
          (Relation.ReflTransGen.tail ((mem_graphConnComp_iff G r e.2).mp he2) (Or.inr he)))⟩
  · rintro ⟨⟨_, hconn⟩, hsplit⟩; ext v; rw [mem_graphConnComp_iff]
    constructor
    · intro hrv; induction hrv with
      | refl => exact hr
      | tail _ hbc ih =>
        rcases hbc with hbc | hcb
        · exact (hsplit _ hbc).elim And.right (fun h => (Finset.mem_compl.mp h.1 ih).elim)
        · exact (hsplit _ hcb).elim And.left (fun h => (Finset.mem_compl.mp h.2 ih).elim)
    · intro hv
      have hpath : ∀ w, Relation.ReflTransGen
          (fun a b => a ∈ S ∧ b ∈ S ∧ PenroseAdj (G.filter (fun e => e.1 ∈ S ∧ e.2 ∈ S)) a b) r w →
          Relation.ReflTransGen (PenroseAdj G) r w := by
        intro w hw; induction hw with
        | refl => exact Relation.ReflTransGen.refl
        | tail _ hbc ih => exact Relation.ReflTransGen.tail ih ((penroseAdj_filter_iff G S _ _).mp hbc.2.2).2.2
      exact hpath v (hconn r hr v hv)

lemma sum_powerset_filter_graphConnComp_eq {n : ℕ}
    (E : Finset (Fin n × Fin n)) (r : Fin n) (S : Finset (Fin n)) (hr : r ∈ S) :
    (∑ G ∈ E.powerset.filter (fun G => graphConnComp G r = S), (-1 : ℝ) ^ G.card) =
      (∑ G₁ ∈ (E.filter (fun e => e.1 ∈ S ∧ e.2 ∈ S)).powerset.filter
        (fun G₁ => KPIsConnectedSubgraph (PenroseAdj G₁) S), (-1 : ℝ) ^ G₁.card) *
      (∑ G₂ ∈ (E.filter (fun e => e.1 ∈ Sᶜ ∧ e.2 ∈ Sᶜ)).powerset, (-1 : ℝ) ^ G₂.card) := by
  rw [Finset.sum_mul_sum, ← Finset.sum_product']
  refine Finset.sum_bij'
    (fun G _ => (G.filter (fun e => e.1 ∈ S ∧ e.2 ∈ S), G.filter (fun e => e.1 ∈ Sᶜ ∧ e.2 ∈ Sᶜ)))
    (fun p _ => p.1 ∪ p.2) ?_ ?_ ?_ ?_ ?_
  · intro G hG; simp only [Finset.mem_filter, Finset.mem_powerset] at hG
    obtain ⟨hGE, hconn, hsplit⟩ := hG.1, (graphConnComp_eq_iff G r S hr).mp hG.2
    simp only [Finset.mem_product, Finset.mem_filter, Finset.mem_powerset]
    exact ⟨⟨fun e he => by simp only [Finset.mem_filter] at he ⊢; exact ⟨hGE he.1, he.2⟩, hconn⟩,
      fun e he => by simp only [Finset.mem_filter] at he ⊢; exact ⟨hGE he.1, he.2⟩⟩
  · rintro ⟨G₁, G₂⟩ hp
    simp only [Finset.mem_product, Finset.mem_filter, Finset.mem_powerset] at hp ⊢
    obtain ⟨⟨hG₁, hconn₁⟩, hG₂⟩ := hp
    have h_filt₁ : (G₁ ∪ G₂).filter (fun e => e.1 ∈ S ∧ e.2 ∈ S) = G₁ := by
      ext e; simp only [Finset.mem_filter, Finset.mem_union]
      refine ⟨fun ⟨he, hS⟩ => he.elim id (fun he₂ => (Finset.mem_compl.mp (Finset.mem_filter.mp (hG₂ he₂)).2.1 hS.1).elim),
        fun he => ⟨Or.inl he, (Finset.mem_filter.mp (hG₁ he)).2⟩⟩
    refine ⟨Finset.union_subset (hG₁.trans (Finset.filter_subset _ _)) (hG₂.trans (Finset.filter_subset _ _)), ?_⟩
    rw [graphConnComp_eq_iff _ r S hr, h_filt₁]
    exact ⟨hconn₁, fun e he => (Finset.mem_union.mp he).imp
      (fun he₁ => (Finset.mem_filter.mp (hG₁ he₁)).2) (fun he₂ => (Finset.mem_filter.mp (hG₂ he₂)).2)⟩
  · intro G hG; simp only [Finset.mem_filter, Finset.mem_powerset] at hG
    have hsplit := ((graphConnComp_eq_iff G r S hr).mp hG.2).2
    ext e; simp only [Finset.mem_union, Finset.mem_filter]
    exact ⟨fun h => h.elim And.left And.left, fun he => (hsplit e he).imp (And.intro he) (And.intro he)⟩
  · rintro ⟨G₁, G₂⟩ hp; simp only [Finset.mem_product, Finset.mem_filter, Finset.mem_powerset] at hp
    obtain ⟨⟨hG₁, _⟩, hG₂⟩ := hp; ext e <;> simp only [Finset.mem_filter, Finset.mem_union]
    · exact ⟨fun ⟨he, hS⟩ => he.elim id (fun he₂ => (Finset.mem_compl.mp (Finset.mem_filter.mp (hG₂ he₂)).2.1 hS.1).elim),
        fun he => ⟨Or.inl he, (Finset.mem_filter.mp (hG₁ he)).2⟩⟩
    · exact ⟨fun ⟨he, hSc⟩ => he.elim (fun he₁ => (Finset.mem_compl.mp hSc.1 (Finset.mem_filter.mp (hG₁ he₁)).2.1).elim) id,
        fun he => ⟨Or.inr he, (Finset.mem_filter.mp (hG₂ he)).2⟩⟩
  · intro G hG; simp only [Finset.mem_filter, Finset.mem_powerset] at hG
    have hsplit := ((graphConnComp_eq_iff G r S hr).mp hG.2).2
    have h_union : G.filter (fun e => e.1 ∈ S ∧ e.2 ∈ S) ∪ G.filter (fun e => e.1 ∈ Sᶜ ∧ e.2 ∈ Sᶜ) = G := by
      ext e; simp only [Finset.mem_union, Finset.mem_filter]
      exact ⟨fun h => h.elim And.left And.left, fun he => (hsplit e he).imp (And.intro he) (And.intro he)⟩
    have h_disj : Disjoint (G.filter (fun e => e.1 ∈ S ∧ e.2 ∈ S)) (G.filter (fun e => e.1 ∈ Sᶜ ∧ e.2 ∈ Sᶜ)) :=
      Finset.disjoint_left.mpr fun e he₁ he₂ =>
        Finset.mem_compl.mp (Finset.mem_filter.mp he₂).2.1 (Finset.mem_filter.mp he₁).2.1
    rw [← pow_add, ← Finset.card_union_of_disjoint h_disj, h_union]

lemma sum_powerset_map_embedding {α β : Type*} (emb : α ↪ β) (A : Finset α)
    (P : Finset α → Prop) (Q : Finset β → Prop) [DecidablePred P] [DecidablePred Q]
    (hPQ : ∀ H ⊆ A, P H ↔ Q (H.map emb)) :
    (∑ H ∈ A.powerset.filter P, (-1 : ℝ) ^ H.card) =
      ∑ G ∈ (A.map emb).powerset.filter Q, (-1 : ℝ) ^ G.card := by
  refine Finset.sum_bij' (fun H _ => H.map emb) (fun G _ => A.filter (fun x => emb x ∈ G))
    ?_ ?_ ?_ ?_ (fun _ _ => by rw [Finset.card_map])
  · intro H hH; simp only [Finset.mem_filter, Finset.mem_powerset] at hH ⊢
    exact ⟨Finset.map_subset_map.mpr hH.1, (hPQ H hH.1).mp hH.2⟩
  · intro G hG; simp only [Finset.mem_filter, Finset.mem_powerset] at hG ⊢
    have h_map : (A.filter (fun x => emb x ∈ G)).map emb = G := by
      ext y; simp only [Finset.mem_map, Finset.mem_filter]
      refine ⟨fun ⟨x, ⟨_, hxG⟩, h⟩ => h ▸ hxG, fun hyG => ?_⟩
      rcases Finset.mem_map.mp (hG.1 hyG) with ⟨x, hxA, rfl⟩; exact ⟨x, ⟨hxA, hyG⟩, rfl⟩
    refine ⟨Finset.filter_subset _ _, ?_⟩
    rw [hPQ _ (Finset.filter_subset _ _), h_map]; exact hG.2
  · intro H hH; simp only [Finset.mem_filter, Finset.mem_powerset] at hH
    ext x; simp only [Finset.mem_filter, Finset.mem_map, emb.injective.eq_iff, exists_eq_right]
    exact ⟨And.right, fun hx => ⟨hH.1 hx, hx⟩⟩
  · intro G hG; simp only [Finset.mem_filter, Finset.mem_powerset] at hG
    ext y; simp only [Finset.mem_map, Finset.mem_filter]
    refine ⟨fun ⟨x, ⟨_, hxG⟩, h⟩ => h ▸ hxG, fun hyG => ?_⟩
    rcases Finset.mem_map.mp (hG.1 hyG) with ⟨x, hxA, rfl⟩; exact ⟨x, ⟨hxA, hyG⟩, rfl⟩

lemma mayer_powerset_sum_eq_sum_connComp {L q_code m_max : ℕ} [NeZero L]
    (sys : SysCSS[L, q_code, m_max]) (C_RCA : ℝ)
    (K : WorldlineUrsellCluster L q_code) (hn : 1 ≤ K.length) :
    (∑ G ∈ (clusterIncompatEdges sys C_RCA K).powerset, (-1 : ℝ) ^ G.card) =
      ∑ S ∈ (Finset.univ : Finset (Fin K.length)).powerset.filter (fun S => (⟨0, hn⟩ : Fin K.length) ∈ S),
        (∑ G₁ ∈ (clusterIncompatEdges sys C_RCA (subCluster K S)).powerset.filter
          (fun G₁ => KPIsConnectedSubgraph (PenroseAdj G₁) Finset.univ), (-1 : ℝ) ^ G₁.card) *
        (∑ G₂ ∈ (clusterIncompatEdges sys C_RCA (subCluster K Sᶜ)).powerset, (-1 : ℝ) ^ G₂.card) := by
  have h_fib : (∑ G ∈ (clusterIncompatEdges sys C_RCA K).powerset, (-1 : ℝ) ^ G.card) =
      ∑ S ∈ (Finset.univ : Finset (Fin K.length)).powerset.filter (fun S => (⟨0, hn⟩ : Fin K.length) ∈ S),
        ∑ G ∈ (clusterIncompatEdges sys C_RCA K).powerset.filter
          (fun G => graphConnComp G ⟨0, hn⟩ = S), (-1 : ℝ) ^ G.card := by
    symm; refine Finset.sum_fiberwise_of_maps_to (fun G _ => ?_) _
    simp only [Finset.mem_filter, Finset.mem_powerset]
    exact ⟨Finset.subset_univ _, self_mem_graphConnComp G ⟨0, hn⟩⟩
  rw [h_fib]; refine Finset.sum_congr rfl fun S hS => ?_
  simp only [Finset.mem_filter, Finset.mem_powerset] at hS
  rw [sum_powerset_filter_graphConnComp_eq _ ⟨0, hn⟩ S hS.2]; congr 1
  · rw [← map_clusterIncompatEdges_subCluster sys C_RCA K S]; symm
    exact sum_powerset_map_embedding (subClusterEdgeEmb K S)
      (clusterIncompatEdges sys C_RCA (subCluster K S))
      (fun H => KPIsConnectedSubgraph (PenroseAdj H) Finset.univ)
      (fun G => KPIsConnectedSubgraph (PenroseAdj G) S)
      (fun H _ => (kpIsConnectedSubgraph_map_subClusterEdgeEmb_iff K S H).symm)
  · rw [← map_clusterIncompatEdges_subCluster sys C_RCA K Sᶜ]; symm
    have h1 : (clusterIncompatEdges sys C_RCA (subCluster K Sᶜ)).powerset =
        (clusterIncompatEdges sys C_RCA (subCluster K Sᶜ)).powerset.filter (fun _ => True) := by
      rw [Finset.filter_true]
    have h2 : ((clusterIncompatEdges sys C_RCA (subCluster K Sᶜ)).map (subClusterEdgeEmb K Sᶜ)).powerset =
        ((clusterIncompatEdges sys C_RCA (subCluster K Sᶜ)).map (subClusterEdgeEmb K Sᶜ)).powerset.filter
          (fun _ => True) := by rw [Finset.filter_true]
    rw [h1, h2]
    exact sum_powerset_map_embedding (subClusterEdgeEmb K Sᶜ)
      (clusterIncompatEdges sys C_RCA (subCluster K Sᶜ))
      (fun _ => True) (fun _ => True) (fun _ _ => Iff.rfl)

def subClusterLen {α : Type*} {n : ℕ} (K : List α) (hK : K.length = n) (S : Finset (Fin n)) : List α :=
  List.ofFn (fun i : Fin S.card => K.get ((S.orderEmbOfFin rfl i).cast hK.symm))

@[simp] lemma subClusterLen_rfl {α : Type*} (K : List α) (S : Finset (Fin K.length)) :
    subClusterLen K rfl S = subCluster K S := rfl

@[simp] lemma length_subClusterLen {α : Type*} {n : ℕ} (K : List α) (hK : K.length = n) (S : Finset (Fin n)) :
    (subClusterLen K hK S).length = S.card := List.length_ofFn

lemma subClusterLen_ofFn {α : Type*} {n : ℕ} (f : Fin n → α) (S : Finset (Fin n)) :
    subClusterLen (List.ofFn f) List.length_ofFn S =
      List.ofFn (fun i : Fin S.card => f (S.orderEmbOfFin rfl i)) := by simp [subClusterLen]

lemma mayer_powerset_sum_eq_sum_connComp_len {L q_code m_max n : ℕ} [NeZero L]
    (sys : SysCSS[L, q_code, m_max]) (C_RCA : ℝ)
    (K : WorldlineUrsellCluster L q_code) (hK : K.length = n) (hn : 1 ≤ n) :
    (∑ G ∈ (clusterIncompatEdges sys C_RCA K).powerset, (-1 : ℝ) ^ G.card) =
      ∑ S ∈ (Finset.univ : Finset (Fin n)).powerset.filter (fun S => (⟨0, hn⟩ : Fin n) ∈ S),
        (∑ G₁ ∈ (clusterIncompatEdges sys C_RCA (subClusterLen K hK S)).powerset.filter
          (fun G₁ => KPIsConnectedSubgraph (PenroseAdj G₁) Finset.univ), (-1 : ℝ) ^ G₁.card) *
        (∑ G₂ ∈ (clusterIncompatEdges sys C_RCA (subClusterLen K hK Sᶜ)).powerset, (-1 : ℝ) ^ G₂.card) := by
  subst hK; exact mayer_powerset_sum_eq_sum_connComp sys C_RCA K hn

lemma prod_map_eq_prod_fin {α : Type*} (w : α → ℝ) (K : List α) :
    (K.map w).prod = ∏ i : Fin K.length, w (K.get i) := by
  induction' K with a K ih
  · simp
  · rw [List.map_cons, List.prod_cons, ih]
    exact (Fin.prod_univ_succ (fun i : Fin (K.length + 1) => w ((a :: K).get i))).symm

lemma prod_map_subCluster_eq {α : Type*} (w : α → ℝ) (K : List α) (S : Finset (Fin K.length)) :
    ((subCluster K S).map w).prod = ∏ v ∈ S, w (K.get v) := by
  rw [prod_map_eq_prod_fin, ← Finset.prod_coe_sort S (fun v => w (K.get v))]
  refine Fintype.prod_equiv ((finCongr (length_subCluster K S)).trans (S.orderIsoOfFin rfl).toEquiv)
    _ _ fun i => by rw [get_subCluster]; rfl

lemma prod_map_eq_mul_subCluster_compl {α : Type*} (w : α → ℝ) (K : List α) (S : Finset (Fin K.length)) :
    (K.map w).prod = ((subCluster K S).map w).prod * ((subCluster K Sᶜ).map w).prod := by
  rw [prod_map_subCluster_eq, prod_map_subCluster_eq, Finset.prod_mul_prod_compl, prod_map_eq_prod_fin]

lemma prod_map_eq_mul_subClusterLen_compl {α : Type*} {n : ℕ} (w : α → ℝ) (K : List α)
    (hK : K.length = n) (S : Finset (Fin n)) :
    (K.map w).prod = ((subClusterLen K hK S).map w).prod * ((subClusterLen K hK Sᶜ).map w).prod := by
  subst hK; exact prod_map_eq_mul_subCluster_compl w K S

def finSpliceEquiv (α : Type*) {n : ℕ} (S : Finset (Fin n)) :
    (Fin n → α) ≃ (Fin S.card → α) × (Fin Sᶜ.card → α) :=
  let eS : Fin S.card ≃ {v : Fin n // v ∈ S} := (S.orderIsoOfFin rfl).toEquiv
  let eSc : Fin Sᶜ.card ≃ {v : Fin n // v ∉ S} :=
    (Sᶜ.orderIsoOfFin rfl).toEquiv.trans (Equiv.subtypeEquivRight (fun _ => Finset.mem_compl))
  let eSum : Fin S.card ⊕ Fin Sᶜ.card ≃ Fin n :=
    (Equiv.sumCongr eS eSc).trans (Equiv.sumCompl (· ∈ S))
  (Equiv.arrowCongr eSum (Equiv.refl α)).symm.trans
    (Equiv.sumArrowEquivProdArrow (Fin S.card) (Fin Sᶜ.card) α)

@[simp] lemma finSpliceEquiv_fst {α : Type*} {n : ℕ} (S : Finset (Fin n)) (f : Fin n → α) :
    (finSpliceEquiv α S f).1 = fun i : Fin S.card => f (S.orderEmbOfFin rfl i) := rfl

@[simp] lemma finSpliceEquiv_snd {α : Type*} {n : ℕ} (S : Finset (Fin n)) (f : Fin n → α) :
    (finSpliceEquiv α S f).2 = fun j : Fin Sᶜ.card => f (Sᶜ.orderEmbOfFin rfl j) := rfl

def finFnEquivList (α : Type*) (n : ℕ) : (Fin n → α) ≃ {K : List α // K.length = n} where
  toFun f := ⟨List.ofFn f, List.length_ofFn⟩
  invFun K i := K.1.get (i.cast K.2.symm)
  left_inv f := by ext i; simp
  right_inv := by rintro ⟨K, rfl⟩; ext1; exact List.ofFn_get K

def mayerRawTerm {L q_code m_max : ℕ} [NeZero L] (sys : SysCSS[L, q_code, m_max]) (C_RCA : ℝ)
    (w : WorldlineDysonPolymer L q_code → ℝ) (K : WorldlineUrsellCluster L q_code) : ℝ :=
  (∑ G ∈ (clusterIncompatEdges sys C_RCA K).powerset, (-1 : ℝ) ^ G.card) * (K.map w).prod

def ursellRawTerm {L q_code m_max : ℕ} [NeZero L] (sys : SysCSS[L, q_code, m_max]) (C_RCA : ℝ)
    (w : WorldlineDysonPolymer L q_code → ℝ) (K : WorldlineUrsellCluster L q_code) : ℝ :=
  (∑ G ∈ (clusterIncompatEdges sys C_RCA K).powerset.filter
    (fun G => KPIsConnectedSubgraph (PenroseAdj G) Finset.univ), (-1 : ℝ) ^ G.card) * (K.map w).prod

lemma mayerRawTerm_eq_sum_connComp_len {L q_code m_max n : ℕ} [NeZero L]
    (sys : SysCSS[L, q_code, m_max]) (C_RCA : ℝ) (w : WorldlineDysonPolymer L q_code → ℝ)
    (K : WorldlineUrsellCluster L q_code) (hK : K.length = n) (hn : 1 ≤ n) :
    mayerRawTerm sys C_RCA w K =
      ∑ S ∈ (Finset.univ : Finset (Fin n)).powerset.filter (fun S => (⟨0, hn⟩ : Fin n) ∈ S),
        ursellRawTerm sys C_RCA w (subClusterLen K hK S) *
          mayerRawTerm sys C_RCA w (subClusterLen K hK Sᶜ) := by
  unfold mayerRawTerm ursellRawTerm
  rw [mayer_powerset_sum_eq_sum_connComp_len sys C_RCA K hK hn, Finset.sum_mul]
  refine Finset.sum_congr rfl fun S _ => by rw [prod_map_eq_mul_subClusterLen_compl w K hK S]; ring

lemma mayerRawTerm_ofFn_eq_sum_connComp {L q_code m_max n : ℕ} [NeZero L]
    (sys : SysCSS[L, q_code, m_max]) (C_RCA : ℝ) (w : WorldlineDysonPolymer L q_code → ℝ)
    (f : Fin n → WorldlineDysonPolymer L q_code) (hn : 1 ≤ n) :
    mayerRawTerm sys C_RCA w (List.ofFn f) =
      ∑ S ∈ (Finset.univ : Finset (Fin n)).powerset.filter (fun S => (⟨0, hn⟩ : Fin n) ∈ S),
        ursellRawTerm sys C_RCA w (List.ofFn ((finSpliceEquiv _ S f).1)) *
          mayerRawTerm sys C_RCA w (List.ofFn ((finSpliceEquiv _ S f).2)) := by
  rw [mayerRawTerm_eq_sum_connComp_len sys C_RCA w (List.ofFn f) List.length_ofFn hn]
  refine Finset.sum_congr rfl fun S _ => by
    rw [subClusterLen_ofFn, subClusterLen_ofFn, finSpliceEquiv_fst, finSpliceEquiv_snd]

def finSuccEquiv (α : Type*) (n : ℕ) : (Fin (n + 1) → α) ≃ α × (Fin n → α) where
  toFun f := (f 0, Fin.tail f)
  invFun p := Fin.cons p.1 p.2
  left_inv f := Fin.cons_self_tail f
  right_inv p := by rcases p with ⟨x, f⟩; simp

lemma tsum_fin_zero {α : Type*} {β : Type*} [AddCommMonoid β] [TopologicalSpace β]
    (g : (Fin 0 → α) → β) : (∑' f : Fin 0 → α, g f) = g Fin.elim0 := by
  rw [tsum_fintype]
  have h_univ : (Finset.univ : Finset (Fin 0 → α)) = {Fin.elim0} := by
    ext f; simp only [Finset.mem_univ, Finset.mem_singleton, true_iff]; funext i; exact Fin.elim0 i
  rw [h_univ, Finset.sum_singleton]

lemma summable_prod_fin_of_nonneg {α : Type*} {a : α → ℝ}
    (ha : ∀ x, 0 ≤ a x) (ha_sum : Summable a) (n : ℕ) :
    Summable (fun f : Fin n → α => ∏ i : Fin n, a (f i)) := by
  induction' n with n ih
  · exact Summable.of_finite
  · have h_prod : Summable (fun p : α × (Fin n → α) => a p.1 * ∏ i : Fin n, a (p.2 i)) :=
      Summable.mul_of_nonneg ha_sum ih ha (fun _ => Finset.prod_nonneg fun _ _ => ha _)
    refine ((finSuccEquiv α n).summable_iff.mpr h_prod).congr fun f => ?_
    dsimp [finSuccEquiv, Fin.tail]
    exact (Fin.prod_univ_succ (fun i : Fin (n + 1) => a (f i))).symm

lemma norm_powerset_filter_neg_one_pow_le {α : Type*} [Fintype α]
    (E : Finset α) (P : Finset α → Prop) [DecidablePred P] :
    ‖∑ G ∈ E.powerset.filter P, (-1 : ℝ) ^ G.card‖ ≤ (2 ^ Fintype.card α : ℝ) := by
  calc ‖∑ G ∈ E.powerset.filter P, (-1 : ℝ) ^ G.card‖
    _ ≤ ∑ G ∈ E.powerset.filter P, ‖(-1 : ℝ) ^ G.card‖ := norm_sum_le _ _
    _ = ((E.powerset.filter P).card : ℝ) := by simp
    _ ≤ (E.powerset.card : ℝ) := by exact_mod_cast Finset.card_filter_le _ _
    _ = (2 ^ E.card : ℝ) := by rw [Finset.card_powerset, Nat.cast_pow, Nat.cast_ofNat]
    _ ≤ (2 ^ Fintype.card α : ℝ) := by
        exact_mod_cast Nat.pow_le_pow_right (by omega) (Finset.card_le_univ E)

lemma norm_mayerRawTerm_ofFn_le {L q_code m_max n : ℕ} [NeZero L]
    (sys : SysCSS[L, q_code, m_max]) (C_RCA : ℝ) (w : WorldlineDysonPolymer L q_code → ℝ)
    (f : Fin n → WorldlineDysonPolymer L q_code) :
    ‖mayerRawTerm sys C_RCA w (List.ofFn f)‖ ≤ ∏ i : Fin n, ‖w (f i)‖ := by
  unfold mayerRawTerm
  rw [sum_powerset_neg_one_pow_card, norm_mul, List.map_ofFn, List.prod_ofFn, norm_prod]
  split_ifs
  · simp
  · rw [norm_zero, zero_mul]
    exact Finset.prod_nonneg fun _ _ => norm_nonneg _

lemma norm_ursellRawTerm_ofFn_le {L q_code m_max n : ℕ} [NeZero L]
    (sys : SysCSS[L, q_code, m_max]) (C_RCA : ℝ) (w : WorldlineDysonPolymer L q_code → ℝ)
    (f : Fin n → WorldlineDysonPolymer L q_code) :
    ‖ursellRawTerm sys C_RCA w (List.ofFn f)‖ ≤ (2 ^ (n * n) : ℝ) * ∏ i : Fin n, ‖w (f i)‖ := by
  unfold ursellRawTerm; rw [norm_mul, List.map_ofFn, List.prod_ofFn, norm_prod]
  refine mul_le_mul_of_nonneg_right ?_ (Finset.prod_nonneg fun _ _ => norm_nonneg _)
  refine (norm_powerset_filter_neg_one_pow_le _ _).trans ?_; simp [List.length_ofFn]

lemma summable_mayerRawTerm_ofFn {L q_code m_max : ℕ} [NeZero L]
    (sys : SysCSS[L, q_code, m_max]) (C_RCA : ℝ)
    {w : WorldlineDysonPolymer L q_code → ℝ} (hw : Summable (fun γ => ‖w γ‖)) (n : ℕ) :
    Summable (fun f : Fin n → WorldlineDysonPolymer L q_code => ‖mayerRawTerm sys C_RCA w (List.ofFn f)‖) :=
  Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (norm_mayerRawTerm_ofFn_le sys C_RCA w)
    (summable_prod_fin_of_nonneg (fun γ => norm_nonneg (w γ)) hw n)

lemma summable_ursellRawTerm_ofFn {L q_code m_max : ℕ} [NeZero L]
    (sys : SysCSS[L, q_code, m_max]) (C_RCA : ℝ)
    {w : WorldlineDysonPolymer L q_code → ℝ} (hw : Summable (fun γ => ‖w γ‖)) (n : ℕ) :
    Summable (fun f : Fin n → WorldlineDysonPolymer L q_code => ‖ursellRawTerm sys C_RCA w (List.ofFn f)‖) :=
  Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (norm_ursellRawTerm_ofFn_le sys C_RCA w)
    ((summable_prod_fin_of_nonneg (fun γ => norm_nonneg (w γ)) hw n).mul_left (2 ^ (n * n) : ℝ))

def mayerLenSum {L q_code m_max : ℕ} [NeZero L]
    (sys : SysCSS[L, q_code, m_max]) (C_RCA : ℝ) (w : WorldlineDysonPolymer L q_code → ℝ) (n : ℕ) : ℝ :=
  ((n.factorial : ℝ)⁻¹) * ∑' f : Fin n → WorldlineDysonPolymer L q_code, mayerRawTerm sys C_RCA w (List.ofFn f)

def ursellLenSum {L q_code m_max : ℕ} [NeZero L]
    (sys : SysCSS[L, q_code, m_max]) (C_RCA : ℝ) (w : WorldlineDysonPolymer L q_code → ℝ) (m : ℕ) : ℝ :=
  if m = 0 then 0 else
    ((m.factorial : ℝ)⁻¹) * ∑' f : Fin m → WorldlineDysonPolymer L q_code, ursellRawTerm sys C_RCA w (List.ofFn f)

lemma mayerLenSum_zero {L q_code m_max : ℕ} [NeZero L]
    (sys : SysCSS[L, q_code, m_max]) (C_RCA : ℝ) (w : WorldlineDysonPolymer L q_code → ℝ) :
    mayerLenSum sys C_RCA w 0 = 1 := by
  unfold mayerLenSum; rw [Nat.factorial_zero, Nat.cast_one, inv_one, one_mul, tsum_fin_zero]; unfold mayerRawTerm
  have h_emp : clusterIncompatEdges sys C_RCA
      (List.ofFn (Fin.elim0 : Fin 0 → WorldlineDysonPolymer L q_code)) = ∅ := by ext ⟨i, _⟩; exact Fin.elim0 i
  rw [h_emp]; simp

lemma ursellLenSum_zero {L q_code m_max : ℕ} [NeZero L]
    (sys : SysCSS[L, q_code, m_max]) (C_RCA : ℝ) (w : WorldlineDysonPolymer L q_code → ℝ) :
    ursellLenSum sys C_RCA w 0 = 0 := by simp [ursellLenSum]

lemma factorial_mul_mayerLenSum {L q_code m_max : ℕ} [NeZero L]
    (sys : SysCSS[L, q_code, m_max]) (C_RCA : ℝ) (w : WorldlineDysonPolymer L q_code → ℝ) (n : ℕ) :
    (n.factorial : ℝ) * mayerLenSum sys C_RCA w n =
      ∑' f : Fin n → WorldlineDysonPolymer L q_code, mayerRawTerm sys C_RCA w (List.ofFn f) := by
  unfold mayerLenSum; rw [← mul_assoc, mul_inv_cancel₀ (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n)), one_mul]

lemma factorial_mul_ursellLenSum {L q_code m_max : ℕ} [NeZero L]
    (sys : SysCSS[L, q_code, m_max]) (C_RCA : ℝ) (w : WorldlineDysonPolymer L q_code → ℝ) {m : ℕ} (hm : 1 ≤ m) :
    (m.factorial : ℝ) * ursellLenSum sys C_RCA w m =
      ∑' f : Fin m → WorldlineDysonPolymer L q_code, ursellRawTerm sys C_RCA w (List.ofFn f) := by
  unfold ursellLenSum; rw [if_neg (by omega), ← mul_assoc,
    mul_inv_cancel₀ (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero m)), one_mul]

lemma card_powerset_filter_zero_and_card {n : ℕ} (hn : 1 ≤ n) {m : ℕ} (hm : m ∈ Finset.Icc 1 n) :
    (((Finset.univ : Finset (Fin n)).powerset.filter (fun S => (⟨0, hn⟩ : Fin n) ∈ S)).filter
      (fun S => S.card = m)).card = (n - 1).choose (m - 1) := by
  rw [Finset.mem_Icc] at hm; let r₀ : Fin n := ⟨0, hn⟩
  have h_bij : (((Finset.univ : Finset (Fin n)).powerset.filter (fun S => r₀ ∈ S)).filter
      (fun S => S.card = m)).card = ((Finset.univ.erase r₀).powersetCard (m - 1)).card := by
    refine Finset.card_bij' (fun S _ => S.erase r₀) (fun T _ => insert r₀ T) ?_ ?_ ?_ ?_
    · intro S hS; simp only [Finset.mem_filter, Finset.mem_powerset] at hS; rw [Finset.mem_powersetCard]
      exact ⟨Finset.erase_subset_erase r₀ (Finset.subset_univ S), by rw [Finset.card_erase_of_mem hS.1.2, hS.2]⟩
    · intro T hT; rw [Finset.mem_powersetCard] at hT
      have hr₀ : r₀ ∉ T := fun h => Finset.notMem_erase r₀ Finset.univ (hT.1 h)
      simp only [Finset.mem_filter, Finset.mem_powerset]
      exact ⟨⟨Finset.subset_univ _, Finset.mem_insert_self r₀ T⟩, by rw [Finset.card_insert_of_notMem hr₀, hT.2]; omega⟩
    · intro S hS; simp only [Finset.mem_filter] at hS; exact Finset.insert_erase hS.1.2
    · intro T hT; rw [Finset.mem_powersetCard] at hT
      exact Finset.erase_insert (fun h => Finset.notMem_erase r₀ Finset.univ (hT.1 h))
  rw [h_bij, Finset.card_powersetCard, Finset.card_erase_of_mem (Finset.mem_univ r₀), Finset.card_univ, Fintype.card_fin]

lemma choose_pred_mul_factorial_eq {n m : ℕ} (hm : m ∈ Finset.Icc 1 n) :
    ((n - 1).choose (m - 1) : ℝ) * (m.factorial : ℝ) * ((n - m).factorial : ℝ) =
      ((n - 1).factorial : ℝ) * (m : ℝ) := by
  rw [Finset.mem_Icc] at hm
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : m ≠ 0)
  obtain ⟨N, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
  simp only [Nat.succ_sub_succ N k]
  have h_nat : N.choose k * (k + 1).factorial * (N - k).factorial = N.factorial * (k + 1) := by
    rw [Nat.factorial_succ k]
    calc N.choose k * ((k + 1) * k.factorial) * (N - k).factorial
      _ = (N.choose k * k.factorial * (N - k).factorial) * (k + 1) := by ring
      _ = N.factorial * (k + 1) := by rw [Nat.choose_mul_factorial_mul_factorial (by omega : k ≤ N)]
  exact_mod_cast h_nat

lemma mayerLenSum_recurrence {L q_code m_max : ℕ} [NeZero L]
    (sys : SysCSS[L, q_code, m_max]) (C_RCA : ℝ)
    {w : WorldlineDysonPolymer L q_code → ℝ} (hw : Summable (fun γ => ‖w γ‖)) (n : ℕ) (hn : 1 ≤ n) :
    (n : ℝ) * mayerLenSum sys C_RCA w n =
      ∑ m ∈ Finset.Icc 1 n, (m : ℝ) * ursellLenSum sys C_RCA w m * mayerLenSum sys C_RCA w (n - m) := by
  apply mul_left_cancel₀ (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero (n - 1)))
  have h_lhs_fac : ((n - 1).factorial : ℝ) * ((n : ℝ) * mayerLenSum sys C_RCA w n) =
      (n.factorial : ℝ) * mayerLenSum sys C_RCA w n := by
    have h_nf : (n.factorial : ℝ) = (n : ℝ) * ((n - 1).factorial : ℝ) := by
      exact_mod_cast (Nat.mul_factorial_pred (by omega : n ≠ 0)).symm
    rw [h_nf]; ring
  rw [h_lhs_fac, factorial_mul_mayerLenSum]
  let S_zero := (Finset.univ : Finset (Fin n)).powerset.filter (fun S => (⟨0, hn⟩ : Fin n) ∈ S)
  have h_term_sum : ∀ S ∈ S_zero, Summable (fun f : Fin n → WorldlineDysonPolymer L q_code =>
      ursellRawTerm sys C_RCA w (List.ofFn ((finSpliceEquiv _ S f).1)) *
        mayerRawTerm sys C_RCA w (List.ofFn ((finSpliceEquiv _ S f).2))) := fun S _ => by
    have h_prod : Summable (fun p : (Fin S.card → WorldlineDysonPolymer L q_code) ×
        (Fin Sᶜ.card → WorldlineDysonPolymer L q_code) =>
        ‖ursellRawTerm sys C_RCA w (List.ofFn p.1) * mayerRawTerm sys C_RCA w (List.ofFn p.2)‖) := by
      simpa only [norm_mul] using Summable.mul_of_nonneg
        (summable_ursellRawTerm_ofFn sys C_RCA hw S.card) (summable_mayerRawTerm_ofFn sys C_RCA hw Sᶜ.card)
        (fun _ => norm_nonneg _) (fun _ => norm_nonneg _)
    exact (finSpliceEquiv _ S).summable_iff.mpr h_prod.of_norm
  have h_tsum_S : (∑' f : Fin n → WorldlineDysonPolymer L q_code, mayerRawTerm sys C_RCA w (List.ofFn f)) =
      ∑ S ∈ S_zero, ((S.card.factorial : ℝ) * ursellLenSum sys C_RCA w S.card) *
        (((n - S.card).factorial : ℝ) * mayerLenSum sys C_RCA w (n - S.card)) := by
    calc (∑' f : Fin n → WorldlineDysonPolymer L q_code, mayerRawTerm sys C_RCA w (List.ofFn f))
      _ = ∑' f : Fin n → WorldlineDysonPolymer L q_code, ∑ S ∈ S_zero,
            ursellRawTerm sys C_RCA w (List.ofFn ((finSpliceEquiv _ S f).1)) *
              mayerRawTerm sys C_RCA w (List.ofFn ((finSpliceEquiv _ S f).2)) :=
          tsum_congr fun f => mayerRawTerm_ofFn_eq_sum_connComp sys C_RCA w f hn
      _ = ∑ S ∈ S_zero, ∑' f : Fin n → WorldlineDysonPolymer L q_code,
            ursellRawTerm sys C_RCA w (List.ofFn ((finSpliceEquiv _ S f).1)) *
              mayerRawTerm sys C_RCA w (List.ofFn ((finSpliceEquiv _ S f).2)) :=
          Summable.tsum_finsetSum h_term_sum
      _ = ∑ S ∈ S_zero, ((S.card.factorial : ℝ) * ursellLenSum sys C_RCA w S.card) *
            (((n - S.card).factorial : ℝ) * mayerLenSum sys C_RCA w (n - S.card)) := by
          refine Finset.sum_congr rfl fun S hS => ?_
          have hS_pos : 1 ≤ S.card := Finset.card_pos.mpr ⟨⟨0, hn⟩, (Finset.mem_filter.mp hS).2⟩
          have hSc_card : Sᶜ.card = n - S.card := by rw [Finset.card_compl, Fintype.card_fin]
          rw [(finSpliceEquiv (WorldlineDysonPolymer L q_code) S).tsum_eq
            (fun p => ursellRawTerm sys C_RCA w (List.ofFn p.1) * mayerRawTerm sys C_RCA w (List.ofFn p.2)),
            ← tsum_mul_tsum_of_summable_norm (summable_ursellRawTerm_ofFn sys C_RCA hw S.card)
              (summable_mayerRawTerm_ofFn sys C_RCA hw Sᶜ.card),
            ← factorial_mul_ursellLenSum sys C_RCA w hS_pos,
            ← factorial_mul_mayerLenSum sys C_RCA w Sᶜ.card, hSc_card]
  have h_fib : (∑ S ∈ S_zero, ((S.card.factorial : ℝ) * ursellLenSum sys C_RCA w S.card) *
        (((n - S.card).factorial : ℝ) * mayerLenSum sys C_RCA w (n - S.card))) =
      ∑ m ∈ Finset.Icc 1 n, ∑ S ∈ S_zero.filter (fun S => S.card = m),
        ((m.factorial : ℝ) * ursellLenSum sys C_RCA w m) *
        (((n - m).factorial : ℝ) * mayerLenSum sys C_RCA w (n - m)) := by
    rw [← Finset.sum_fiberwise_of_maps_to (t := Finset.Icc 1 n) (g := Finset.card)]
    · exact Finset.sum_congr rfl fun m _ => Finset.sum_congr rfl fun S hS => by rw [(Finset.mem_filter.mp hS).2]
    · exact fun S hS => Finset.mem_Icc.mpr ⟨Finset.card_pos.mpr ⟨⟨0, hn⟩, (Finset.mem_filter.mp hS).2⟩,
        (Finset.card_le_univ S).trans (by simp)⟩
  rw [h_tsum_S, h_fib, Finset.mul_sum]
  refine Finset.sum_congr rfl fun m hm => ?_
  rw [Finset.sum_const, nsmul_eq_mul, card_powerset_filter_zero_and_card hn hm]
  calc ((n - 1).choose (m - 1) : ℝ) * (((m.factorial : ℝ) * ursellLenSum sys C_RCA w m) *
        (((n - m).factorial : ℝ) * mayerLenSum sys C_RCA w (n - m)))
      = (((n - 1).choose (m - 1) : ℝ) * (m.factorial : ℝ) * ((n - m).factorial : ℝ)) *
          (ursellLenSum sys C_RCA w m * mayerLenSum sys C_RCA w (n - m)) := by ring
    _ = (((n - 1).factorial : ℝ) * (m : ℝ)) *
          (ursellLenSum sys C_RCA w m * mayerLenSum sys C_RCA w (n - m)) := by rw [choose_pred_mul_factorial_eq hm]
    _ = ((n - 1).factorial : ℝ) * ((m : ℝ) * ursellLenSum sys C_RCA w m * mayerLenSum sys C_RCA w (n - m)) := by ring

def sigmaFinFnEquivList (α : Type*) : (Σ n : ℕ, Fin n → α) ≃ List α :=
  (Equiv.sigmaCongrRight (finFnEquivList α)).trans (Equiv.sigmaFiberEquiv List.length)

@[simp] lemma sigmaFinFnEquivList_apply {α : Type*} (p : Σ n : ℕ, Fin n → α) :
    sigmaFinFnEquivList α p = List.ofFn p.2 := rfl

def validPolymerWeight {L q_code r_0 m_max : ℕ} [NeZero L]
    (D_field : Box3D L → LocalCSSDescriptor q_code r_0 m_max)
    (sys : SysCSS[L, q_code, m_max]) (C_RCA : ℝ) (R_cut : ℕ) (β : ℝ)
    (V : QuasiLocalPerturbation 3 L (SiteCSS[L, q_code]))
    (d_loc : ℕ → Finset (Box3D L) → (IdxCSS[L, q_code, m_max] → Bool) → ℝ)
    (ν : PauliBitstringPair L q_code) (σ : IdxCSS[L, q_code, m_max] → Bool)
    (γ : WorldlineDysonPolymer L q_code) : ℝ :=
  if IsValidWorldlinePolymer D_field sys C_RCA R_cut γ then
    worldlinePolymerWeight D_field sys C_RCA β V d_loc ν γ σ else 0

lemma prod_map_validPolymerWeight_eq_ite {L q_code r_0 m_max R_cut : ℕ} [NeZero L]
    (D_field : Box3D L → LocalCSSDescriptor q_code r_0 m_max)
    (sys : SysCSS[L, q_code, m_max]) (C_RCA β : ℝ)
    (V : QuasiLocalPerturbation 3 L (SiteCSS[L, q_code]))
    (d_loc : ℕ → Finset (Box3D L) → (IdxCSS[L, q_code, m_max] → Bool) → ℝ)
    (ν : PauliBitstringPair L q_code) (σ : IdxCSS[L, q_code, m_max] → Bool)
    (K : WorldlineUrsellCluster L q_code) :
    (K.map (validPolymerWeight D_field sys C_RCA R_cut β V d_loc ν σ)).prod =
      if ∀ γ ∈ K, IsValidWorldlinePolymer D_field sys C_RCA R_cut γ then
        (K.map (fun γ => worldlinePolymerWeight D_field sys C_RCA β V d_loc ν γ σ)).prod else 0 := by
  by_cases hK : ∀ γ ∈ K, IsValidWorldlinePolymer D_field sys C_RCA R_cut γ
  · rw [if_pos hK]; congr 1; exact List.map_congr_left fun γ hγ => by simp [validPolymerWeight, hK γ hγ]
  · rw [if_neg hK]; push_neg at hK; rcases hK with ⟨γ, hγK, hγ_inv⟩
    exact List.prod_eq_zero (List.mem_map.mpr ⟨γ, hγK, by simp [validPolymerWeight, hγ_inv]⟩)

lemma worldlineMayerPolymerClusterWeight_eq_mayerRawTerm {L q_code r_0 m_max R_cut : ℕ} [NeZero L]
    (D_field : Box3D L → LocalCSSDescriptor q_code r_0 m_max)
    (sys : SysCSS[L, q_code, m_max]) (C_RCA β : ℝ)
    (V : QuasiLocalPerturbation 3 L (SiteCSS[L, q_code]))
    (d_loc : ℕ → Finset (Box3D L) → (IdxCSS[L, q_code, m_max] → Bool) → ℝ)
    (ν : PauliBitstringPair L q_code) (σ : IdxCSS[L, q_code, m_max] → Bool)
    (K : WorldlineUrsellCluster L q_code) :
    worldlineMayerPolymerClusterWeight D_field sys C_RCA R_cut β V d_loc ν σ K =
      ((K.length.factorial : ℝ)⁻¹) *
        mayerRawTerm sys C_RCA (validPolymerWeight D_field sys C_RCA R_cut β V d_loc ν σ) K := by
  rw [worldlineMayerPolymerClusterWeight_eq_powerset_sum]
  unfold mayerRawTerm clusterIncompatEdges; rw [prod_map_validPolymerWeight_eq_ite]; split_ifs <;> ring

lemma valid_worldlineClusterUrsellWeight_eq_ursellRawTerm {L q_code r_0 m_max R_cut : ℕ} [NeZero L]
    (D_field : Box3D L → LocalCSSDescriptor q_code r_0 m_max)
    (sys : SysCSS[L, q_code, m_max]) (C_RCA β : ℝ)
    (V : QuasiLocalPerturbation 3 L (SiteCSS[L, q_code]))
    (d_loc : ℕ → Finset (Box3D L) → (IdxCSS[L, q_code, m_max] → Bool) → ℝ)
    (ν : PauliBitstringPair L q_code) (σ : IdxCSS[L, q_code, m_max] → Bool)
    (K : WorldlineUrsellCluster L q_code) :
    (if IsValidWorldlineUrsellCluster D_field sys C_RCA R_cut K then
      worldlineClusterUrsellWeight D_field sys C_RCA β V d_loc ν K σ else 0) =
      if K = [] then 0 else
        ((K.length.factorial : ℝ)⁻¹) *
          ursellRawTerm sys C_RCA (validPolymerWeight D_field sys C_RCA R_cut β V d_loc ν σ) K := by
  rw [(ursellConnectedGraphCoeff_eq_zero_of_not_connected_and_valid_ite_eq D_field sys C_RCA β V d_loc ν σ K).2]
  unfold worldlineClusterUrsellWeight ursellConnectedGraphCoeff ursellRawTerm clusterIncompatEdges PenroseAdj
  rw [prod_map_validPolymerWeight_eq_ite]
  by_cases hK : K = []
  · simp [hK]
  · by_cases hval : ∀ γ ∈ K, IsValidWorldlinePolymer D_field sys C_RCA R_cut γ
    · rw [if_pos ⟨hK, hval⟩, if_neg hK, if_pos hval]; ring
    · rw [if_neg (not_and_of_not_right _ hval), if_neg hK, if_neg hval, mul_zero, mul_zero]

lemma summable_sigma_tsum_of_nonneg {α : Type*} {β : α → Type*} {g : (Σ a, β a) → ℝ}
    (h_sum : Summable g) (hg : ∀ p, 0 ≤ g p) :
    Summable (fun a => ∑' b, g ⟨a, b⟩) := by
  refine summable_of_sum_le (c := ∑' p, g p) (fun a => tsum_nonneg (fun b => hg ⟨a, b⟩)) fun s => ?_
  have h_row : ∀ a, Summable (fun b => g ⟨a, b⟩) := fun a => h_sum.comp_injective sigma_mk_injective
  rw [← (s.tsum_subtype (fun a => ∑' b, g ⟨a, b⟩))]
  have h_inj : Function.Injective (fun p : (Σ a : s, β a.1) => (⟨p.1.1, p.2⟩ : Σ a, β a)) := by
    rintro ⟨⟨a₁, ha₁⟩, b₁⟩ ⟨⟨a₂, ha₂⟩, b₂⟩ h; cases h; rfl
  have h_sub_sum : Summable (fun p : Σ a : s, β a.1 => g ⟨p.1.1, p.2⟩) := h_sum.comp_injective h_inj
  rw [← Summable.tsum_sigma' (fun a : s => h_row a.1) h_sub_sum]
  refine le_of_tendsto' h_sub_sum.hasSum fun t => ?_
  have h_map : (∑ b ∈ t, g ⟨b.1.1, b.2⟩) = ∑ p ∈ t.map ⟨fun p => ⟨p.1.1, p.2⟩, h_inj⟩, g p :=
    (Finset.sum_map t ⟨fun p => ⟨p.1.1, p.2⟩, h_inj⟩ g).symm
  rw [h_map]
  exact h_sum.sum_le_tsum _ fun q _ => hg q

lemma summable_sigma_of_nonneg {α : Type*} {β : α → Type*} {g : ∀ a, β a → ℝ}
    (h_row : ∀ a, Summable (g a)) (h_col : Summable (fun a => ∑' b, g a b))
    (hg : ∀ a b, 0 ≤ g a b) : Summable (fun p : Σ a, β a => g p.1 p.2) := by
  refine summable_of_sum_le (c := ∑' a, ∑' b, g a b) (fun p => hg p.1 p.2) fun s => ?_
  classical
  calc (∑ p ∈ s, g p.1 p.2)
    _ ≤ ∑ a ∈ s.image Sigma.fst, ∑' b, g a b := by
        rw [← Finset.sum_fiberwise_of_maps_to (fun p hp => Finset.mem_image_of_mem Sigma.fst hp)]
        refine Finset.sum_le_sum fun a _ => ?_
        rw [← Finset.sum_attach (s.filter (fun p => p.1 = a))]
        let emb : {p // p ∈ s.filter (fun p => p.1 = a)} ↪ β a :=
          ⟨fun p => (Finset.mem_filter.mp p.2).2 ▸ p.1.2, by
            rintro ⟨⟨a₁, b₁⟩, hp₁⟩ ⟨⟨a₂, b₂⟩, hp₂⟩ h_eq
            have ha₁ : a₁ = a := (Finset.mem_filter.mp hp₁).2
            have ha₂ : a₂ = a := (Finset.mem_filter.mp hp₂).2
            subst ha₁ ha₂; (try dsimp at h_eq); subst h_eq; rfl⟩
        have h_map : (∑ p ∈ (s.filter (fun p => p.1 = a)).attach, g p.1.1 p.1.2) =
            ∑ b ∈ (s.filter (fun p => p.1 = a)).attach.map emb, g a b := by
          rw [Finset.sum_map]; refine Finset.sum_congr rfl fun ⟨⟨a', b⟩, hp⟩ _ => ?_
          have ha' : a' = a := (Finset.mem_filter.mp hp).2; subst ha'; rfl
        rw [h_map]; exact (h_row a).sum_le_tsum _ fun b _ => hg a b
    _ ≤ ∑' a, ∑' b, g a b := h_col.sum_le_tsum _ fun a _ => tsum_nonneg fun b => hg a b

lemma tsum_prod_fin_eq_pow_tsum {α : Type*} {w : α → ℝ} (hw_nn : ∀ x, 0 ≤ w x) (hw : Summable w)
    (n : ℕ) : (∑' f : Fin n → α, ∏ i : Fin n, w (f i)) = (∑' x, w x) ^ n := by
  induction' n with n ih
  · rw [tsum_fin_zero]; simp
  · rw [pow_succ']
    have h_eq := (finSuccEquiv α n).tsum_eq (fun p => w p.1 * ∏ i : Fin n, w (p.2 i))
    have h_congr : (∑' f : Fin (n + 1) → α, ∏ i : Fin (n + 1), w (f i)) =
        ∑' f : Fin (n + 1) → α, (w (finSuccEquiv α n f).1 * ∏ i : Fin n, w ((finSuccEquiv α n f).2 i)) :=
      tsum_congr fun f => Fin.prod_univ_succ (fun i : Fin (n + 1) => w (f i))
    have h1 : Summable (fun x => ‖w x‖) := hw.congr fun x => (Real.norm_of_nonneg (hw_nn x)).symm
    have h2 : Summable (fun f : Fin n → α => ‖∏ i : Fin n, w (f i)‖) :=
      (summable_prod_fin_of_nonneg hw_nn hw n).congr fun f =>
        (Real.norm_of_nonneg (Finset.prod_nonneg fun _ _ => hw_nn _)).symm
    rw [h_congr, h_eq, (tsum_mul_tsum_of_summable_norm h1 h2).symm, ih]

lemma tsum_mayer_eq_exp_tsum_ursell {L q_code m_max : ℕ} [NeZero L]
    (sys : SysCSS[L, q_code, m_max]) (C_RCA : ℝ) (w : WorldlineDysonPolymer L q_code → ℝ)
    (F_U F_Z : WorldlineUrsellCluster L q_code → ℝ) (hw : Summable (fun γ => ‖w γ‖))
    (hFU_norm : Summable (fun K => ‖F_U K‖))
    (hFU_eq : ∀ K, F_U K = if K = [] then 0 else ((K.length.factorial : ℝ)⁻¹) * ursellRawTerm sys C_RCA w K)
    (hFZ_eq : ∀ K, F_Z K = ((K.length.factorial : ℝ)⁻¹) * mayerRawTerm sys C_RCA w K) :
    (∑' K, F_Z K) = Real.exp (∑' K, F_U K) := by
  have hFU_sig_norm : Summable (fun p : Σ m : ℕ, Fin m → WorldlineDysonPolymer L q_code =>
      ‖F_U (List.ofFn p.2)‖) :=
    (sigmaFinFnEquivList (WorldlineDysonPolymer L q_code)).summable_iff.mpr hFU_norm
  have hFU_row_norm : ∀ m : ℕ, Summable (fun f : Fin m → WorldlineDysonPolymer L q_code => ‖F_U (List.ofFn f)‖) :=
    fun m => hFU_sig_norm.comp_injective sigma_mk_injective
  have hFU_ofFn : ∀ (m : ℕ) (f : Fin m → WorldlineDysonPolymer L q_code),
      F_U (List.ofFn f) = if m = 0 then 0 else ((m.factorial : ℝ)⁻¹) * ursellRawTerm sys C_RCA w (List.ofFn f) := by
    intro m f; rw [hFU_eq (List.ofFn f)]
    have h_nil : (List.ofFn f = []) ↔ m = 0 := by rw [← List.length_eq_zero_iff, List.length_ofFn]
    by_cases hm : m = 0
    · rw [if_pos (h_nil.mpr hm), if_pos hm]
    · rw [if_neg (mt h_nil.mp hm), if_neg hm, List.length_ofFn]
  have h_ursellLenSum_eq : ∀ m : ℕ,
      ursellLenSum sys C_RCA w m = ∑' f : Fin m → WorldlineDysonPolymer L q_code, F_U (List.ofFn f) := by
    intro m; by_cases hm : m = 0
    · subst hm; rw [ursellLenSum_zero, tsum_fin_zero, hFU_ofFn 0 Fin.elim0, if_pos rfl]
    · unfold ursellLenSum; rw [if_neg hm, ← tsum_mul_left]
      exact tsum_congr fun f => by rw [hFU_ofFn m f, if_neg hm]
  have hU_abs : Summable (fun m => ‖ursellLenSum sys C_RCA w m‖) := by
    have h_col_u := summable_sigma_tsum_of_nonneg hFU_sig_norm (fun _ => norm_nonneg _)
    refine h_col_u.of_nonneg_of_le (fun m => norm_nonneg (ursellLenSum sys C_RCA w m)) (fun m => ?_)
    rw [h_ursellLenSum_eq m]
    exact norm_tsum_le_tsum_norm (f := fun f : Fin m → WorldlineDysonPolymer L q_code => F_U (List.ofFn f))
      (hFU_row_norm m)
  have hU_tsum : (∑' m, ursellLenSum sys C_RCA w m) = ∑' K, F_U K := by
    have h_eq_U := (sigmaFinFnEquivList (WorldlineDysonPolymer L q_code)).tsum_eq F_U
    dsimp only [sigmaFinFnEquivList_apply] at h_eq_U
    rw [← h_eq_U, Summable.tsum_sigma' (fun m => (hFU_row_norm m).of_norm) hFU_sig_norm.of_norm]
    exact tsum_congr h_ursellLenSum_eq
  have h_rec := summable_and_tsum_eq_exp_of_recurrence
    (ursellLenSum_zero sys C_RCA w) (mayerLenSum_zero sys C_RCA w) hU_abs (mayerLenSum_recurrence sys C_RCA hw)
  rw [← hU_tsum, ← h_rec.2]
  have hFZ_ofFn : ∀ (n : ℕ) (f : Fin n → WorldlineDysonPolymer L q_code),
      F_Z (List.ofFn f) = ((n.factorial : ℝ)⁻¹) * mayerRawTerm sys C_RCA w (List.ofFn f) :=
    fun n f => by rw [hFZ_eq (List.ofFn f), List.length_ofFn]
  have hFZ_sig_norm : Summable (fun p : Σ n : ℕ, Fin n → WorldlineDysonPolymer L q_code =>
      ‖F_Z (List.ofFn p.2)‖) := by
    have h_row : ∀ n : ℕ, Summable (fun f : Fin n → WorldlineDysonPolymer L q_code =>
        ((n.factorial : ℝ)⁻¹) * ∏ i : Fin n, ‖w (f i)‖) :=
      fun n => (summable_prod_fin_of_nonneg (fun γ => norm_nonneg (w γ)) hw n).mul_left _
    have h_col : Summable (fun n : ℕ => ∑' f : Fin n → WorldlineDysonPolymer L q_code,
        ((n.factorial : ℝ)⁻¹) * ∏ i : Fin n, ‖w (f i)‖) :=
      (Real.summable_pow_div_factorial (∑' γ, ‖w γ‖)).congr fun n => by
        rw [tsum_mul_left, tsum_prod_fin_eq_pow_tsum (fun γ => norm_nonneg (w γ)) hw n, div_eq_inv_mul]
    have h_prod_sig := summable_sigma_of_nonneg h_row h_col
      (fun _ _ => mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg _)) (Finset.prod_nonneg fun _ _ => norm_nonneg _))
    refine h_prod_sig.of_nonneg_of_le (fun p => norm_nonneg (F_Z (List.ofFn p.2))) (fun ⟨n, f⟩ => ?_)
    rw [hFZ_ofFn n f, norm_mul, Real.norm_of_nonneg (inv_nonneg.mpr (Nat.cast_nonneg _))]
    exact mul_le_mul_of_nonneg_left (norm_mayerRawTerm_ofFn_le sys C_RCA w f) (inv_nonneg.mpr (Nat.cast_nonneg _))
  have hFZ_row_norm : ∀ n : ℕ, Summable (fun f : Fin n → WorldlineDysonPolymer L q_code => ‖F_Z (List.ofFn f)‖) :=
    fun n => hFZ_sig_norm.comp_injective sigma_mk_injective
  have h_eq_Z := (sigmaFinFnEquivList (WorldlineDysonPolymer L q_code)).tsum_eq F_Z
  dsimp only [sigmaFinFnEquivList_apply] at h_eq_Z
  rw [← h_eq_Z, Summable.tsum_sigma' (fun n => (hFZ_row_norm n).of_norm) hFZ_sig_norm.of_norm]
  exact tsum_congr fun n => by unfold mayerLenSum; rw [← tsum_mul_left]; exact tsum_congr fun f => hFZ_ofFn n f

lemma worldlineMayerPolymerPartition_eq_exp_of_summable {L q_code r_0 m_max R_cut : ℕ} [NeZero L]
    (D_field : Box3D L → LocalCSSDescriptor q_code r_0 m_max) (sys : SysCSS[L, q_code, m_max]) (C_RCA β : ℝ)
    (V : QuasiLocalPerturbation 3 L (SiteCSS[L, q_code]))
    (d_loc : ℕ → Finset (Box3D L) → (IdxCSS[L, q_code, m_max] → Bool) → ℝ)
    (ν : PauliBitstringPair L q_code) (σ : IdxCSS[L, q_code, m_max] → Bool)
    (h_poly_sum : Summable (fun γ : WorldlineDysonPolymer L q_code =>
      if IsValidWorldlinePolymer D_field sys C_RCA R_cut γ then
        |worldlinePolymerWeight D_field sys C_RCA β V d_loc ν γ σ| else 0))
    (h_ursell_sum : Summable (fun K : WorldlineUrsellCluster L q_code =>
      if IsValidWorldlineUrsellCluster D_field sys C_RCA R_cut K then
        |worldlineClusterUrsellWeight D_field sys C_RCA β V d_loc ν K σ| else 0)) :
    worldlineMayerPolymerPartition D_field sys C_RCA R_cut β V d_loc ν σ =
      Real.exp (∑ γ ∈ worldlineUrsellIndexFinset L q_code m_max R_cut,
        worldlineUrsellPhi D_field sys C_RCA R_cut β V d_loc ν γ σ) := by
  have hw : Summable (fun γ => ‖validPolymerWeight D_field sys C_RCA R_cut β V d_loc ν σ γ‖) :=
    h_poly_sum.congr fun γ => by dsimp [validPolymerWeight]; split_ifs <;> simp
  have hFU_norm : Summable (fun K : WorldlineUrsellCluster L q_code =>
      ‖if IsValidWorldlineUrsellCluster D_field sys C_RCA R_cut K then
        worldlineClusterUrsellWeight D_field sys C_RCA β V d_loc ν K σ else 0‖) :=
    h_ursell_sum.congr fun K => by split_ifs <;> simp
  rw [sum_worldlineUrsellIndexFinset_worldlineUrsellPhi_eq_tsum_of_summable D_field sys C_RCA β V d_loc ν σ h_ursell_sum]
  exact tsum_mayer_eq_exp_tsum_ursell sys C_RCA
    (validPolymerWeight D_field sys C_RCA R_cut β V d_loc ν σ)
    (fun K => if IsValidWorldlineUrsellCluster D_field sys C_RCA R_cut K then
      worldlineClusterUrsellWeight D_field sys C_RCA β V d_loc ν K σ else 0)
    (worldlineMayerPolymerClusterWeight D_field sys C_RCA R_cut β V d_loc ν σ) hw hFU_norm
    (valid_worldlineClusterUrsellWeight_eq_ursellRawTerm D_field sys C_RCA β V d_loc ν σ)
    (worldlineMayerPolymerClusterWeight_eq_mayerRawTerm D_field sys C_RCA β V d_loc ν σ)

private lemma single_scale_worldlineSpanningThreshold_bound
    {R_cut : ℕ} {Δ_RCA C_wl c_wl β J : ℝ} {f : ℕ → ℝ}
    (hf_nn : ∀ r, 0 ≤ f r) (hc_wl : 0 ≤ c_wl) (hβ : 0 ≤ β) (hJ : 0 ≤ J)
    (h_sum_pos : 0 < worldlineNativeKPSum f C_wl c_wl β R_cut)
    (h_thresh : J ≤ worldlineSpanningThreshold Δ_RCA C_wl c_wl β f R_cut)
    {r : ℕ} (hr : r ∈ Finset.Icc 1 R_cut) :
    64 * Real.exp 1 * C_wl * ((r : ℝ) ^ 6) * (β * J * f r) *
      Real.exp (c_wl * (1 + β) * ((r : ℝ) ^ 3)) ≤ 1 := by
  let term : ℕ → ℝ := fun s => C_wl * ((s : ℝ) ^ 6) * f s * Real.exp (c_wl * (1 + β) * ((s : ℝ) ^ 3))
  have hC : 0 ≤ C_wl := by
    by_contra h_neg; push_neg at h_neg
    have h_sum_le : worldlineNativeKPSum f C_wl c_wl β R_cut ≤ 0 := by
      unfold worldlineNativeKPSum; refine Finset.sum_nonpos fun s' _ => ?_
      have hs' := hf_nn s'
      have h1 : 0 ≤ ((s' : ℝ) ^ 6) * f s' * Real.exp (c_wl * (1 + β) * ((s' : ℝ) ^ 3)) := by positivity
      nlinarith
    linarith
  have h_term_nn : ∀ s, 0 ≤ term s := fun s => by dsimp [term]; have := hf_nn s; positivity
  have h_term_le_sum : term r ≤ worldlineNativeKPSum f C_wl c_wl β R_cut :=
    Finset.single_le_sum (f := term) (fun s _ => h_term_nn s) hr
  let D := 64 * Real.exp 1 * max 1 β * worldlineNativeKPSum f C_wl c_wl β R_cut
  have h_max_pos : 0 < max 1 β := lt_of_lt_of_le zero_lt_one (le_max_left 1 β)
  have hD_pos : 0 < D := by dsimp [D]; positivity
  have h_num_le_D : 64 * Real.exp 1 * β * term r ≤ D :=
    mul_le_mul (mul_le_mul_of_nonneg_left (le_max_right 1 β) (by positivity)) h_term_le_sum (h_term_nn r) (by positivity)
  calc 64 * Real.exp 1 * C_wl * ((r : ℝ) ^ 6) * (β * J * f r) * Real.exp (c_wl * (1 + β) * ((r : ℝ) ^ 3))
    _ = J * (64 * Real.exp 1 * β * term r) := by dsimp [term]; ring
    _ ≤ J * D := mul_le_mul_of_nonneg_left h_num_le_D hJ
    _ ≤ (1 / D) * D := mul_le_mul_of_nonneg_right (le_trans h_thresh (min_le_right _ _)) (le_of_lt hD_pos)
    _ = 1 := one_div_mul_cancel (ne_of_gt hD_pos)

private lemma kpMonomerWeight_bounds_local
    {L r_0 w_0 R_cut : ℕ} {C_RCA Δ_RCA C_wl c_wl β J : ℝ} {f : ℕ → ℝ}
    (hR_cut : 1 ≤ R_cut) (hf_nn : ∀ r, 0 ≤ f r)
    (hC_wl_cal : (kpCollarMaxCheckCard R_cut r_0 w_0 C_RCA : ℝ) ≤ C_wl)
    (hc_wl_cal : (kpCollarMaxCheckCard R_cut r_0 w_0 C_RCA : ℝ) ≤ c_wl)
    (hβ : 16 < β) (hJ : 0 ≤ J)
    (h_sum_pos : 0 < worldlineNativeKPSum f C_wl c_wl β R_cut)
    (h_thresh : J ≤ worldlineSpanningThreshold Δ_RCA C_wl c_wl β f R_cut)
    {p : ℕ × Finset (Box3D L)} (hp : p ∈ worldlineScaleCubeFinset L R_cut) :
    let Δ_V := (kpCollarMaxCheckCard R_cut r_0 w_0 C_RCA : ℝ)
    0 ≤ kpMonomerWeight c_wl β J f p ∧
    4 * Real.exp 1 * Real.exp ((1 / 8 : ℝ) * Δ_V) * kpMonomerWeight c_wl β J f p ≤
      (1 / 64 : ℝ) * Real.exp (-12 * Δ_V) ∧
    kpMonomerWeight c_wl β J f p ≤ 1 ∧
    4 * β * J * f p.1 * Real.exp (4 * β * J * f p.1) ≤ kpMonomerWeight c_wl β J f p := by
  rcases mem_kpScaleCubeFinset_iff.mp hp with ⟨hp_r, _⟩
  exact kpMonomerWeight_bounds hR_cut hf_nn hC_wl_cal hc_wl_cal hβ hJ hp
    (single_scale_worldlineSpanningThreshold_bound hf_nn (le_trans (Nat.cast_nonneg _) hc_wl_cal)
      (by linarith) hJ h_sum_pos h_thresh
      (Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp hp_r).1, le_trans (Finset.mem_Icc.mp hp_r).2 (Nat.min_le_left R_cut L)⟩))

private lemma exp_eighth_worldlinePolymerNativeCollar_le
    {L q_code r_0 m_max w_0 R_cut : ℕ} [NeZero L] {C_RCA : ℝ} (hC_RCA : 0 ≤ C_RCA)
    (D_field : Box3D L → LocalCSSDescriptor q_code r_0 m_max) (sys : SysCSS[L, q_code, m_max])
    (h_sys_checks : ∀ idx, sys.checkProj idx = staticCSSCheckProj D_field idx ∧
      sys.support idx = staticCSSCheckSupport D_field idx ∧ sys.weight idx = 1)
    (h_geom : sys.IsGeometricallyLocal r_0 w_0)
    {M : Finset (ℕ × Finset (Box3D L))} (hM_sub : M ⊆ worldlineScaleCubeFinset L R_cut)
    {γ : WorldlineDysonPolymer L q_code} (hγ_M : worldlinePolymerMonomers γ = M) :
    Real.exp ((1 / 8 : ℝ) * ((worldlinePolymerNativeCollar sys C_RCA γ).card : ℝ)) ≤
      (Real.exp ((1 / 8 : ℝ) * (kpCollarMaxCheckCard R_cut r_0 w_0 C_RCA : ℝ))) ^ M.card := by
  have h_card : (worldlinePolymerNativeCollar sys C_RCA γ).card ≤
      M.card * kpCollarMaxCheckCard R_cut r_0 w_0 C_RCA := by
    unfold worldlinePolymerNativeCollar nativeCollarSupport; rw [hγ_M]
    calc (M.biUnion (fun p => rcaCollarChecks sys C_RCA p.1 p.2)).card
      _ ≤ ∑ p ∈ M, (rcaCollarChecks sys C_RCA p.1 p.2).card := Finset.card_biUnion_le
      _ ≤ M.card • kpCollarMaxCheckCard R_cut r_0 w_0 C_RCA :=
          Finset.sum_le_card_nsmul M _ _ fun p hp =>
            card_kpRCACollarChecks_le D_field sys h_sys_checks h_geom hC_RCA
              (mem_kpScaleCubeFinset_iff.mp (hM_sub hp)).1 p.2
      _ = M.card * kpCollarMaxCheckCard R_cut r_0 w_0 C_RCA := smul_eq_mul _ _
  rw [← Real.exp_nat_mul]; refine Real.exp_le_exp.mpr ?_
  have h_cast : ((worldlinePolymerNativeCollar sys C_RCA γ).card : ℝ) ≤
      (M.card : ℝ) * (kpCollarMaxCheckCard R_cut r_0 w_0 C_RCA : ℝ) := by exact_mod_cast h_card
  linarith

private lemma sum_validPolymers_with_monomers_le
    {L q_code r_0 m_max w_0 R_cut : ℕ} [NeZero L]
    {C_RCA β Δ_RCA C_wl c_wl J : ℝ} {f : ℕ → ℝ}
    (hR_cut : 1 ≤ R_cut) (hC_RCA : 0 ≤ C_RCA)
    (hC_wl_cal : (kpCollarMaxCheckCard R_cut r_0 w_0 C_RCA : ℝ) ≤ C_wl)
    (hc_wl_cal : (kpCollarMaxCheckCard R_cut r_0 w_0 C_RCA : ℝ) ≤ c_wl)
    (hβ : 16 < β) (hJ : 0 ≤ J) (hf_nn : ∀ r, 0 ≤ f r)
    (h_sum_pos : 0 < worldlineNativeKPSum f C_wl c_wl β R_cut)
    (h_thresh : J ≤ worldlineSpanningThreshold Δ_RCA C_wl c_wl β f R_cut)
    (D_field : Box3D L → LocalCSSDescriptor q_code r_0 m_max)
    (sys : SysCSS[L, q_code, m_max])
    (h_sys_checks : ∀ idx, sys.checkProj idx = staticCSSCheckProj D_field idx ∧
      sys.support idx = staticCSSCheckSupport D_field idx ∧ sys.weight idx = 1)
    (h_geom : sys.IsGeometricallyLocal r_0 w_0)
    (V : QuasiLocalPerturbation 3 L (SiteCSS[L, q_code]))
    (hV_norm : ∀ r ∈ Finset.Icc 1 (min R_cut L), ∀ A ∈ boxCubes 3 L r, ‖V.term r A‖ ≤ J * f r)
    (d_loc : ℕ → Finset (Box3D L) → (IdxCSS[L, q_code, m_max] → Bool) → ℝ)
    (hd_scale : ∀ r ∈ Finset.Icc 1 (min R_cut L), ∀ A ∈ boxCubes 3 L r,
      ∀ σ, |d_loc r A σ| ≤ 2 * (J * f r))
    (ν : PauliBitstringPair L q_code)
    (σ : IdxCSS[L, q_code, m_max] → Bool)
    (ℱ : Finset (WorldlineDysonPolymer L q_code))
    {M : Finset (ℕ × Finset (Box3D L))} (hM_sub : M ⊆ worldlineScaleCubeFinset L R_cut) :
    (∑ γ ∈ ℱ.filter (fun γ => IsValidWorldlinePolymer D_field sys C_RCA R_cut γ ∧
        worldlinePolymerMonomers γ = M),
      |worldlinePolymerWeight D_field sys C_RCA β V d_loc ν γ σ| *
        Real.exp ((1 / 8 : ℝ) * ((worldlinePolymerNativeCollar sys C_RCA γ).card : ℝ))) ≤
      ((1 / 64 : ℝ) *
        Real.exp (-12 * (kpCollarMaxCheckCard R_cut r_0 w_0 C_RCA : ℝ))) ^ M.card := by
  have hβ_nn : 0 ≤ β := by linarith
  let Δ_V : ℕ := kpCollarMaxCheckCard R_cut r_0 w_0 C_RCA
  let C_col : ℝ := Real.exp ((1 / 8 : ℝ) * (Δ_V : ℝ))
  have h_bounds : ∀ {p}, p ∈ M →
      0 ≤ kpMonomerWeight c_wl β J f p ∧
      4 * Real.exp 1 * C_col * kpMonomerWeight c_wl β J f p ≤
        (1 / 64 : ℝ) * Real.exp (-12 * (Δ_V : ℝ)) ∧
      kpMonomerWeight c_wl β J f p ≤ 1 ∧
      4 * β * J * f p.1 * Real.exp (4 * β * J * f p.1) ≤ kpMonomerWeight c_wl β J f p :=
    fun {p} hp => kpMonomerWeight_bounds_local hR_cut hf_nn hC_wl_cal hc_wl_cal hβ hJ
      h_sum_pos h_thresh (hM_sub hp)
  let w_J (p : ℕ × Finset (Box3D L)) : ℝ :=
    2 * β * J * f p.1 * Real.exp ((1 / 27 : ℝ) * c_wl * β * ((p.1 : ℝ) ^ 3))
  let w_D (p : ℕ × Finset (Box3D L)) : ℝ :=
    4 * β * J * f p.1 * Real.exp (4 * β * J * f p.1)
  let ℱ_M := ℱ.filter (fun γ => IsValidWorldlinePolymer D_field sys C_RCA R_cut γ ∧
    worldlinePolymerMonomers γ = M)
  let F_raw (γ : WorldlineDysonPolymer L q_code) : ℝ :=
    ((γ.1.length.factorial : ℝ)⁻¹) * (γ.1.map (fun ξ => w_J ξ.1)).prod * ∏ ϑ ∈ γ.2, w_D ϑ
  have h_pt : ∀ γ ∈ ℱ_M,
      |worldlinePolymerWeight D_field sys C_RCA β V d_loc ν γ σ| *
        Real.exp ((1 / 8 : ℝ) * ((worldlinePolymerNativeCollar sys C_RCA γ).card : ℝ)) ≤
        (C_col ^ M.card) * F_raw γ := by
    intro γ hγ
    rcases Finset.mem_filter.mp hγ with ⟨_, hγ_val, hγ_M⟩
    have h_w := worldlinePolymerWeight_abs_le_prod hR_cut hβ_nn hJ hf_nn D_field sys
      h_sys_checks h_geom hc_wl_cal V hV_norm d_loc hd_scale ν γ hγ_val σ
    have h_e := exp_eighth_worldlinePolymerNativeCollar_le hC_RCA D_field sys h_sys_checks h_geom hM_sub hγ_M
    calc |worldlinePolymerWeight D_field sys C_RCA β V d_loc ν γ σ| *
          Real.exp ((1 / 8 : ℝ) * ((worldlinePolymerNativeCollar sys C_RCA γ).card : ℝ))
      _ ≤ F_raw γ * (C_col ^ M.card) :=
          mul_le_mul h_w h_e (Real.exp_nonneg _) (le_trans (abs_nonneg _) h_w)
      _ = (C_col ^ M.card) * F_raw γ := mul_comm _ _
  let K_max : ℕ := ℱ_M.sup (fun γ => γ.1.length)
  have h_len_mem : ∀ γ ∈ ℱ_M, γ.1.length ∈ Finset.range (K_max + 1) := fun γ hγ =>
    Finset.mem_range.mpr (Nat.lt_succ_of_le
      (Finset.le_sup (f := fun γ : WorldlineDysonPolymer L q_code => γ.1.length) hγ))
  have h_m_bound : ∀ m ∈ Finset.range (K_max + 1),
      (∑ γ ∈ ℱ_M.filter (fun γ => γ.1.length = m), F_raw γ) ≤
        (((M.card : ℝ) ^ m / (m.factorial : ℝ)) * ((2 : ℝ) ^ M.card)) *
          ∏ p ∈ M, kpMonomerWeight c_wl β J f p := by
    intro m _
    let ℱ_m := ℱ_M.filter (fun γ => γ.1.length = m)
    let monomerTuple (γ : WorldlineDysonPolymer L q_code) (j : Fin m) : WorldlineJumpMonomer L q_code :=
      if h : j.val < γ.1.length then γ.1.get ⟨j.val, h⟩ else ((0, ∅), (0, 0))
    let cubeTuple (γ : WorldlineDysonPolymer L q_code) (j : Fin m) : ℕ × Finset (Box3D L) :=
      (monomerTuple γ j).1
    let P_M := (Fintype.piFinset (fun _ : Fin m => M)) ×ˢ M.powerset
    have h_maps : ∀ γ ∈ ℱ_m, (cubeTuple γ, γ.2) ∈ P_M := by
      intro γ hγ
      rcases Finset.mem_filter.mp hγ with ⟨hγ_M_mem, h_len⟩
      rcases Finset.mem_filter.mp hγ_M_mem with ⟨_, _, h_mon⟩
      refine Finset.mem_product.mpr ⟨Fintype.mem_piFinset.mpr fun j => ?_, Finset.mem_powerset.mpr ?_⟩
      · have hj : j.val < γ.1.length := h_len ▸ j.isLt
        dsimp [cubeTuple, monomerTuple]; rw [dif_pos hj, ← h_mon]
        exact Finset.mem_union_left _ (List.mem_toFinset.mpr (List.mem_map_of_mem (List.get_mem _ _)))
      · rw [← h_mon]; exact Finset.subset_union_right
    have h_P_bound : ∀ P ∈ P_M,
        (∑ γ ∈ ℱ_m.filter (fun γ => (cubeTuple γ, γ.2) = P), F_raw γ) ≤
          ((m.factorial : ℝ)⁻¹) * ∏ p ∈ M, kpMonomerWeight c_wl β J f p := by
      intro P hP
      let ℱ_P := ℱ_m.filter (fun γ => (cubeTuple γ, γ.2) = P)
      change (∑ γ ∈ ℱ_P, F_raw γ) ≤ _
      by_cases h_emp : ℱ_P = ∅
      · rw [h_emp, Finset.sum_empty]
        exact mul_nonneg (by positivity) (Finset.prod_nonneg fun p hp => (h_bounds hp).1)
      · rcases Finset.nonempty_iff_ne_empty.mpr h_emp with ⟨γ₀, hγ₀⟩
        have h_ofFn_mon : ∀ γ ∈ ℱ_P, List.ofFn (monomerTuple γ) = γ.1 := by
          intro γ hγ
          exact ofFn_get_eq_self γ.1 ((0, ∅), (0, 0)) m (Finset.mem_filter.mp (Finset.mem_filter.mp hγ).1).2
        have h_ofFn_cube : ∀ γ ∈ ℱ_P, List.ofFn P.1 = γ.1.map Prod.fst := by
          intro γ hγ
          rw [← congrArg Prod.fst (Finset.mem_filter.mp hγ).2, ← h_ofFn_mon γ hγ, List.map_ofFn]; rfl
        have h_union_eq : (List.ofFn P.1).toFinset ∪ P.2 = M := by
          rw [h_ofFn_cube γ₀ hγ₀, ← congrArg Prod.snd (Finset.mem_filter.mp hγ₀).2]
          exact (Finset.mem_filter.mp (Finset.mem_filter.mp (Finset.mem_filter.mp hγ₀).1).1).2.2
        have h_F_eq : ∀ γ ∈ ℱ_P,
            F_raw γ = ((m.factorial : ℝ)⁻¹) * (∏ j : Fin m, w_J (P.1 j)) * ∏ ϑ ∈ P.2, w_D ϑ := by
          intro γ hγ
          have h_len : γ.1.length = m := (Finset.mem_filter.mp (Finset.mem_filter.mp hγ).1).2
          have h_eq_P2 : γ.2 = P.2 := congrArg Prod.snd (Finset.mem_filter.mp hγ).2
          have h_map_eq : γ.1.map (fun ξ => w_J ξ.1) = List.ofFn (fun j : Fin m => w_J (P.1 j)) := by
            calc γ.1.map (fun ξ => w_J ξ.1)
              _ = (γ.1.map Prod.fst).map w_J := by rw [List.map_map]; rfl
              _ = (List.ofFn P.1).map w_J := by rw [← h_ofFn_cube γ hγ]
              _ = List.ofFn (fun j : Fin m => w_J (P.1 j)) := by rw [List.map_ofFn]; rfl
          dsimp [F_raw]; rw [h_len, h_eq_P2, h_map_eq, List.prod_ofFn]
        have h_card_P : ℱ_P.card ≤
            ∏ j : Fin m, (validJumpMonomersAtCube D_field sys (P.1 j)).card := by
          rw [← Fintype.card_piFinset]
          refine Finset.card_le_card_of_injOn monomerTuple (fun γ hγ => ?_) (fun γ₁ hγ₁ γ₂ hγ₂ h_eq => ?_)
          · refine Fintype.mem_piFinset.mpr fun j => ?_
            have h_len : γ.1.length = m := (Finset.mem_filter.mp (Finset.mem_filter.mp hγ).1).2
            have h_val : IsValidWorldlinePolymer D_field sys C_RCA R_cut γ :=
              (Finset.mem_filter.mp (Finset.mem_filter.mp (Finset.mem_filter.mp hγ).1).1).2.1
            have h_eq_P1 : cubeTuple γ j = P.1 j :=
              congrFun (congrArg Prod.fst (Finset.mem_filter.mp hγ).2) j
            have hj : j.val < γ.1.length := h_len ▸ j.isLt
            rw [← h_eq_P1]
            change monomerTuple γ j ∈ validJumpMonomersAtCube D_field sys (monomerTuple γ j).1
            dsimp only [monomerTuple]
            rw [dif_pos hj]
            exact mem_validJumpMonomersAtCube_of_valid D_field sys
              (fun idx => (h_sys_checks idx).2.1) h_val (List.get_mem _ _)
          · exact Prod.ext (by rw [← h_ofFn_mon γ₁ hγ₁, ← h_ofFn_mon γ₂ hγ₂, h_eq])
              (by rw [congrArg Prod.snd (Finset.mem_filter.mp hγ₁).2,
                congrArg Prod.snd (Finset.mem_filter.mp hγ₂).2])
        have h_J_prod : ((ℱ_P.card : ℝ) * ∏ j : Fin m, w_J (P.1 j)) ≤
            ∏ p ∈ (List.ofFn P.1).toFinset, kpMonomerWeight c_wl β J f p := by
          have h_wJ_nn : 0 ≤ ∏ j : Fin m, w_J (P.1 j) :=
            Finset.prod_nonneg fun j _ => by dsimp [w_J]; have := hf_nn (P.1 j).1; positivity
          have h_P1_mem : ∀ j : Fin m, P.1 j ∈ M :=
            Fintype.mem_piFinset.mp (Finset.mem_product.mp hP).1
          calc (ℱ_P.card : ℝ) * ∏ j : Fin m, w_J (P.1 j)
            _ ≤ ((∏ j : Fin m, (validJumpMonomersAtCube D_field sys (P.1 j)).card : ℕ) : ℝ) *
                  ∏ j : Fin m, w_J (P.1 j) :=
                mul_le_mul_of_nonneg_right (by exact_mod_cast h_card_P) h_wJ_nn
            _ = ∏ j : Fin m, (((validJumpMonomersAtCube D_field sys (P.1 j)).card : ℝ) * w_J (P.1 j)) := by
                push_cast; rw [← Finset.prod_mul_distrib]
            _ ≤ ∏ j : Fin m, kpMonomerWeight c_wl β J f (P.1 j) := by
                refine Finset.prod_le_prod₀ (fun j _ => by
                  have := hf_nn (P.1 j).1; dsimp [w_J]; positivity) (fun j _ => ?_)
                exact validJumpMonomersAtCube_card_mul_le_kpMonomerWeight hR_cut hβ_nn hJ hf_nn
                  D_field sys h_geom hc_wl_cal (hM_sub (h_P1_mem j))
            _ = ((List.ofFn P.1).map (kpMonomerWeight c_wl β J f)).prod := by
                rw [List.map_ofFn, List.prod_ofFn]; rfl
            _ ≤ ∏ p ∈ (List.ofFn P.1).toFinset, kpMonomerWeight c_wl β J f p := by
                refine list_prod_le_finset_prod_of_le_one (List.ofFn P.1) (kpMonomerWeight c_wl β J f)
                  (fun p hp => ?_) (fun p hp => ?_)
                · rcases List.mem_ofFn.mp hp with ⟨j, rfl⟩; exact (h_bounds (h_P1_mem j)).1
                · rcases List.mem_ofFn.mp hp with ⟨j, rfl⟩; exact (h_bounds (h_P1_mem j)).2.2.1
        have h_D_prod : (∏ ϑ ∈ P.2, w_D ϑ) ≤ ∏ p ∈ P.2, kpMonomerWeight c_wl β J f p := by
          have hP2_sub : P.2 ⊆ M := Finset.mem_powerset.mp (Finset.mem_product.mp hP).2
          refine Finset.prod_le_prod₀ (fun ϑ _ => by dsimp [w_D]; have := hf_nn ϑ.1; positivity)
            (fun ϑ hϑ => (h_bounds (hP2_sub hϑ)).2.2.2)
        have h_union_prod :
            (∏ p ∈ (List.ofFn P.1).toFinset, kpMonomerWeight c_wl β J f p) *
              (∏ p ∈ P.2, kpMonomerWeight c_wl β J f p) ≤
              ∏ p ∈ M, kpMonomerWeight c_wl β J f p := by
          rw [← h_union_eq]
          refine finset_prod_mul_prod_le_prod_union_of_le_one _ _ _ (fun p hp => ?_) (fun p hp => ?_)
          · rw [h_union_eq] at hp; exact (h_bounds hp).1
          · rw [h_union_eq] at hp; exact (h_bounds hp).2.2.1
        calc (∑ γ ∈ ℱ_P, F_raw γ)
          _ = ∑ _γ ∈ ℱ_P, (((m.factorial : ℝ)⁻¹) * (∏ j : Fin m, w_J (P.1 j)) * ∏ ϑ ∈ P.2, w_D ϑ) :=
              Finset.sum_congr rfl h_F_eq
          _ = ((m.factorial : ℝ)⁻¹) * (((ℱ_P.card : ℝ) * ∏ j : Fin m, w_J (P.1 j)) * ∏ ϑ ∈ P.2, w_D ϑ) := by
              rw [Finset.sum_const, nsmul_eq_mul]; ring
          _ ≤ ((m.factorial : ℝ)⁻¹) *
                ((∏ p ∈ (List.ofFn P.1).toFinset, kpMonomerWeight c_wl β J f p) *
                  ∏ p ∈ P.2, kpMonomerWeight c_wl β J f p) := by
              refine mul_le_mul_of_nonneg_left (mul_le_mul h_J_prod h_D_prod
                (Finset.prod_nonneg fun ϑ _ => by dsimp [w_D]; have := hf_nn ϑ.1; positivity)
                (Finset.prod_nonneg fun p hp => ?_)) (by positivity)
              exact (h_bounds (h_union_eq ▸ Finset.mem_union_left _ hp)).1
          _ ≤ ((m.factorial : ℝ)⁻¹) * ∏ p ∈ M, kpMonomerWeight c_wl β J f p :=
              mul_le_mul_of_nonneg_left h_union_prod (by positivity)
    have h_card_PM : (P_M.card : ℝ) = ((M.card : ℝ) ^ m) * ((2 : ℝ) ^ M.card) := by
      dsimp [P_M]
      rw [Finset.card_product, Fintype.card_piFinset, Finset.prod_const, Finset.card_univ,
        Fintype.card_fin, Finset.card_powerset]
      push_cast; rfl
    calc (∑ γ ∈ ℱ_m, F_raw γ)
      _ = ∑ P ∈ P_M, ∑ γ ∈ ℱ_m.filter (fun γ => (cubeTuple γ, γ.2) = P), F_raw γ := by
          rw [Finset.sum_fiberwise_of_maps_to h_maps]
      _ ≤ ∑ _P ∈ P_M, (((m.factorial : ℝ)⁻¹) * ∏ p ∈ M, kpMonomerWeight c_wl β J f p) :=
          Finset.sum_le_sum h_P_bound
      _ = (((M.card : ℝ) ^ m / (m.factorial : ℝ)) * ((2 : ℝ) ^ M.card)) *
            ∏ p ∈ M, kpMonomerWeight c_wl β J f p := by
          rw [Finset.sum_const, nsmul_eq_mul, h_card_PM, div_eq_mul_inv]; ring
  have h_sum_m :
      (∑ m ∈ Finset.range (K_max + 1), (((M.card : ℝ) ^ m / (m.factorial : ℝ)) * ((2 : ℝ) ^ M.card))) ≤
        (4 * Real.exp 1) ^ M.card := by
    rw [← Finset.sum_mul]
    calc (∑ m ∈ Finset.range (K_max + 1), (M.card : ℝ) ^ m / (m.factorial : ℝ)) * ((2 : ℝ) ^ M.card)
      _ ≤ Real.exp (M.card : ℝ) * ((2 : ℝ) ^ M.card) :=
          mul_le_mul_of_nonneg_right (Real.sum_le_exp_of_nonneg (Nat.cast_nonneg M.card) (K_max + 1))
            (by positivity)
      _ = (2 * Real.exp 1) ^ M.card := by
          rw [mul_pow, ← Real.exp_nat_mul, mul_one, mul_comm]
      _ ≤ (4 * Real.exp 1) ^ M.card := by
          refine pow_le_pow_left₀ (by positivity) ?_ _
          have := Real.exp_pos 1; linarith
  have h_prod_M_nn : 0 ≤ ∏ p ∈ M, kpMonomerWeight c_wl β J f p :=
    Finset.prod_nonneg fun p hp => (h_bounds hp).1
  have h_raw_total : (∑ γ ∈ ℱ_M, F_raw γ) ≤
      (4 * Real.exp 1) ^ M.card * ∏ p ∈ M, kpMonomerWeight c_wl β J f p := by
    calc (∑ γ ∈ ℱ_M, F_raw γ)
      _ = ∑ m ∈ Finset.range (K_max + 1), ∑ γ ∈ ℱ_M.filter (fun γ => γ.1.length = m), F_raw γ := by
          rw [Finset.sum_fiberwise_of_maps_to h_len_mem]
      _ ≤ ∑ m ∈ Finset.range (K_max + 1),
            ((((M.card : ℝ) ^ m / (m.factorial : ℝ)) * ((2 : ℝ) ^ M.card)) *
              ∏ p ∈ M, kpMonomerWeight c_wl β J f p) :=
          Finset.sum_le_sum h_m_bound
      _ = (∑ m ∈ Finset.range (K_max + 1),
            (((M.card : ℝ) ^ m / (m.factorial : ℝ)) * ((2 : ℝ) ^ M.card))) *
            ∏ p ∈ M, kpMonomerWeight c_wl β J f p := by rw [← Finset.sum_mul]
      _ ≤ (4 * Real.exp 1) ^ M.card * ∏ p ∈ M, kpMonomerWeight c_wl β J f p :=
          mul_le_mul_of_nonneg_right h_sum_m h_prod_M_nn
  calc (∑ γ ∈ ℱ_M,
        |worldlinePolymerWeight D_field sys C_RCA β V d_loc ν γ σ| *
          Real.exp ((1 / 8 : ℝ) * ((worldlinePolymerNativeCollar sys C_RCA γ).card : ℝ)))
    _ ≤ ∑ γ ∈ ℱ_M, (C_col ^ M.card) * F_raw γ := Finset.sum_le_sum h_pt
    _ = (C_col ^ M.card) * ∑ γ ∈ ℱ_M, F_raw γ := by rw [← Finset.mul_sum]
    _ ≤ (C_col ^ M.card) * ((4 * Real.exp 1) ^ M.card * ∏ p ∈ M, kpMonomerWeight c_wl β J f p) :=
        mul_le_mul_of_nonneg_left h_raw_total (pow_nonneg (Real.exp_nonneg _) _)
    _ = ∏ p ∈ M, (4 * Real.exp 1 * C_col * kpMonomerWeight c_wl β J f p) := by
        rw [Finset.prod_mul_distrib, Finset.prod_const]; ring
    _ ≤ ∏ _p ∈ M, ((1 / 64 : ℝ) * Real.exp (-12 * (Δ_V : ℝ))) := by
        refine Finset.prod_le_prod₀ (fun p hp => ?_) (fun p hp => (h_bounds hp).2.1)
        have hp_nn := (h_bounds hp).1; dsimp [C_col]; positivity
    _ = ((1 / 64 : ℝ) * Real.exp (-12 * (Δ_V : ℝ))) ^ M.card := by rw [Finset.prod_const]

private lemma worldline_polymer_native_collar_kp_bound
    {L q_code r_0 m_max w_0 R_cut : ℕ} [NeZero L]
    {C_RCA β Δ_RCA C_wl c_wl J : ℝ} {f : ℕ → ℝ}
    (D_field : Box3D L → LocalCSSDescriptor q_code r_0 m_max)
    (sys : SysCSS[L, q_code, m_max])
    (h_sys_checks : ∀ idx, sys.checkProj idx = staticCSSCheckProj D_field idx ∧
      sys.support idx = staticCSSCheckSupport D_field idx ∧ sys.weight idx = 1)
    (h_geom : sys.IsGeometricallyLocal r_0 w_0)
    (V : QuasiLocalPerturbation 3 L (SiteCSS[L, q_code]))
    (hf_nn : ∀ r, 0 ≤ f r)
    (hV_norm : ∀ r ∈ Finset.Icc 1 (min R_cut L), ∀ A ∈ boxCubes 3 L r, ‖V.term r A‖ ≤ J * f r)
    (d_loc : ℕ → Finset (Box3D L) → (IdxCSS[L, q_code, m_max] → Bool) → ℝ)
    (hd_scale : ∀ r ∈ Finset.Icc 1 (min R_cut L), ∀ A ∈ boxCubes 3 L r,
      ∀ σ, |d_loc r A σ| ≤ 2 * (J * f r))
    (hR_cut : 1 ≤ R_cut) (hC_RCA : 0 ≤ C_RCA)
    (hC_wl_cal : (kpCollarMaxCheckCard R_cut r_0 w_0 C_RCA : ℝ) ≤ C_wl)
    (hc_wl_cal : (kpCollarMaxCheckCard R_cut r_0 w_0 C_RCA : ℝ) ≤ c_wl)
    (hβ : 16 < β) (hJ : 0 ≤ J)
    (h_sum_pos : 0 < worldlineNativeKPSum f C_wl c_wl β R_cut)
    (h_thresh : J ≤ worldlineSpanningThreshold Δ_RCA C_wl c_wl β f R_cut)
    (ν : PauliBitstringPair L q_code)
    (σ : IdxCSS[L, q_code, m_max] → Bool)
    (u₁ : IdxCSS[L, q_code, m_max]) :
    Summable (fun γ : WorldlineDysonPolymer L q_code =>
      if IsValidWorldlinePolymer D_field sys C_RCA R_cut γ ∧
          u₁ ∈ worldlinePolymerNativeCollar sys C_RCA γ then
        |worldlinePolymerWeight D_field sys C_RCA β V d_loc ν γ σ| *
          Real.exp ((1 / 8 : ℝ) * ((worldlinePolymerNativeCollar sys C_RCA γ).card : ℝ))
      else 0) ∧
    (∑' γ : WorldlineDysonPolymer L q_code,
      if IsValidWorldlinePolymer D_field sys C_RCA R_cut γ ∧
          u₁ ∈ worldlinePolymerNativeCollar sys C_RCA γ then
        |worldlinePolymerWeight D_field sys C_RCA β V d_loc ν γ σ| *
          Real.exp ((1 / 8 : ℝ) * ((worldlinePolymerNativeCollar sys C_RCA γ).card : ℝ))
      else 0) ≤ 1 / 8 := by
  let w_exp (γ : WorldlineDysonPolymer L q_code) : ℝ :=
    |worldlinePolymerWeight D_field sys C_RCA β V d_loc ν γ σ| *
      Real.exp ((1 / 8 : ℝ) * ((worldlinePolymerNativeCollar sys C_RCA γ).card : ℝ))
  have hw_exp_nn : ∀ γ, 0 ≤ w_exp γ := fun γ => mul_nonneg (abs_nonneg _) (Real.exp_nonneg _)
  let term_u (γ : WorldlineDysonPolymer L q_code) : ℝ :=
    if IsValidWorldlinePolymer D_field sys C_RCA R_cut γ ∧
        u₁ ∈ worldlinePolymerNativeCollar sys C_RCA γ then w_exp γ else 0
  have h_term_u_nn : ∀ γ, 0 ≤ term_u γ := fun γ => by
    dsimp [term_u]; split_ifs <;> [exact hw_exp_nn γ; exact le_refl 0]
  have h_fin_bound : ∀ ℱ : Finset (WorldlineDysonPolymer L q_code),
      (∑ γ ∈ ℱ, term_u γ) ≤ 1 / 8 := by
    intro ℱ
    let U := worldlineScaleCubeFinset L R_cut
    let S_cal : ℕ := 4 * (Nat.ceil C_RCA + 1) * (r_0 + 1) * R_cut
    let Δ_V : ℕ := kpCollarMaxCheckCard R_cut r_0 w_0 C_RCA
    let ℱ_u := ℱ.filter (fun γ => IsValidWorldlinePolymer D_field sys C_RCA R_cut γ ∧
      u₁ ∈ worldlinePolymerNativeCollar sys C_RCA γ)
    let P_act (M : Finset (ℕ × Finset (Box3D L))) : Prop :=
      ∃ γ ∈ ℱ_u, worldlinePolymerMonomers γ = M
    have hP_act : ∀ M ⊆ U, P_act M →
        KPIsConnectedSubgraph (KPScaleCubeOverlap sys C_RCA) M ∧
        ∃ p₀ ∈ M, ∀ i : Fin 3,
          kpNatDist (anchorOfCube p₀.1 p₀.2 i).val (kpStaticCSSCheckAnchor u₁ i).val ≤
            M.card * Δ_V := by
      intro M hM_sub ⟨γ, hγ_mem, hγ_M⟩
      rcases Finset.mem_filter.mp hγ_mem with ⟨_, hγ_val, hc_col⟩
      refine ⟨hγ_M ▸ hγ_val.2.2.2, ?_⟩
      have hM_nonempty : M.Nonempty := by
        rw [← hγ_M]
        rcases List.exists_mem_of_length_pos (l := γ.1) (by have := hγ_val.2.2.1.1; omega) with ⟨ξ, hξ⟩
        exact ⟨ξ.1, Finset.mem_union_left _ (List.mem_toFinset.mpr (List.mem_map_of_mem hξ))⟩
      unfold worldlinePolymerNativeCollar nativeCollarSupport at hc_col
      rw [hγ_M] at hc_col
      rcases Finset.mem_biUnion.mp hc_col with ⟨p₀, hp₀, hc_p₀⟩
      rcases mem_kpScaleCubeFinset_iff.mp (hM_sub hp₀) with ⟨hr₀, hA₀⟩
      have hp₀_sub_self : p₀.2 ⊆ boxCube (anchorOfCube p₀.1 p₀.2) p₀.1 := by
        rw [boxCube_anchorOfCube hA₀]
      have hr₀_le_S : p₀.1 ≤ M.card * S_cal := by
        have h1 : p₀.1 ≤ R_cut := le_trans (Finset.mem_Icc.mp hr₀).2 (Nat.min_le_left R_cut L)
        have h2 : R_cut ≤ 1 * S_cal := by
          dsimp [S_cal]; rw [one_mul]; exact Nat.le_mul_of_pos_left R_cut (by positivity)
        exact le_trans h1 (le_trans h2 (Nat.mul_le_mul_right S_cal hM_nonempty.card_pos))
      refine ⟨p₀, hp₀, fun i => ?_⟩
      exact kpNatDist_anchor_le_of_enclosing_and_collar hR_cut D_field sys
        (fun idx => (h_sys_checks idx).2.1) hC_RCA (hM_sub hp₀)
        (Finset.mem_Icc.mp hr₀).1 hr₀_le_S hr₀_le_S
        hp₀_sub_self hA₀ hp₀_sub_self hc_p₀ i
    let Pow_act := U.powerset.filter (fun M => 1 ≤ M.card ∧ P_act M)
    have h_maps_M : ∀ γ ∈ ℱ_u, worldlinePolymerMonomers γ ∈ Pow_act := by
      intro γ hγ
      rcases Finset.mem_filter.mp hγ with ⟨_, hγ_val, _⟩
      have hM_pos : 1 ≤ (worldlinePolymerMonomers γ).card := by
        rcases List.exists_mem_of_length_pos (l := γ.1) (by have := hγ_val.2.2.1.1; omega) with ⟨ξ, hξ⟩
        exact Finset.card_pos.mpr
          ⟨ξ.1, Finset.mem_union_left _ (List.mem_toFinset.mpr (List.mem_map_of_mem hξ))⟩
      exact Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr hγ_val.1, hM_pos, γ, hγ, rfl⟩
    have h_fib_le : ∀ M ∈ Pow_act,
        (∑ γ ∈ ℱ_u.filter (fun γ => worldlinePolymerMonomers γ = M), w_exp γ) ≤
          ((1 / 64 : ℝ) * Real.exp (-12 * (Δ_V : ℝ))) ^ M.card := by
      intro M hM
      have hM_sub : M ⊆ U := Finset.mem_powerset.mp (Finset.mem_filter.mp hM).1
      have h_sub_filt : ℱ_u.filter (fun γ => worldlinePolymerMonomers γ = M) ⊆
          ℱ.filter (fun γ => IsValidWorldlinePolymer D_field sys C_RCA R_cut γ ∧
            worldlinePolymerMonomers γ = M) := by
        intro γ hγ
        rcases Finset.mem_filter.mp hγ with ⟨hγ_c, hγ_M⟩
        rcases Finset.mem_filter.mp hγ_c with ⟨hγ_ℱ, hγ_val, _⟩
        exact Finset.mem_filter.mpr ⟨hγ_ℱ, hγ_val, hγ_M⟩
      exact le_trans
        (Finset.sum_le_sum_of_subset_of_nonneg h_sub_filt (fun γ _ _ => hw_exp_nn γ))
        (sum_validPolymers_with_monomers_le hR_cut hC_RCA hC_wl_cal hc_wl_cal
          hβ hJ hf_nn h_sum_pos h_thresh D_field sys h_sys_checks
          h_geom V hV_norm d_loc hd_scale ν σ ℱ hM_sub)
    have h_maps_n : ∀ M ∈ Pow_act, M.card ∈ Finset.Icc 1 U.card := fun M hM =>
      Finset.mem_Icc.mpr ⟨(Finset.mem_filter.mp hM).2.1,
        Finset.card_le_card (Finset.mem_powerset.mp (Finset.mem_filter.mp hM).1)⟩
    have h_n_bound : ∀ n ∈ Finset.Icc 1 U.card,
        (∑ M ∈ Pow_act.filter (fun M => M.card = n),
          ((1 / 64 : ℝ) * Real.exp (-12 * (Δ_V : ℝ))) ^ M.card) ≤ (1 / 64 : ℝ) ^ n := by
      intro n hn
      have hn_pos : 1 ≤ n := (Finset.mem_Icc.mp hn).1
      have h_filt_eq : Pow_act.filter (fun M => M.card = n) =
          U.powerset.filter (fun M => M.card = n ∧ P_act M) := by
        ext M; simp only [Pow_act, Finset.mem_filter]
        exact ⟨fun ⟨⟨h1, _, h3⟩, h4⟩ => ⟨h1, h4, h3⟩, fun ⟨h1, h4, h3⟩ => ⟨⟨h1, h4 ▸ hn_pos, h3⟩, h4⟩⟩
      have h_card_n := card_activeMonomerSets_of_card_le (L_star := Fintype.card (Box3D L))
        hR_cut D_field sys h_sys_checks h_geom hC_RCA
        ((le_add_of_nonneg_right zero_le_one).trans (Real.add_one_le_exp _))
        (kpStaticCSSCheckAnchor u₁) P_act
        (fun M hM hp => ⟨(hP_act M hM hp).1, fun _ => (hP_act M hM hp).2⟩) hn_pos
      calc (∑ M ∈ Pow_act.filter (fun M => M.card = n),
            ((1 / 64 : ℝ) * Real.exp (-12 * (Δ_V : ℝ))) ^ M.card)
        _ = ((U.powerset.filter (fun M => M.card = n ∧ P_act M)).card : ℝ) *
            (((1 / 64 : ℝ) * Real.exp (-12 * (Δ_V : ℝ))) ^ n) := by
            rw [h_filt_eq, Finset.sum_congr rfl (fun M hM => by rw [(Finset.mem_filter.mp hM).2.1]),
              Finset.sum_const, nsmul_eq_mul]
        _ ≤ (Real.exp (12 * (Δ_V : ℝ))) ^ n *
            (((1 / 64 : ℝ) * Real.exp (-12 * (Δ_V : ℝ))) ^ n) :=
            mul_le_mul_of_nonneg_right h_card_n (by positivity)
        _ = ((1 / 64 : ℝ) * (Real.exp (12 * (Δ_V : ℝ)) * Real.exp (-12 * (Δ_V : ℝ)))) ^ n := by
            rw [← mul_pow]; ring
        _ = (1 / 64 : ℝ) ^ n := by
            rw [← Real.exp_add]
            have h_z : (12 : ℝ) * (Δ_V : ℝ) + -12 * (Δ_V : ℝ) = 0 := by ring
            rw [h_z, Real.exp_zero, mul_one]
    calc (∑ γ ∈ ℱ, term_u γ)
      _ = ∑ γ ∈ ℱ_u, w_exp γ := by
          dsimp [term_u, ℱ_u]; rw [Finset.sum_filter]
          exact Finset.sum_congr rfl fun γ _ => by split_ifs <;> rfl
      _ = ∑ M ∈ Pow_act, ∑ γ ∈ ℱ_u.filter (fun γ => worldlinePolymerMonomers γ = M), w_exp γ := by
          rw [Finset.sum_fiberwise_of_maps_to h_maps_M]
      _ ≤ ∑ M ∈ Pow_act, ((1 / 64 : ℝ) * Real.exp (-12 * (Δ_V : ℝ))) ^ M.card :=
          Finset.sum_le_sum h_fib_le
      _ = ∑ n ∈ Finset.Icc 1 U.card,
            ∑ M ∈ Pow_act.filter (fun M => M.card = n),
              ((1 / 64 : ℝ) * Real.exp (-12 * (Δ_V : ℝ))) ^ M.card := by
          rw [Finset.sum_fiberwise_of_maps_to h_maps_n]
      _ ≤ ∑ n ∈ Finset.Icc 1 U.card, (1 / 64 : ℝ) ^ n := Finset.sum_le_sum h_n_bound
      _ ≤ 2 * (1 / 64 : ℝ) := sum_Icc_pow_le_two_mul (by norm_num) (by norm_num) U.card
      _ ≤ 1 / 8 := by norm_num
  have h_summable : Summable term_u := summable_of_sum_le h_term_u_nn h_fin_bound
  exact ⟨h_summable, le_of_tendsto' h_summable.hasSum h_fin_bound⟩

private def pinnedCollarClusterAbsWeight
    {L q_code r_0 m_max : ℕ} [NeZero L]
    (D_field : Box3D L → LocalCSSDescriptor q_code r_0 m_max)
    (sys : SysCSS[L, q_code, m_max]) (C_RCA : ℝ) (R_cut : ℕ) (β : ℝ)
    (V : QuasiLocalPerturbation 3 L (SiteCSS[L, q_code]))
    (d_loc : ℕ → Finset (Box3D L) → (IdxCSS[L, q_code, m_max] → Bool) → ℝ)
    (ν : PauliBitstringPair L q_code)
    (σ : IdxCSS[L, q_code, m_max] → Bool)
    (c : IdxCSS[L, q_code, m_max])
    (K : WorldlineUrsellCluster L q_code) : ℝ :=
  if IsValidWorldlineUrsellCluster D_field sys C_RCA R_cut K ∧
      ∃ γ ∈ K, c ∈ worldlinePolymerNativeCollar sys C_RCA γ then
    |worldlineClusterUrsellWeight D_field sys C_RCA β V d_loc ν K σ|
  else 0

private lemma pinnedCollarClusterAbsWeight_nonneg
    {L q_code r_0 m_max : ℕ} [NeZero L]
    (D_field : Box3D L → LocalCSSDescriptor q_code r_0 m_max)
    (sys : SysCSS[L, q_code, m_max]) (C_RCA : ℝ) (R_cut : ℕ) (β : ℝ)
    (V : QuasiLocalPerturbation 3 L (SiteCSS[L, q_code]))
    (d_loc : ℕ → Finset (Box3D L) → (IdxCSS[L, q_code, m_max] → Bool) → ℝ)
    (ν : PauliBitstringPair L q_code)
    (σ : IdxCSS[L, q_code, m_max] → Bool)
    (c : IdxCSS[L, q_code, m_max])
    (K : WorldlineUrsellCluster L q_code) :
    0 ≤ pinnedCollarClusterAbsWeight D_field sys C_RCA R_cut β V d_loc ν σ c K := by
  unfold pinnedCollarClusterAbsWeight
  split_ifs <;> [exact abs_nonneg _; exact le_refl 0]

private lemma sum_pinnedCollarClusterAbsWeight_le_of_kp
    {L q_code r_0 m_max R_cut : ℕ} [NeZero L]
    {C_RCA β : ℝ}
    (D_field : Box3D L → LocalCSSDescriptor q_code r_0 m_max)
    (sys : SysCSS[L, q_code, m_max])
    (V : QuasiLocalPerturbation 3 L (SiteCSS[L, q_code]))
    (d_loc : ℕ → Finset (Box3D L) → (IdxCSS[L, q_code, m_max] → Bool) → ℝ)
    (ν : PauliBitstringPair L q_code)
    (σ : IdxCSS[L, q_code, m_max] → Bool)
    (h_kp : ∀ u₁ : IdxCSS[L, q_code, m_max],
      Summable (fun γ : WorldlineDysonPolymer L q_code =>
        if IsValidWorldlinePolymer D_field sys C_RCA R_cut γ ∧
            u₁ ∈ worldlinePolymerNativeCollar sys C_RCA γ then
          |worldlinePolymerWeight D_field sys C_RCA β V d_loc ν γ σ| *
            Real.exp ((1 / 8 : ℝ) * ((worldlinePolymerNativeCollar sys C_RCA γ).card : ℝ))
        else 0) ∧
      (∑' γ : WorldlineDysonPolymer L q_code,
        if IsValidWorldlinePolymer D_field sys C_RCA R_cut γ ∧
            u₁ ∈ worldlinePolymerNativeCollar sys C_RCA γ then
          |worldlinePolymerWeight D_field sys C_RCA β V d_loc ν γ σ| *
            Real.exp ((1 / 8 : ℝ) * ((worldlinePolymerNativeCollar sys C_RCA γ).card : ℝ))
        else 0) ≤ 1 / 8)
    (c : IdxCSS[L, q_code, m_max])
    (ℱ : Finset (WorldlineUrsellCluster L q_code)) :
    (∑ K ∈ ℱ, pinnedCollarClusterAbsWeight D_field sys C_RCA R_cut β V d_loc ν σ c K) ≤ 1 / 8 := by
  let P₀ : Finset (WorldlineDysonPolymer L q_code) :=
    (ℱ.biUnion List.toFinset).filter (IsValidWorldlinePolymer D_field sys C_RCA R_cut)
  let w (γ : WorldlineDysonPolymer L q_code) : ℝ :=
    |worldlinePolymerWeight D_field sys C_RCA β V d_loc ν γ σ|
  let a (γ : WorldlineDysonPolymer L q_code) : ℝ :=
    (1 / 8 : ℝ) * ((worldlinePolymerNativeCollar sys C_RCA γ).card : ℝ)
  let incompat := ArePolymersIncompatible sys C_RCA
  have hw : ∀ γ ∈ P₀, 0 ≤ w γ := fun _ _ => abs_nonneg _
  have ha : ∀ γ ∈ P₀, 0 ≤ a γ := fun _ _ => mul_nonneg (by norm_num) (Nat.cast_nonneg _)
  have h_u₁_le : ∀ u₁ : IdxCSS[L, q_code, m_max],
      (∑ γ ∈ P₀.filter (fun γ => u₁ ∈ worldlinePolymerNativeCollar sys C_RCA γ), w γ * Real.exp (a γ)) ≤ 1 / 8 := by
    intro u₁
    let f_u₁ := fun γ : WorldlineDysonPolymer L q_code =>
      if IsValidWorldlinePolymer D_field sys C_RCA R_cut γ ∧
          u₁ ∈ worldlinePolymerNativeCollar sys C_RCA γ then w γ * Real.exp (a γ) else 0
    have h_eq : ∀ γ ∈ P₀.filter (fun γ => u₁ ∈ worldlinePolymerNativeCollar sys C_RCA γ),
        w γ * Real.exp (a γ) = f_u₁ γ := by
      intro γ hγ; rcases Finset.mem_filter.mp hγ with ⟨hγ_P₀, hu₁⟩
      dsimp [f_u₁]; rw [if_pos ⟨(Finset.mem_filter.mp hγ_P₀).2, hu₁⟩]
    rw [Finset.sum_congr rfl h_eq]
    exact le_trans (Summable.sum_le_tsum _ (fun γ _ => by split_ifs <;> positivity) (h_kp u₁).1) (h_kp u₁).2
  have h_kp_a : ∀ γ₀ ∈ P₀, (∑ γ ∈ P₀.filter (incompat γ₀), w γ * Real.exp (a γ)) ≤ a γ₀ := by
    intro γ₀ _
    have h_sub : P₀.filter (incompat γ₀) ⊆
        (worldlinePolymerNativeCollar sys C_RCA γ₀).biUnion
          (fun u₁ => P₀.filter (fun γ => u₁ ∈ worldlinePolymerNativeCollar sys C_RCA γ)) := by
      intro γ hγ; rcases Finset.mem_filter.mp hγ with ⟨hγ_P₀, h_inc⟩
      rcases Finset.not_disjoint_iff.mp h_inc with ⟨u₁, hu₁_₀, hu₁_γ⟩
      exact Finset.mem_biUnion.mpr ⟨u₁, hu₁_₀, Finset.mem_filter.mpr ⟨hγ_P₀, hu₁_γ⟩⟩
    calc (∑ γ ∈ P₀.filter (incompat γ₀), w γ * Real.exp (a γ))
      _ ≤ ∑ γ ∈ (worldlinePolymerNativeCollar sys C_RCA γ₀).biUnion
            (fun u₁ => P₀.filter (fun γ => u₁ ∈ worldlinePolymerNativeCollar sys C_RCA γ)),
            w γ * Real.exp (a γ) :=
          Finset.sum_le_sum_of_subset_of_nonneg h_sub (fun _ _ _ => mul_nonneg (abs_nonneg _) (Real.exp_nonneg _))
      _ ≤ ∑ u₁ ∈ worldlinePolymerNativeCollar sys C_RCA γ₀,
            ∑ γ ∈ P₀.filter (fun γ => u₁ ∈ worldlinePolymerNativeCollar sys C_RCA γ),
              w γ * Real.exp (a γ) :=
          sum_biUnion_le_of_nonneg _ _ (fun _ => mul_nonneg (abs_nonneg _) (Real.exp_nonneg _))
      _ ≤ ∑ _u₁ ∈ worldlinePolymerNativeCollar sys C_RCA γ₀, (1 / 8 : ℝ) :=
          Finset.sum_le_sum fun u₁ _ => h_u₁_le u₁
      _ = a γ₀ := by simp [a, mul_comm]
  let T_c := P₀.filter (fun γ => c ∈ worldlinePolymerNativeCollar sys C_RCA γ)
  have h_root_sum : (∑ γ₀ ∈ T_c, w γ₀ * Real.exp (a γ₀)) ≤ 1 / 8 := h_u₁_le c
  have h_prod_get : ∀ K : List (WorldlineDysonPolymer L q_code),
      |(K.map (fun γ => worldlinePolymerWeight D_field sys C_RCA β V d_loc ν γ σ)).prod| =
        ∏ i : Fin K.length, w (K.get i) := by
    intro K
    have h_abs : |(K.map (fun γ => worldlinePolymerWeight D_field sys C_RCA β V d_loc ν γ σ)).prod| =
        (K.map w).prod := by
      induction K with
      | nil => simp
      | cons hd tl ih => simp [List.map_cons, List.prod_cons, abs_mul, ih, w]
    have h_ofFn : K.map w = List.ofFn (fun i : Fin K.length => w (K.get i)) :=
      List.ext_get (by simp) (by simp)
    rw [h_abs, h_ofFn, List.prod_ofFn]
  let tupleTerm (p : ℕ) (r : Fin p) (t : Fin p → WorldlineDysonPolymer L q_code) : ℝ :=
    if c ∈ worldlinePolymerNativeCollar sys C_RCA (t r) then
      ∑ f ∈ (arborescenceForests Finset.univ {r}).filter
          (fun f => ∀ v ∈ (Finset.univ : Finset (Fin p)) \ {r}, incompat (t (f v)) (t v)),
        ∏ v : Fin p, w (t v)
    else 0
  let tupleBound (p : ℕ) (t : Fin p → WorldlineDysonPolymer L q_code) : ℝ :=
    ((p.factorial : ℝ)⁻¹) * ∑ r : Fin p, tupleTerm p r t
  have h_term_nn : ∀ (p : ℕ) (r : Fin p) (t : Fin p → WorldlineDysonPolymer L q_code),
      0 ≤ tupleTerm p r t := fun p r t => by
    dsimp [tupleTerm]; split_ifs
    · exact Finset.sum_nonneg fun _ _ => Finset.prod_nonneg fun _ _ => abs_nonneg _
    · exact le_refl 0
  have h_bound_nn : ∀ (p : ℕ) (t : Fin p → WorldlineDysonPolymer L q_code), 0 ≤ tupleBound p t :=
    fun p t => mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg _)) (Finset.sum_nonneg fun r _ => h_term_nn p r t)
  have h_K_le_tuple : ∀ K : WorldlineUrsellCluster L q_code,
      pinnedCollarClusterAbsWeight D_field sys C_RCA R_cut β V d_loc ν σ c K ≤
        tupleBound K.length (fun i => K.get i) := by
    intro K; unfold pinnedCollarClusterAbsWeight; split_ifs with h_cond
    · rcases h_cond with ⟨h_val, γ₀, hγ₀_K, hc_γ₀⟩
      have hp : 0 < K.length := List.length_pos_iff.mpr h_val.1
      rcases List.mem_iff_get.mp hγ₀_K with ⟨r₀, rfl⟩
      unfold worldlineClusterUrsellWeight ursellConnectedGraphCoeff
      rw [abs_mul, abs_mul, abs_of_nonneg (inv_nonneg.mpr (Nat.cast_nonneg _)), h_prod_get K, mul_assoc]
      refine mul_le_mul_of_nonneg_left ?_ (inv_nonneg.mpr (Nat.cast_nonneg _))
      have h_penrose := abs_sum_connGraphs_le_arborescenceForests hp
        (PolymerClusterOverlap sys C_RCA K) (fun u v h => ⟨h.1.symm, fun hd => h.2 hd.symm⟩) r₀
      have h_sub_arb : (arborescenceForests Finset.univ {r₀}).filter
          (fun f => ∀ v : Fin K.length, v ≠ r₀ → PolymerClusterOverlap sys C_RCA K (f v) v) ⊆
          (arborescenceForests Finset.univ {r₀}).filter
          (fun f => ∀ v ∈ (Finset.univ : Finset (Fin K.length)) \ {r₀}, incompat (K.get (f v)) (K.get v)) := by
        intro f hf; rcases Finset.mem_filter.mp hf with ⟨hf_arb, hf_ov⟩
        refine Finset.mem_filter.mpr ⟨hf_arb, fun v hv => (hf_ov v (by simpa using hv)).2⟩
      have h_card_le : (((arborescenceForests Finset.univ {r₀}).filter
          (fun f => ∀ v : Fin K.length, v ≠ r₀ → PolymerClusterOverlap sys C_RCA K (f v) v)).card : ℝ) ≤
          (((arborescenceForests Finset.univ {r₀}).filter
          (fun f => ∀ v ∈ (Finset.univ : Finset (Fin K.length)) \ {r₀}, incompat (K.get (f v)) (K.get v))).card : ℝ) :=
        Nat.cast_le.mpr (Finset.card_le_card h_sub_arb)
      have h_prod_nn : 0 ≤ ∏ i : Fin K.length, w (K.get i) := Finset.prod_nonneg fun _ _ => abs_nonneg _
      have h_r₀_eq : (((arborescenceForests Finset.univ {r₀}).filter
          (fun f => ∀ v ∈ (Finset.univ : Finset (Fin K.length)) \ {r₀}, incompat (K.get (f v)) (K.get v))).card : ℝ) *
          (∏ i : Fin K.length, w (K.get i)) = tupleTerm K.length r₀ (fun i => K.get i) := by
        change _ = if c ∈ worldlinePolymerNativeCollar sys C_RCA (K.get r₀) then
          ∑ f ∈ (arborescenceForests Finset.univ {r₀}).filter
              (fun f => ∀ v ∈ (Finset.univ : Finset (Fin K.length)) \ {r₀}, incompat (K.get (f v)) (K.get v)),
            ∏ v : Fin K.length, w (K.get v) else 0
        rw [if_pos hc_γ₀, Finset.sum_const, nsmul_eq_mul]
      calc |∑ G ∈ (Finset.univ.filter (fun e : Fin K.length × Fin K.length =>
              e.1 < e.2 ∧ PolymerClusterOverlap sys C_RCA K e.1 e.2)).powerset.filter
              (fun G => KPIsConnectedSubgraph (fun a b => (a, b) ∈ G ∨ (b, a) ∈ G) Finset.univ),
            ((-1 : ℝ) ^ G.card)| * (∏ i : Fin K.length, w (K.get i))
        _ ≤ (((arborescenceForests Finset.univ {r₀}).filter
            (fun f => ∀ v ∈ (Finset.univ : Finset (Fin K.length)) \ {r₀}, incompat (K.get (f v)) (K.get v))).card : ℝ) *
            (∏ i : Fin K.length, w (K.get i)) :=
            mul_le_mul_of_nonneg_right (le_trans h_penrose h_card_le) h_prod_nn
        _ = tupleTerm K.length r₀ (fun i => K.get i) := h_r₀_eq
        _ ≤ ∑ r : Fin K.length, tupleTerm K.length r (fun i => K.get i) :=
            Finset.single_le_sum (fun r _ => h_term_nn K.length r _) (Finset.mem_univ r₀)
    · exact h_bound_nn K.length _
  let P := ℱ.sup List.length
  let ℱ_val := ℱ.filter (fun K => IsValidWorldlineUrsellCluster D_field sys C_RCA R_cut K)
  have h_sum_val : (∑ K ∈ ℱ, pinnedCollarClusterAbsWeight D_field sys C_RCA R_cut β V d_loc ν σ c K) =
      ∑ K ∈ ℱ_val, pinnedCollarClusterAbsWeight D_field sys C_RCA R_cut β V d_loc ν σ c K := by
    symm; refine Finset.sum_subset (Finset.filter_subset _ _) fun K hK h_not => ?_
    have h_nv : ¬IsValidWorldlineUrsellCluster D_field sys C_RCA R_cut K :=
      fun hv => h_not (Finset.mem_filter.mpr ⟨hK, hv⟩)
    unfold pinnedCollarClusterAbsWeight; rw [if_neg (fun h => h_nv h.1)]
  have h_part_P : ℱ_val = (Finset.Icc 1 P).biUnion (fun p => ℱ_val.filter (fun K => K.length = p)) := by
    ext K; simp only [Finset.mem_biUnion, Finset.mem_Icc, Finset.mem_filter]
    exact ⟨fun hK => ⟨K.length, ⟨List.length_pos_iff.mpr (Finset.mem_filter.mp hK).2.1,
      Finset.le_sup (f := List.length) (Finset.mem_filter.mp hK).1⟩, hK, rfl⟩,
      fun ⟨_, _, hK, _⟩ => hK⟩
  have h_disj_P : Set.PairwiseDisjoint ↑(Finset.Icc 1 P) (fun p => ℱ_val.filter (fun K => K.length = p)) :=
    fun p₁ _ p₂ _ h_ne => Finset.disjoint_left.mpr fun K h₁ h₂ =>
      h_ne ((Finset.mem_filter.mp h₁).2.symm.trans (Finset.mem_filter.mp h₂).2)
  let γ_def : WorldlineDysonPolymer L q_code := ([], ∅)
  let toTuple (p : ℕ) (K : WorldlineUrsellCluster L q_code) : Fin p → WorldlineDysonPolymer L q_code :=
    if hp : K.length = p then fun i => K.get (i.cast hp.symm) else fun _ => γ_def
  have h_tuple_cast : ∀ (K : WorldlineUrsellCluster L q_code) (p : ℕ) (hp : K.length = p),
      tupleBound K.length (fun i => K.get i) = tupleBound p (toTuple p K) := by
    intro K p hp; subst hp
    have h_eq : (fun i : Fin K.length => K.get i) = toTuple K.length K := by dsimp [toTuple]; rw [dif_pos rfl]
    rw [h_eq]
  have h_p_sum_le : ∀ p ∈ Finset.Icc 1 P,
      (∑ K ∈ ℱ_val.filter (fun K => K.length = p),
        pinnedCollarClusterAbsWeight D_field sys C_RCA R_cut β V d_loc ν σ c K) ≤
      ∑ γ₀ ∈ T_c, w γ₀ * kpForestWeight P₀ incompat w p [γ₀] := by
    intro p hp_Icc
    have hp_pos : 0 < p := Nat.lt_of_lt_of_le Nat.zero_lt_one (Finset.mem_Icc.mp hp_Icc).1
    have h_inj_p : Set.InjOn (toTuple p) (ℱ_val.filter (fun K => K.length = p)) := by
      intro K₁ hK₁ K₂ hK₂ h_eq
      have hp₁ : K₁.length = p := (Finset.mem_filter.mp hK₁).2
      have hp₂ : K₂.length = p := (Finset.mem_filter.mp hK₂).2
      refine List.ext_get (hp₁.trans hp₂.symm) fun n hn₁ hn₂ => ?_
      have h_i := congrFun h_eq ⟨n, hp₁ ▸ hn₁⟩
      dsimp [toTuple] at h_i; rw [dif_pos hp₁, dif_pos hp₂] at h_i; exact h_i
    have h_maps_p : ∀ K ∈ ℱ_val.filter (fun K => K.length = p),
        toTuple p K ∈ Fintype.piFinset (fun _ : Fin p => P₀) := by
      intro K hK; rcases Finset.mem_filter.mp hK with ⟨hK_val, hp_K⟩
      rcases Finset.mem_filter.mp hK_val with ⟨hK_ℱ, h_val⟩
      rw [Fintype.mem_piFinset]; intro i; dsimp [toTuple]; rw [dif_pos hp_K]
      have h_mem_K : K.get (i.cast hp_K.symm) ∈ K := List.get_mem K _
      exact Finset.mem_filter.mpr ⟨Finset.mem_biUnion.mpr ⟨K, hK_ℱ, List.mem_toFinset.mpr h_mem_K⟩,
        h_val.2.1 _ h_mem_K⟩
    have h_step1 : (∑ K ∈ ℱ_val.filter (fun K => K.length = p),
        pinnedCollarClusterAbsWeight D_field sys C_RCA R_cut β V d_loc ν σ c K) ≤
        ∑ t ∈ Fintype.piFinset (fun _ : Fin p => P₀), tupleBound p t := by
      calc (∑ K ∈ ℱ_val.filter (fun K => K.length = p),
            pinnedCollarClusterAbsWeight D_field sys C_RCA R_cut β V d_loc ν σ c K)
        _ ≤ ∑ K ∈ ℱ_val.filter (fun K => K.length = p), tupleBound p (toTuple p K) :=
            Finset.sum_le_sum fun K hK => h_tuple_cast K p (Finset.mem_filter.mp hK).2 ▸ h_K_le_tuple K
        _ = ∑ t ∈ (ℱ_val.filter (fun K => K.length = p)).image (toTuple p), tupleBound p t :=
            (Finset.sum_image h_inj_p).symm
        _ ≤ ∑ t ∈ Fintype.piFinset (fun _ : Fin p => P₀), tupleBound p t :=
            Finset.sum_le_sum_of_subset_of_nonneg (Finset.image_subset_iff.mpr h_maps_p)
              (fun t _ _ => h_bound_nn p t)
    have h_r_bound : ∀ r : Fin p,
        (∑ t ∈ Fintype.piFinset (fun _ : Fin p => P₀), tupleTerm p r t) ≤
          (((p - 1).factorial : ℝ)) * ∑ γ₀ ∈ T_c, w γ₀ * kpForestWeight P₀ incompat w p [γ₀] := by
      intro r
      have h_disj_r : Disjoint ({r} : Finset (Fin p)) (Finset.univ \ {r}) :=
        Finset.disjoint_singleton_left.mpr (by simp)
      have h_pi_eq : Fintype.piFinset (fun _ : Fin p => P₀) =
          Fintype.piFinset (fun v : Fin p =>
            if v ∈ ({r} : Finset (Fin p)) then P₀ else if v ∈ Finset.univ \ {r} then P₀ else {γ_def}) := by
        congr 1; funext v; by_cases hvr : v = r <;> [subst hvr; skip] <;> simp [*]
      rw [h_pi_eq, piFinset_split_sum {r} (Finset.univ \ {r}) h_disj_r (fun _ => P₀) (fun _ => P₀) (fun _ => γ_def)]
      have h_KR_le : ∀ K_R ∈ Fintype.piFinset (fun v : Fin p => if v ∈ ({r} : Finset (Fin p)) then P₀ else {γ_def}),
          (∑ t ∈ Fintype.piFinset (fun v : Fin p => if v ∈ Finset.univ \ {r} then P₀ else {K_R v}),
            tupleTerm p r t) ≤
          if c ∈ worldlinePolymerNativeCollar sys C_RCA (K_R r) then
            (((p - 1).factorial : ℝ)) * (w (K_R r) * kpForestWeight P₀ incompat w p [K_R r]) else 0 := by
        intro K_R hK_R
        have h_tr_eq : ∀ t ∈ Fintype.piFinset (fun v : Fin p => if v ∈ Finset.univ \ {r} then P₀ else {K_R v}),
            tupleTerm p r t =
              if c ∈ worldlinePolymerNativeCollar sys C_RCA (K_R r) then
                ∑ f ∈ (arborescenceForests Finset.univ {r}).filter
                    (fun f => ∀ v ∈ (Finset.univ : Finset (Fin p)) \ {r}, incompat (t (f v)) (t v)),
                  w (K_R r) * ∏ v ∈ Finset.univ \ {r}, w (t v) else 0 := by
          intro t ht
          have htr : t r = K_R r := by simpa using Fintype.mem_piFinset.mp ht r
          dsimp [tupleTerm]; rw [htr]; split_ifs with hc_r
          · refine Finset.sum_congr rfl fun f _ => ?_
            have h_er : (Finset.univ : Finset (Fin p)).erase r = Finset.univ \ {r} := by ext v; simp
            rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ r), htr, h_er]
          · rfl
        rw [Finset.sum_congr rfl h_tr_eq]
        by_cases hc_r : c ∈ worldlinePolymerNativeCollar sys C_RCA (K_R r)
        · simp only [hc_r, if_true]
          have h_fps_eq : (∑ t ∈ Fintype.piFinset (fun v : Fin p => if v ∈ Finset.univ \ {r} then P₀ else {K_R v}),
              ∑ f ∈ (arborescenceForests Finset.univ {r}).filter
                  (fun f => ∀ v ∈ (Finset.univ : Finset (Fin p)) \ {r}, incompat (t (f v)) (t v)),
                w (K_R r) * ∏ v ∈ Finset.univ \ {r}, w (t v)) =
              w (K_R r) * forestPolymerSum P₀ incompat w Finset.univ {r} K_R := by
            unfold forestPolymerSum; simp only [Finset.sum_filter, Finset.mul_sum]; rw [Finset.sum_comm]
            refine Finset.sum_congr rfl fun f _ => Finset.sum_congr rfl fun t _ => ?_; split_ifs <;> ring
          rw [h_fps_eq]
          have h_fps_le := forestPolymerSum_le_kpForestWeight P₀ incompat hw p Finset.univ [r]
            (by simp) (List.nodup_singleton r) (Finset.subset_univ _) K_R
          have h_r_toFinset : ([r] : List (Fin p)).toFinset = {r} := rfl
          have h_sdiff_card : ((Finset.univ : Finset (Fin p)) \ {r}).card = p - 1 := by
            have h_er : (Finset.univ : Finset (Fin p)) \ {r} = Finset.univ.erase r := by ext v; simp
            rw [h_er, Finset.card_erase_of_mem (Finset.mem_univ r), Finset.card_univ, Fintype.card_fin]
          rw [h_r_toFinset, h_sdiff_card] at h_fps_le
          simpa [List.map_singleton, mul_left_comm, mul_assoc] using
            mul_le_mul_of_nonneg_left h_fps_le (abs_nonneg _)
        · simp [hc_r]
      have h_bij_r : (∑ K_R ∈ Fintype.piFinset (fun v : Fin p => if v ∈ ({r} : Finset (Fin p)) then P₀ else {γ_def}),
          if c ∈ worldlinePolymerNativeCollar sys C_RCA (K_R r) then
            (((p - 1).factorial : ℝ)) * (w (K_R r) * kpForestWeight P₀ incompat w p [K_R r]) else 0) =
          (((p - 1).factorial : ℝ)) * ∑ γ₀ ∈ T_c, w γ₀ * kpForestWeight P₀ incompat w p [γ₀] := by
        have h_bij : (∑ K_R ∈ Fintype.piFinset (fun v : Fin p => if v ∈ ({r} : Finset (Fin p)) then P₀ else {γ_def}),
            if c ∈ worldlinePolymerNativeCollar sys C_RCA (K_R r) then
              (((p - 1).factorial : ℝ)) * (w (K_R r) * kpForestWeight P₀ incompat w p [K_R r]) else 0) =
            ∑ γ₀ ∈ P₀, if c ∈ worldlinePolymerNativeCollar sys C_RCA γ₀ then
              (((p - 1).factorial : ℝ)) * (w γ₀ * kpForestWeight P₀ incompat w p [γ₀]) else 0 := by
          refine Finset.sum_bij (fun K_R _ => K_R r)
            (fun K_R hK_R => by simpa using (Fintype.mem_piFinset.mp hK_R) r) ?_ ?_ (fun _ _ => rfl)
          · intro K₁ hK₁ K₂ hK₂ h_eq; funext v; rcases eq_or_ne v r with rfl | hvr
            · exact h_eq
            · have h₁ := (Fintype.mem_piFinset.mp hK₁) v; have h₂ := (Fintype.mem_piFinset.mp hK₂) v
              simp only [Finset.mem_singleton, hvr, if_false] at h₁ h₂; exact h₁.trans h₂.symm
          · intro γ₀ hγ₀
            refine ⟨Function.update (fun _ => γ_def) r γ₀, Fintype.mem_piFinset.mpr fun v => ?_, by simp⟩
            rcases eq_or_ne v r with rfl | hvr <;> simp [*]
        rw [h_bij, Finset.mul_sum]; symm
        calc (∑ i ∈ T_c, (((p - 1).factorial : ℝ)) * (w i * kpForestWeight P₀ incompat w p [i]))
          _ = ∑ i ∈ T_c, if c ∈ worldlinePolymerNativeCollar sys C_RCA i then
                (((p - 1).factorial : ℝ)) * (w i * kpForestWeight P₀ incompat w p [i]) else 0 :=
              Finset.sum_congr rfl fun i hi => (if_pos (Finset.mem_filter.mp hi).2).symm
          _ = ∑ γ₀ ∈ P₀, if c ∈ worldlinePolymerNativeCollar sys C_RCA γ₀ then
                (((p - 1).factorial : ℝ)) * (w γ₀ * kpForestWeight P₀ incompat w p [γ₀]) else 0 :=
              Finset.sum_subset (Finset.filter_subset _ P₀) fun γ₀ hγ₀ h_not =>
                if_neg (fun hc => h_not (Finset.mem_filter.mpr ⟨hγ₀, hc⟩))
      exact le_trans (Finset.sum_le_sum h_KR_le) (le_of_eq h_bij_r)
    have h_fac_p : ((p.factorial : ℝ)⁻¹) * ((p : ℝ) * (((p - 1).factorial : ℝ))) = 1 := by
      have h_cast : (p : ℝ) * (((p - 1).factorial : ℝ)) = (p.factorial : ℝ) := by
        exact_mod_cast Nat.mul_factorial_pred (Nat.ne_of_gt hp_pos)
      rw [h_cast, inv_mul_cancel₀ (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero p))]
    calc (∑ K ∈ ℱ_val.filter (fun K => K.length = p),
          pinnedCollarClusterAbsWeight D_field sys C_RCA R_cut β V d_loc ν σ c K)
      _ ≤ ∑ t ∈ Fintype.piFinset (fun _ : Fin p => P₀), tupleBound p t := h_step1
      _ = ((p.factorial : ℝ)⁻¹) * ∑ r : Fin p, ∑ t ∈ Fintype.piFinset (fun _ : Fin p => P₀), tupleTerm p r t := by
          dsimp [tupleBound]; rw [← Finset.mul_sum, Finset.sum_comm]
      _ ≤ ((p.factorial : ℝ)⁻¹) * ∑ _r : Fin p,
          (((p - 1).factorial : ℝ)) * ∑ γ₀ ∈ T_c, w γ₀ * kpForestWeight P₀ incompat w p [γ₀] :=
          mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun r _ => h_r_bound r) (inv_nonneg.mpr (Nat.cast_nonneg _))
      _ = (((p.factorial : ℝ)⁻¹) * ((p : ℝ) * (((p - 1).factorial : ℝ)))) *
          ∑ γ₀ ∈ T_c, w γ₀ * kpForestWeight P₀ incompat w p [γ₀] := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; ring
      _ = ∑ γ₀ ∈ T_c, w γ₀ * kpForestWeight P₀ incompat w p [γ₀] := by rw [h_fac_p, one_mul]
  rw [h_sum_val, h_part_P, Finset.sum_biUnion h_disj_P]
  calc (∑ p ∈ Finset.Icc 1 P, ∑ K ∈ ℱ_val.filter (fun K => K.length = p),
        pinnedCollarClusterAbsWeight D_field sys C_RCA R_cut β V d_loc ν σ c K)
    _ ≤ ∑ p ∈ Finset.Icc 1 P, ∑ γ₀ ∈ T_c, w γ₀ * kpForestWeight P₀ incompat w p [γ₀] :=
        Finset.sum_le_sum h_p_sum_le
    _ = ∑ γ₀ ∈ T_c, w γ₀ * ∑ p ∈ Finset.Icc 1 P, kpForestWeight P₀ incompat w p [γ₀] := by
        rw [Finset.sum_comm]; exact Finset.sum_congr rfl fun γ₀ _ => (Finset.mul_sum _ _ _).symm
    _ ≤ ∑ γ₀ ∈ T_c, w γ₀ * Real.exp (a γ₀) := by
        refine Finset.sum_le_sum fun γ₀ hγ₀ => mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
        have h_icc_eq : Finset.Icc 1 P = (Finset.range P).image (· + [γ₀].length) := by
          ext p; simp only [Finset.mem_Icc, Finset.mem_image, Finset.mem_range, List.length_singleton]
          exact ⟨fun hp => ⟨p - 1, by omega, by omega⟩, fun ⟨n, hn, hnp⟩ => by omega⟩
        have h_reidx : (∑ p ∈ Finset.Icc 1 P, kpForestWeight P₀ incompat w p [γ₀]) ≤
            ∑ n ∈ Finset.range (P + 1), kpForestWeight P₀ incompat w (n + [γ₀].length) [γ₀] := by
          rw [h_icc_eq, Finset.sum_image (fun x _ y _ h => Nat.add_right_cancel h)]
          exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono (Nat.le_succ P))
            (fun n _ _ => kpForestWeight_nonneg P₀ incompat hw (n + [γ₀].length) [γ₀])
        have h_deg := sum_kpDegWeight_le_exp P₀ incompat hw ha h_kp_a P [γ₀]
          (by intro γ hγ; rcases List.mem_singleton.mp hγ with rfl; exact (Finset.mem_filter.mp hγ₀).1)
        simpa using le_trans h_reidx h_deg
    _ ≤ 1 / 8 := h_root_sum

/-- **Mayer–Ursell Cluster Logarithm Identity for the Polymer Partition Function** (Part II, Section 3.5 (`subsec:worldline-expansion`), Lemma 3.9 (`lem:worldline-factorization-time-reversal`), and Proposition 3.10 (`prop:tube-local-ursell-erasure`), Equation `eq:ursell-partition-sigma`): Under the Kotecký–Preiss (1986) convergence hypotheses, the polymer-gas partition function `worldlineMayerPolymerPartition D_field sys C_RCA R_cut β V d_loc ν σ` in each joint syndrome-logical sector $(\sigma, \nu)$ equals the exponential of the finite-cutoff Mayer–Ursell cluster sum `∑ γ ∈ worldlineUrsellIndexFinset L q_code m_max R_cut, worldlineUrsellPhi ... ν γ σ`. -/
theorem worldline_mayer_ursell_cluster_log_identity
    {L q_code r_0 m_max w_0 L_star R_cut : ℕ} [NeZero L]
    {C_RCA β Δ_RCA C_wl c_wl J : ℝ}
    (D_field : Box3D L → LocalCSSDescriptor q_code r_0 m_max) (h_valid : ValidDescriptorField D_field)
    (sys : SysCSS[L, q_code, m_max])
    (h_sys_checks : ∀ idx, sys.checkProj idx = staticCSSCheckProj D_field idx ∧
      sys.support idx = staticCSSCheckSupport D_field idx ∧ sys.weight idx = 1)
    (h_geom : sys.IsGeometricallyLocal r_0 w_0)
    (h_tqo1 : SatisfiesTQO1 sys L_star) (h_tqo2 : SatisfiesSectorFilteredLinearTQO2 sys 1 L_star C_RCA)
    (V : QuasiLocalPerturbation 3 L (SiteCSS[L, q_code])) (f : ℕ → ℝ)
    (hf_nn : ∀ r, 0 ≤ f r) (hf_le_one : ∀ r, f r ≤ 1)
    (hV_norm : ∀ r ∈ Finset.Icc 1 (min R_cut L), ∀ A ∈ boxCubes 3 L r, ‖V.term r A‖ ≤ J * f r)
    (e_loc : ℕ → Finset (Box3D L) → ℝ)
    (d_loc : ℕ → Finset (Box3D L) → (IdxCSS[L, q_code, m_max] → Bool) → ℝ)
    (hd_scale : ∀ r ∈ Finset.Icc 1 (min R_cut L), ∀ A ∈ boxCubes 3 L r,
      ∀ σ, |d_loc r A σ| ≤ 2 * (J * f r))
    (h_scalar : IsLocalCollarScalarFamily D_field sys R_cut C_RCA J V e_loc d_loc)
    (hH_trunc : IsSelfAdjoint (sys.H0 + scaleSplitTruncatedOp V R_cut))
    (hR_cut : 1 ≤ R_cut) (hR_le : R_cut ≤ L_star)
    (h_scale_cal : SatisfiesWorldlineScaleCalibration L L_star R_cut r_0 C_RCA) (hC_RCA : 0 ≤ C_RCA)
    (h_rca_cal : rcaDiagonalCoercivityConstant 3 R_cut r_0 w_0 C_RCA ≤ Δ_RCA)
    (hC_wl_cal : (kpCollarMaxCheckCard R_cut r_0 w_0 C_RCA : ℝ) ≤ C_wl)
    (hc_wl_cal : (kpCollarMaxCheckCard R_cut r_0 w_0 C_RCA : ℝ) ≤ c_wl)
    (hΔ_RCA : 0 < Δ_RCA) (hβ : 16 < β) (hJ : 0 ≤ J)
    (h_sum_pos : 0 < worldlineNativeKPSum f C_wl c_wl β R_cut)
    (hJ_walsh : J ≤ collarWalshCouplingThreshold R_cut r_0 w_0 C_RCA)
    (hJ_wl : J ≤ worldlineCouplingThreshold (1 / 4) Δ_RCA)
    (h_thresh : J ≤ worldlineSpanningThreshold Δ_RCA C_wl c_wl β f R_cut)
    (ν : PauliBitstringPair L q_code)
    {σ : IdxCSS[L, q_code, m_max] → Bool}
    (hσ : σ ∈ realizableSyndromes D_field) :
    worldlineMayerPolymerPartition D_field sys C_RCA R_cut β V d_loc ν σ =
      Real.exp (∑ γ ∈ worldlineUrsellIndexFinset L q_code m_max R_cut,
        worldlineUrsellPhi D_field sys C_RCA R_cut β V d_loc ν γ σ) := by
  have h_kp := worldline_polymer_native_collar_kp_bound D_field sys h_sys_checks h_geom V
    hf_nn hV_norm d_loc hd_scale hR_cut hC_RCA hC_wl_cal hc_wl_cal hβ hJ h_sum_pos h_thresh ν σ
  have h_poly_sum : Summable (fun γ : WorldlineDysonPolymer L q_code =>
      if IsValidWorldlinePolymer D_field sys C_RCA R_cut γ then
        |worldlinePolymerWeight D_field sys C_RCA β V d_loc ν γ σ| else 0) := by
    let g_u (u₁ : IdxCSS[L, q_code, m_max]) (γ : WorldlineDysonPolymer L q_code) : ℝ :=
      if IsValidWorldlinePolymer D_field sys C_RCA R_cut γ ∧
          u₁ ∈ worldlinePolymerNativeCollar sys C_RCA γ then
        |worldlinePolymerWeight D_field sys C_RCA β V d_loc ν γ σ| *
          Real.exp ((1 / 8 : ℝ) * ((worldlinePolymerNativeCollar sys C_RCA γ).card : ℝ))
      else 0
    have hg_u_nn : ∀ u₁ γ, 0 ≤ g_u u₁ γ := fun u₁ γ => by dsimp [g_u]; split_ifs <;> positivity
    have h_sum_u : Summable (fun γ => ∑ u₁ : IdxCSS[L, q_code, m_max], g_u u₁ γ) :=
      summable_sum fun u₁ _ => (h_kp u₁).1
    refine h_sum_u.of_nonneg_of_le (fun γ => by split_ifs <;> positivity) (fun γ => ?_)
    split_ifs with hγ
    · rcases (worldlinePolymerNativeCollar_nonempty_of_valid D_field sys
          (fun idx => (h_sys_checks idx).2.1) h_geom h_scale_cal.2.1 hγ).1 with ⟨u₀, hu₀⟩
      have h_le_exp : |worldlinePolymerWeight D_field sys C_RCA β V d_loc ν γ σ| ≤ g_u u₀ γ := by
        dsimp [g_u]; rw [if_pos ⟨hγ, hu₀⟩]
        exact le_mul_of_one_le_right (abs_nonneg _) (Real.one_le_exp (by positivity))
      exact le_trans h_le_exp (Finset.single_le_sum (fun u₁ _ => hg_u_nn u₁ γ) (Finset.mem_univ u₀))
    · exact Finset.sum_nonneg fun u₁ _ => hg_u_nn u₁ γ
  have h_ursell_sum : Summable (fun K : WorldlineUrsellCluster L q_code =>
      if IsValidWorldlineUrsellCluster D_field sys C_RCA R_cut K then
        |worldlineClusterUrsellWeight D_field sys C_RCA β V d_loc ν K σ| else 0) := by
    have h_pin_sum : ∀ c : IdxCSS[L, q_code, m_max],
        Summable (pinnedCollarClusterAbsWeight D_field sys C_RCA R_cut β V d_loc ν σ c) := fun c =>
      summable_of_sum_le (pinnedCollarClusterAbsWeight_nonneg D_field sys C_RCA R_cut β V d_loc ν σ c)
        (sum_pinnedCollarClusterAbsWeight_le_of_kp D_field sys V d_loc ν σ h_kp c)
    have h_sum_c : Summable (fun K : WorldlineUrsellCluster L q_code =>
        ∑ c : IdxCSS[L, q_code, m_max],
          pinnedCollarClusterAbsWeight D_field sys C_RCA R_cut β V d_loc ν σ c K) :=
      summable_sum fun c _ => h_pin_sum c
    refine h_sum_c.of_nonneg_of_le (fun K => by split_ifs <;> positivity) (fun K => ?_)
    split_ifs with hK
    · rcases List.exists_mem_of_ne_nil K hK.1 with ⟨γ₀, hγ₀⟩
      rcases (worldlinePolymerNativeCollar_nonempty_of_valid D_field sys
          (fun idx => (h_sys_checks idx).2.1) h_geom h_scale_cal.2.1 (hK.2.1 γ₀ hγ₀)).1 with ⟨c₀, hc₀⟩
      have h_eq : |worldlineClusterUrsellWeight D_field sys C_RCA β V d_loc ν K σ| =
          pinnedCollarClusterAbsWeight D_field sys C_RCA R_cut β V d_loc ν σ c₀ K := by
        unfold pinnedCollarClusterAbsWeight
        exact (if_pos ⟨hK, γ₀, hγ₀, hc₀⟩).symm
      exact h_eq.le.trans (Finset.single_le_sum
        (fun c _ => pinnedCollarClusterAbsWeight_nonneg D_field sys C_RCA R_cut β V d_loc ν σ c K)
        (Finset.mem_univ c₀))
    · exact Finset.sum_nonneg fun c _ =>
        pinnedCollarClusterAbsWeight_nonneg D_field sys C_RCA R_cut β V d_loc ν σ c K
  exact worldlineMayerPolymerPartition_eq_exp_of_summable D_field sys C_RCA β V d_loc ν σ
    h_poly_sum h_ursell_sum

end DirectWorldlineCluster
end
