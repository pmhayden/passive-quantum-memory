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

import Proofs.DirectWorldlineCluster.WorldlineClusterDefs
import Proofs.SpacetimeWorldlineKP.SpacetimeCollarWalshPositivity
import Proofs.SpacetimeWorldlineKP.BoltzmannOperatorDuhamelIntegral

/-!
# Super-Polynomial Scale-Split Truncation and Pauli-Diagonal Walsh–Hadamard Peeling

Bounds the super-polynomial RCA collar constant (`rcaCollarConstant_le_pi_sq_div_six_mul_moment5`), proves the Duhamel–Weyl relative partition ratio inequality (`duhamelWeyl_relative_partition_ratio_bound`), and establishes the scale-split decomposition separating short-range interactions from the long-range tail (`superpolynomial_collar_and_scale_split_decomp`). Also proves the temperature-independent Pauli-diagonal witness coset peeling bound (`pauli_diagonal_witness_peeling_gibbs_bound`) via Walsh–Hadamard positivity.

## References

* Part II, Section 3.3 (`subsec:walsh-coset-peeling`), Proposition 3.8 (`prop:diagonal-peeling`)
* Part II, Section 3.1 (`subsec:weyl-witness-poisson`), Lemma 3.1 (`lem:duhamel-weyl-ratio`)
* Part II, Section 3.3 (`subsec:walsh-coset-peeling`), Proposition 3.6 (`prop:walsh-coset-dominance`)
-/

noncomputable section

open scoped Classical BigOperators InnerProduct ComplexConjugate
open Filter Topology Asymptotics ContinuousLinearMap KMSPinchedGibbs PerturbedThermalBarrier
open SpacetimeWorldlineKP

namespace DirectWorldlineCluster

local notation "ℋ[" L ", " Site0 "]" => ManyBodyHilbertSpace (UniformSite3D L Site0)
local notation "ℬ[" L ", " Site0 "]" => ℋ[L, Site0] →L[ℂ] ℋ[L, Site0]
local notation "ℋ_CP[" L ", " Site0 ", " N_checks "]" =>
  IndexedCommutingProjectorHamiltonian 3 L (UniformSite3D L Site0) (Fin N_checks)
local notation "𝒱_pert[" L ", " Site0 "]" =>
  QuasiLocalPerturbation 3 L (UniformSite3D L Site0)

private def collarMajorantSeq (r : ℕ) : ℝ :=
  if r = 0 then 1 else if r = 1 then 1 / 32 else 1 / (1 + (r : ℝ)) ^ 2

private lemma summable_and_tsum_collarMajorantSeq_le :
    Summable collarMajorantSeq ∧
    (∑' r : ℕ, collarMajorantSeq r) ≤ Real.pi ^ 2 / 6 := by
  have h_nn : ∀ r : ℕ, 0 ≤ collarMajorantSeq r := by
    intro r; unfold collarMajorantSeq
    split_ifs <;> positivity
  have h_tail_step : ∀ k : ℕ,
      collarMajorantSeq (2 + k) ≤
        1 / ((k : ℝ) + 5 / 2) - 1 / (((k + 1 : ℕ) : ℝ) + 5 / 2) := by
    intro k
    have h_eq : collarMajorantSeq (2 + k) = 1 / (1 + ((2 + k : ℕ) : ℝ)) ^ 2 := by
      unfold collarMajorantSeq
      rw [if_neg (by omega), if_neg (by omega)]
    rw [h_eq]
    push_cast
    have hk1 : (0 : ℝ) < (k : ℝ) + 5 / 2 := by positivity
    have hk2 : (0 : ℝ) < (k : ℝ) + 1 + 5 / 2 := by positivity
    have hk3 : (0 : ℝ) < (1 + (2 + (k : ℝ))) ^ 2 := by positivity
    rw [div_sub_div _ _ (ne_of_gt hk1) (ne_of_gt hk2), div_le_div_iff₀ hk3 (mul_pos hk1 hk2)]
    nlinarith
  have h_partial : ∀ N : ℕ,
      (∑ r ∈ Finset.range N, collarMajorantSeq r) ≤ Real.pi ^ 2 / 6 := by
    intro N
    have h_sub : Finset.range N ⊆ Finset.range (2 + N) :=
      Finset.range_mono (Nat.le_add_left N 2)
    have h1 : (∑ r ∈ Finset.range N, collarMajorantSeq r) ≤
        ∑ r ∈ Finset.range (2 + N), collarMajorantSeq r :=
      Finset.sum_le_sum_of_subset_of_nonneg h_sub (fun r _ _ => h_nn r)
    rw [Finset.sum_range_add] at h1
    have h2 : (∑ k ∈ Finset.range N, collarMajorantSeq (2 + k)) ≤
        ∑ k ∈ Finset.range N, (1 / ((k : ℝ) + 5 / 2) - 1 / (((k + 1 : ℕ) : ℝ) + 5 / 2)) :=
      Finset.sum_le_sum fun k _ => h_tail_step k
    have h_tele := Finset.sum_range_sub' (fun k : ℕ => 1 / ((k : ℝ) + 5 / 2)) N
    rw [h_tele] at h2
    have h_rem_nn : 0 ≤ 1 / ((N : ℝ) + 5 / 2) := by positivity
    have h_head : (∑ x ∈ Finset.range 2, collarMajorantSeq x) +
        1 / ((0 : ℕ) + 5 / 2 : ℝ) ≤ (3 : ℝ) ^ 2 / 6 := by
      simp only [Finset.sum_range_succ, Finset.sum_range_zero, collarMajorantSeq,
         ↓reduceIte, one_ne_zero, Nat.cast_zero]
      norm_num
    have h_pi : (3 : ℝ) ^ 2 / 6 ≤ Real.pi ^ 2 / 6 := by
      have h_gt : (3 : ℝ) ≤ Real.pi := by
        by_contra! h_lt
        have h_le : Real.sin (Real.pi / 6) ≤ Real.sin (1 / 2) :=
          Real.sin_le_sin_of_le_of_le_pi_div_two
            (by linarith [Real.two_le_pi]) (by linarith [Real.two_le_pi]) (by linarith)
        have h_sb := (abs_sub_le_iff.mp (Real.sin_bound (x := 1 / 2) (by norm_num))).1
        rw [Real.sin_pi_div_six] at h_le
        rw [abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)] at h_sb
        linarith
      nlinarith
    linarith
  have h_sum : Summable collarMajorantSeq :=
    summable_of_sum_range_le h_nn h_partial
  exact ⟨h_sum, h_sum.tsum_le_of_sum_range_le h_partial⟩

/-- **Super-Polynomial Collar and Tail Moment Bounds (`rcaCollarConstant_le_pi_sq_div_six_mul_moment5`, Part II, Lemma 2.4 (`lem:D-super-closure`))**:
Under `HasDecayMomentBound f 5 M_5` with `1 ≤ c_chk`, `1 ≤ r_0`, and `0 ≤ C_RCA`:
1. For every `r : ℕ`, the active check footprint of the RCA collar ball of radius
   `rcaCollarRadius C_RCA r_0 r` is bounded by `rcaCollarEnvelopeConst c_chk r_0 C_RCA * (1 + r)^3`.
2. The RCA collar series `rcaCollarSeries f c_chk r_0 C_RCA` is bounded by
   `(Real.pi ^ 2 / 6) * rcaCollarEnvelopeConst c_chk r_0 C_RCA * M_5`.
3. For every cutoff `R_cut ≥ 1`, the tail series `perturbationTailSeries f R_cut` is bounded by
   `(Real.pi ^ 2 / 6) * M_5 / (R_cut : ℝ) ^ 3`.
4. If `InPerturbationClassFin f r_pert` and `r_pert ≤ R_cut`, then `perturbationTailSeries f R_cut = 0`. -/
theorem rcaCollarConstant_le_pi_sq_div_six_mul_moment5
    (f : ℕ → ℝ) (c_chk r_0 : ℕ) (C_RCA M_5 : ℝ)
    (hc_chk : 1 ≤ c_chk) (hr_0 : 1 ≤ r_0) (hC_RCA : 0 ≤ C_RCA)
    (hM5 : HasDecayMomentBound f 5 M_5) :
    (∀ r : ℕ,
      (activeCheckFootprintBound c_chk r_0 (rcaCollarRadius C_RCA r_0 r) : ℝ) ≤
        rcaCollarEnvelopeConst c_chk r_0 C_RCA * ((1 + (r : ℝ)) ^ 3)) ∧
    (∀ L_star : ℕ,
      rcaCollarFiniteSum f c_chk r_0 L_star C_RCA ≤
        rcaCollarSeries f c_chk r_0 C_RCA) ∧
    rcaCollarSeries f c_chk r_0 C_RCA ≤
      (Real.pi ^ 2 / 6) * rcaCollarEnvelopeConst c_chk r_0 C_RCA * M_5 ∧
    (∀ R_cut : ℕ, 1 ≤ R_cut →
      perturbationTailSeries f R_cut ≤ (Real.pi ^ 2 / 6) * M_5 / ((R_cut : ℝ) ^ 3)) ∧
    (∀ r_pert R_cut : ℕ, InPerturbationClassFin f r_pert → r_pert ≤ R_cut →
      perturbationTailSeries f R_cut = 0) := by
  have hr0_ge : (1 : ℝ) ≤ (r_0 : ℝ) := by exact_mod_cast hr_0
  have hc_nn : (0 : ℝ) ≤ (c_chk : ℝ) := Nat.cast_nonneg c_chk
  have hM5_nn : 0 ≤ M_5 := by
    have h0 := hM5.2.2 0
    rw [Nat.cast_zero, add_zero, one_pow, one_mul, hM5.2.1] at h0
    linarith
  have h_part1 : ∀ r : ℕ,
      (activeCheckFootprintBound c_chk r_0 (rcaCollarRadius C_RCA r_0 r) : ℝ) ≤
        rcaCollarEnvelopeConst c_chk r_0 C_RCA * ((1 + (r : ℝ)) ^ 3) := by
    intro r
    unfold activeCheckFootprintBound rcaCollarRadius rcaCollarEnvelopeConst
    push_cast
    have hr_nn : (0 : ℝ) ≤ (r : ℝ) := Nat.cast_nonneg r
    have h_max_nn : (0 : ℝ) ≤ max (r : ℝ) (r_0 : ℝ) := by positivity
    have h_max_le : max (r : ℝ) (r_0 : ℝ) ≤ (r_0 : ℝ) * (1 + (r : ℝ)) :=
      max_le (by nlinarith) (by nlinarith)
    have h_ceil_lt := Nat.ceil_lt_add_one (mul_nonneg hC_RCA h_max_nn)
    have h_rad_le : (Nat.ceil (C_RCA * max (r : ℝ) (r_0 : ℝ)) : ℝ) + (r_0 : ℝ) ≤
        (C_RCA * (r_0 : ℝ) + (r_0 : ℝ) + 1) * (1 + (r : ℝ)) := by
      have h_cm : C_RCA * max (r : ℝ) (r_0 : ℝ) ≤ C_RCA * ((r_0 : ℝ) * (1 + (r : ℝ))) :=
        mul_le_mul_of_nonneg_left h_max_le hC_RCA
      nlinarith
    have h_pow_le : ((Nat.ceil (C_RCA * max (r : ℝ) (r_0 : ℝ)) : ℝ) + (r_0 : ℝ)) ^ 3 ≤
        ((C_RCA * (r_0 : ℝ) + (r_0 : ℝ) + 1) * (1 + (r : ℝ))) ^ 3 :=
      pow_le_pow_left₀ (by positivity) h_rad_le 3
    calc (c_chk : ℝ) * ((Nat.ceil (C_RCA * max (r : ℝ) (r_0 : ℝ)) : ℝ) + (r_0 : ℝ)) ^ 3
      _ ≤ (c_chk : ℝ) * (((C_RCA * (r_0 : ℝ) + (r_0 : ℝ) + 1) * (1 + (r : ℝ))) ^ 3) :=
          mul_le_mul_of_nonneg_left h_pow_le hc_nn
      _ = (c_chk : ℝ) * (C_RCA * (r_0 : ℝ) + (r_0 : ℝ) + 1) ^ 3 * (1 + (r : ℝ)) ^ 3 := by ring
  have h_env_nn : 0 ≤ rcaCollarEnvelopeConst c_chk r_0 C_RCA := by
    unfold rcaCollarEnvelopeConst
    positivity
  obtain ⟨h_zeta_sum, h_zeta_le⟩ := summable_and_tsum_collarMajorantSeq_le
  have h_lhs_sum_and_le :
      Summable (fun r : ℕ =>
        f r * (activeCheckFootprintBound c_chk r_0 (rcaCollarRadius C_RCA r_0 r) : ℝ)) ∧
      rcaCollarSeries f c_chk r_0 C_RCA ≤
        (Real.pi ^ 2 / 6) * rcaCollarEnvelopeConst c_chk r_0 C_RCA * M_5 := by
    unfold rcaCollarSeries
    let C_top := rcaCollarEnvelopeConst c_chk r_0 C_RCA * M_5
    have hC_top_nn : 0 ≤ C_top := mul_nonneg h_env_nn hM5_nn
    have h_term_le : ∀ r : ℕ,
        f r * (activeCheckFootprintBound c_chk r_0 (rcaCollarRadius C_RCA r_0 r) : ℝ) ≤
          C_top * collarMajorantSeq r := by
      intro r
      unfold collarMajorantSeq
      split_ifs with hr0 hr1
      · subst hr0
        have hp0 := h_part1 0
        rw [Nat.cast_zero, add_zero, one_pow, mul_one] at hp0
        have hf0 : f 0 ≤ M_5 := by
          have := hM5.2.2 0
          rwa [Nat.cast_zero, add_zero, one_pow, one_mul] at this
        calc f 0 * (activeCheckFootprintBound c_chk r_0 (rcaCollarRadius C_RCA r_0 0) : ℝ)
          _ ≤ M_5 * rcaCollarEnvelopeConst c_chk r_0 C_RCA :=
              mul_le_mul hf0 hp0 (Nat.cast_nonneg _) hM5_nn
          _ = C_top * 1 := by dsimp [C_top]; ring
      · subst hr1
        have h_rad1 : rcaCollarRadius C_RCA r_0 1 = rcaCollarRadius C_RCA r_0 0 := by
          unfold rcaCollarRadius
          rw [Nat.cast_one, Nat.cast_zero, max_eq_right hr0_ge,
            max_eq_right (le_trans zero_le_one hr0_ge)]
        have hp1 : (activeCheckFootprintBound c_chk r_0 (rcaCollarRadius C_RCA r_0 1) : ℝ) ≤
            rcaCollarEnvelopeConst c_chk r_0 C_RCA := by
          rw [h_rad1]
          have hp0 := h_part1 0
          rwa [Nat.cast_zero, add_zero, one_pow, mul_one] at hp0
        have hf1 : f 1 ≤ M_5 * (1 / 32) := by
          have h5 := hM5.2.2 1
          rw [Nat.cast_one] at h5
          linarith
        calc f 1 * (activeCheckFootprintBound c_chk r_0 (rcaCollarRadius C_RCA r_0 1) : ℝ)
          _ ≤ (M_5 * (1 / 32)) * rcaCollarEnvelopeConst c_chk r_0 C_RCA :=
              mul_le_mul hf1 hp1 (Nat.cast_nonneg _) (by positivity)
          _ = C_top * (1 / 32) := by dsimp [C_top]; ring
      · have hr_pos : 0 < 1 + (r : ℝ) := by positivity
        have h_f_step : ((1 + (r : ℝ)) ^ 3) * f r ≤ M_5 * (1 / (1 + (r : ℝ)) ^ 2) := by
          have h5 := hM5.2.2 r
          have h_sq_pos : 0 < (1 + (r : ℝ)) ^ 2 := by positivity
          rw [mul_one_div, le_div_iff₀ h_sq_pos]
          calc ((1 + (r : ℝ)) ^ 3) * f r * (1 + (r : ℝ)) ^ 2
            _ = ((1 + (r : ℝ)) ^ 5) * f r := by ring
            _ ≤ M_5 := h5
        calc f r * (activeCheckFootprintBound c_chk r_0 (rcaCollarRadius C_RCA r_0 r) : ℝ)
          _ ≤ f r * (rcaCollarEnvelopeConst c_chk r_0 C_RCA * ((1 + (r : ℝ)) ^ 3)) :=
              mul_le_mul_of_nonneg_left (h_part1 r) (hM5.1 r)
          _ = rcaCollarEnvelopeConst c_chk r_0 C_RCA * (((1 + (r : ℝ)) ^ 3) * f r) := by ring
          _ ≤ rcaCollarEnvelopeConst c_chk r_0 C_RCA * (M_5 * (1 / (1 + (r : ℝ)) ^ 2)) :=
              mul_le_mul_of_nonneg_left h_f_step h_env_nn
          _ = C_top * (1 / (1 + (r : ℝ)) ^ 2) := by dsimp [C_top]; ring
    have h_lhs_sum : Summable (fun r : ℕ =>
        f r * (activeCheckFootprintBound c_chk r_0 (rcaCollarRadius C_RCA r_0 r) : ℝ)) :=
      Summable.of_nonneg_of_le (fun r => mul_nonneg (hM5.1 r) (Nat.cast_nonneg _))
        h_term_le (h_zeta_sum.mul_left C_top)
    refine ⟨h_lhs_sum, ?_⟩
    calc (∑' r : ℕ, f r * (activeCheckFootprintBound c_chk r_0 (rcaCollarRadius C_RCA r_0 r) : ℝ))
      _ ≤ ∑' r : ℕ, C_top * collarMajorantSeq r :=
          h_lhs_sum.tsum_le_tsum h_term_le (h_zeta_sum.mul_left C_top)
      _ = C_top * (∑' r : ℕ, collarMajorantSeq r) := tsum_mul_left
      _ ≤ C_top * (Real.pi ^ 2 / 6) := mul_le_mul_of_nonneg_left h_zeta_le hC_top_nn
      _ = (Real.pi ^ 2 / 6) * rcaCollarEnvelopeConst c_chk r_0 C_RCA * M_5 := by
          dsimp [C_top]; ring
  refine ⟨h_part1, ?_, h_lhs_sum_and_le.2, ?_, ?_⟩
  · intro L_star
    unfold rcaCollarFiniteSum rcaCollarSeries
    exact h_lhs_sum_and_le.1.sum_le_tsum (Finset.Icc 1 L_star)
      (fun r _ => mul_nonneg (hM5.1 r) (Nat.cast_nonneg _))
  · intro R_cut hR_cut
    unfold perturbationTailSeries
    let C_tail := M_5 / ((R_cut : ℝ) ^ 3)
    have hR_pos : (0 : ℝ) < (R_cut : ℝ) := by exact_mod_cast (Nat.succ_le_iff.mp hR_cut)
    have hC_tail_nn : 0 ≤ C_tail := div_nonneg hM5_nn (by positivity)
    have h_term_le : ∀ r : ℕ,
        (if R_cut < r then f r else 0) ≤ C_tail * collarMajorantSeq r := by
      intro r
      split_ifs with hr
      · have hr_ge2 : 2 ≤ r := by omega
        have h_maj_eq : collarMajorantSeq r = 1 / (1 + (r : ℝ)) ^ 2 := by
          unfold collarMajorantSeq
          rw [if_neg (by omega), if_neg (by omega)]
        rw [h_maj_eq]
        have hr_le : (R_cut : ℝ) ≤ 1 + (r : ℝ) := by
          have : R_cut + 1 ≤ r := hr
          have : (R_cut : ℝ) + 1 ≤ (r : ℝ) := by exact_mod_cast this
          linarith
        have h_pow3 : (R_cut : ℝ) ^ 3 ≤ (1 + (r : ℝ)) ^ 3 :=
          pow_le_pow_left₀ (le_of_lt hR_pos) hr_le 3
        have h_prod_pos : 0 < ((R_cut : ℝ) ^ 3) * ((1 + (r : ℝ)) ^ 2) := by positivity
        have h_f_mul : f r * (((R_cut : ℝ) ^ 3) * ((1 + (r : ℝ)) ^ 2)) ≤ M_5 := by
          calc f r * (((R_cut : ℝ) ^ 3) * ((1 + (r : ℝ)) ^ 2))
            _ ≤ f r * (((1 + (r : ℝ)) ^ 3) * ((1 + (r : ℝ)) ^ 2)) := by
                refine mul_le_mul_of_nonneg_left ?_ (hM5.1 r)
                exact mul_le_mul_of_nonneg_right h_pow3 (by positivity)
            _ = ((1 + (r : ℝ)) ^ 5) * f r := by ring
            _ ≤ M_5 := hM5.2.2 r
        dsimp [C_tail]
        rw [div_mul_div_comm, mul_one, le_div_iff₀ h_prod_pos]
        exact h_f_mul
      · have h_maj_nn : 0 ≤ collarMajorantSeq r := by
          unfold collarMajorantSeq; split_ifs <;> positivity
        exact mul_nonneg hC_tail_nn h_maj_nn
    have h_lhs_sum : Summable (fun r : ℕ => if R_cut < r then f r else 0) :=
      Summable.of_nonneg_of_le (fun r => by split_ifs <;> [exact hM5.1 r; exact le_rfl])
        h_term_le (h_zeta_sum.mul_left C_tail)
    calc (∑' r : ℕ, if R_cut < r then f r else 0)
      _ ≤ ∑' r : ℕ, C_tail * collarMajorantSeq r :=
          h_lhs_sum.tsum_le_tsum h_term_le (h_zeta_sum.mul_left C_tail)
      _ = C_tail * (∑' r : ℕ, collarMajorantSeq r) := tsum_mul_left
      _ ≤ C_tail * (Real.pi ^ 2 / 6) := mul_le_mul_of_nonneg_left h_zeta_le hC_tail_nn
      _ = (Real.pi ^ 2 / 6) * M_5 / ((R_cut : ℝ) ^ 3) := by
          dsimp [C_tail]; ring
  · intro r_pert R_cut h_fin hr_le
    unfold perturbationTailSeries
    have h_zero : (fun r : ℕ => if R_cut < r then f r else 0) = fun _ => 0 := by
      funext r
      split_ifs with hr
      · exact h_fin.2 r (lt_of_le_of_lt hr_le hr)
      · rfl
    rw [h_zero, tsum_zero]

private lemma sortedEigenvalues_le_add_norm_sub_local {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    (H1 H2 : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site)
    (hH1 : IsSelfAdjoint H1) (hH2 : IsSelfAdjoint H2)
    (i : Fin (Module.finrank ℂ (ManyBodyHilbertSpace Site))) :
    sortedEigenvalues H1 hH1 i ≤ sortedEigenvalues H2 hH2 i + ‖H1 - H2‖ := by
  let W := eigenSpanBelow H2 hH2 (i.1 + 1)
  let U_orth := (eigenSpanBelow H1 hH1 i.1)ᗮ
  have hW_dim : Module.finrank ℂ W = i.1 + 1 := finrank_eigenSpanBelow H2 hH2 (i.1 + 1) i.2
  have h_dim_E1 : Module.finrank ℂ (eigenSpanBelow H1 hH1 i.1) = i.1 :=
    finrank_eigenSpanBelow H1 hH1 i.1 (le_of_lt i.2)
  have h_orth := (eigenSpanBelow H1 hH1 i.1).finrank_add_finrank_orthogonal
  have h_dim_lt : Module.finrank ℂ (ManyBodyHilbertSpace Site) <
      Module.finrank ℂ W + Module.finrank ℂ U_orth := by dsimp [U_orth]; omega
  rcases exists_ne_zero_mem_inf_of_finrank_lt_add W U_orth h_dim_lt with ⟨ψ, hψW, hψU, hψ_ne⟩
  have h_H2_le : RCLike.re (inner ℂ ψ (H2 ψ)) ≤ sortedEigenvalues H2 hH2 i * ‖ψ‖ ^ 2 := by
    apply re_inner_apply_H_le_of_mem_eigenSpanBelow H2 hH2 (i.1 + 1) (sortedEigenvalues H2 hH2 i) _ hψW
    intro j hj; exact sortedEigenvalues_monotone_bhm H2 hH2 (Nat.lt_succ_iff.mp hj)
  have h_H1_ge : sortedEigenvalues H1 hH1 i * ‖ψ‖ ^ 2 ≤ RCLike.re (inner ℂ ψ (H1 ψ)) := by
    apply le_re_inner_apply_H_of_mem_orthogonal_eigenSpanBelow H1 hH1 i.1 (sortedEigenvalues H1 hH1 i) _ hψU
    intro j hj; exact sortedEigenvalues_monotone_bhm H1 hH1 hj
  have h_diff_eq : RCLike.re (inner ℂ ψ (H1 ψ)) - RCLike.re (inner ℂ ψ (H2 ψ)) =
      RCLike.re (inner ℂ ψ ((H1 - H2) ψ)) := by
    rw [ContinuousLinearMap.sub_apply, inner_sub_right, map_sub]
  have h_diff_le : RCLike.re (inner ℂ ψ (H1 ψ)) - RCLike.re (inner ℂ ψ (H2 ψ)) ≤
      ‖H1 - H2‖ * ‖ψ‖ ^ 2 := by
    rw [h_diff_eq]
    exact le_trans (le_abs_self _) (abs_re_inner_le_opNorm_mul_norm_sq (H1 - H2) ψ)
  have h_le : sortedEigenvalues H1 hH1 i * ‖ψ‖ ^ 2 ≤
      (sortedEigenvalues H2 hH2 i + ‖H1 - H2‖) * ‖ψ‖ ^ 2 := by linarith
  exact le_of_mul_le_mul_right h_le (sq_pos_of_pos (norm_pos_iff.mpr hψ_ne))

private lemma sum_mul_le_of_sum_sq_le {ι : Type*} (s : Finset ι) (u v : ι → ℝ) {K_norm : ℝ}
    (hK : 0 ≤ K_norm)
    (hu : ∑ i ∈ s, (u i) ^ 2 ≤ K_norm ^ 2 * 1)
    (hv : ∑ i ∈ s, (v i) ^ 2 ≤ 1) :
    ∑ i ∈ s, u i * v i ≤ K_norm * 1 := by
  have h_cs := Real.sum_mul_le_sqrt_mul_sqrt s u v
  have h1 : Real.sqrt (∑ i ∈ s, (u i) ^ 2) ≤ K_norm := by
    rw [mul_one] at hu
    exact le_trans (Real.sqrt_le_sqrt hu) (Real.sqrt_sq hK).le
  have h2 : Real.sqrt (∑ i ∈ s, (v i) ^ 2) ≤ 1 :=
    le_trans (Real.sqrt_le_sqrt hv) Real.sqrt_one.le
  calc ∑ i ∈ s, u i * v i
    _ ≤ Real.sqrt (∑ i ∈ s, (u i) ^ 2) * Real.sqrt (∑ i ∈ s, (v i) ^ 2) := h_cs
    _ ≤ K_norm * 1 := mul_le_mul h1 h2 (Real.sqrt_nonneg _) hK

private lemma eq_sum_opEigenbasis {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    (H : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site)
    (hH : IsSelfAdjoint H) (χ : ManyBodyHilbertSpace Site) :
    χ = ∑ ω : ManyBodyConfig Site,
      inner ℂ (opEigenbasis H hH ω) χ • opEigenbasis H hH ω := by
  have h_id := onb_sum_ketBra_eq_one (opEigenbasis H hH)
    (opEigenbasis_orthonormal H hH) (opEigenbasis_parseval H hH)
  calc χ = (1 : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site) χ := rfl
    _ = (∑ ω : ManyBodyConfig Site, rankOneKetBra (opEigenbasis H hH ω)) χ := by rw [← h_id]
    _ = ∑ ω : ManyBodyConfig Site, inner ℂ (opEigenbasis H hH ω) χ • opEigenbasis H hH ω := by
        rw [ContinuousLinearMap.sum_apply]
        simp_rw [rankOneKetBra_apply]

private lemma sum_norm_inner_uncommuted_proj_le {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    (H0 H K P : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site)
    (hH0 : IsSelfAdjoint H0) (hH : IsSelfAdjoint H) (hK : IsSelfAdjoint K) (hP : IsStarProjection P) :
    let φ := opEigenbasis H0 hH0; let ψ := opEigenbasis H hH
    (∀ α : ManyBodyConfig Site,
      (∑ ω : ManyBodyConfig Site, ‖inner ℂ (φ α) (K (ψ ω))‖ * ‖inner ℂ (ψ ω) (P (φ α))‖) ≤
      ‖K‖ * 1) ∧
    (∀ ω : ManyBodyConfig Site,
      (∑ α : ManyBodyConfig Site, ‖inner ℂ (φ α) (K (ψ ω))‖ * ‖inner ℂ (ψ ω) (P (φ α))‖) ≤
      ‖K‖ * 1) := by
  intro φ ψ
  have hP_adj : P† = P := ContinuousLinearMap.isSelfAdjoint_iff'.mp hP.isSelfAdjoint
  have hK_adj : K† = K := ContinuousLinearMap.isSelfAdjoint_iff'.mp hK
  refine ⟨fun α => ?_, fun ω => ?_⟩
  · have h_u_eq : ∀ ω : ManyBodyConfig Site,
        ‖inner ℂ (φ α) (K (ψ ω))‖ = ‖inner ℂ (ψ ω) (K (φ α))‖ := fun ω => by
      rw [← ContinuousLinearMap.adjoint_inner_left, hK_adj, norm_inner_symm]
    have h_norm_φ : ‖φ α‖ ^ 2 = 1 := by
      have h1 := congrArg RCLike.re (opEigenbasis_orthonormal H0 hH0 α α)
      rw [if_pos rfl, inner_self_eq_norm_sq] at h1; simpa using h1
    have hu_sq : ∑ ω : ManyBodyConfig Site, ‖inner ℂ (φ α) (K (ψ ω))‖ ^ 2 ≤ ‖K‖ ^ 2 * 1 := by
      simp_rw [h_u_eq]
      rw [opEigenbasis_parseval H hH (K (φ α)), mul_one]
      have h2 := K.le_opNorm (φ α)
      have h3 : ‖K (φ α)‖ ^ 2 ≤ ‖K‖ ^ 2 * ‖φ α‖ ^ 2 := by
        nlinarith [norm_nonneg (K (φ α)), norm_nonneg K, norm_nonneg (φ α)]
      rwa [h_norm_φ, mul_one] at h3
    have hv_sq : ∑ ω : ManyBodyConfig Site, ‖inner ℂ (ψ ω) (P (φ α))‖ ^ 2 ≤ 1 := by
      rw [opEigenbasis_parseval H hH (P (φ α)), ← h_norm_φ]
      exact isStarProjection_norm_sq_apply_le hP (φ α)
    exact sum_mul_le_of_sum_sq_le Finset.univ _ _ (norm_nonneg K) hu_sq hv_sq
  · have h_v_eq : ∀ α : ManyBodyConfig Site,
        ‖inner ℂ (ψ ω) (P (φ α))‖ = ‖inner ℂ (φ α) (P (ψ ω))‖ := fun α => by
      rw [← ContinuousLinearMap.adjoint_inner_left, hP_adj, norm_inner_symm]
    have h_norm_ψ : ‖ψ ω‖ ^ 2 = 1 := by
      have h1 := congrArg RCLike.re (opEigenbasis_orthonormal H hH ω ω)
      rw [if_pos rfl, inner_self_eq_norm_sq] at h1; simpa using h1
    have hu_sq : ∑ α : ManyBodyConfig Site, ‖inner ℂ (φ α) (K (ψ ω))‖ ^ 2 ≤ ‖K‖ ^ 2 * 1 := by
      rw [opEigenbasis_parseval H0 hH0 (K (ψ ω)), mul_one]
      have h2 := K.le_opNorm (ψ ω)
      have h3 : ‖K (ψ ω)‖ ^ 2 ≤ ‖K‖ ^ 2 * ‖ψ ω‖ ^ 2 := by
        nlinarith [norm_nonneg (K (ψ ω)), norm_nonneg K, norm_nonneg (ψ ω)]
      rwa [h_norm_ψ, mul_one] at h3
    have hv_sq : ∑ α : ManyBodyConfig Site, ‖inner ℂ (ψ ω) (P (φ α))‖ ^ 2 ≤ 1 := by
      simp_rw [h_v_eq]; rw [opEigenbasis_parseval H0 hH0 (P (ψ ω)), ← h_norm_ψ]
      exact isStarProjection_norm_sq_apply_le hP (ψ ω)
    exact sum_mul_le_of_sum_sq_le Finset.univ _ _ (norm_nonneg K) hu_sq hv_sq

private lemma abs_exp_neg_sub_le_abs_sub_mul_add (a b : ℝ) :
    |Real.exp (-b) - Real.exp (-a)| ≤ |a - b| * (Real.exp (-a) + Real.exp (-b)) := by
  rcases le_total a b with hab | hba
  · have h_le : Real.exp (-b) ≤ Real.exp (-a) := Real.exp_le_exp.mpr (by linarith)
    have h_abs1 : |Real.exp (-b) - Real.exp (-a)| = Real.exp (-a) - Real.exp (-b) := by
      rw [abs_sub_comm, abs_of_nonneg (sub_nonneg.mpr h_le)]
    have h_abs2 : |a - b| = b - a := by
      rw [abs_sub_comm, abs_of_nonneg (sub_nonneg.mpr hab)]
    have h_exp_step : 1 - Real.exp (-(b - a)) ≤ b - a := by
      linarith [Real.add_one_le_exp (-(b - a))]
    have h_mul : Real.exp (-a) * (1 - Real.exp (-(b - a))) = Real.exp (-a) - Real.exp (-b) := by
      rw [mul_sub, mul_one, ← Real.exp_add]; ring_nf
    rw [h_abs1, h_abs2]
    calc Real.exp (-a) - Real.exp (-b)
      _ = Real.exp (-a) * (1 - Real.exp (-(b - a))) := h_mul.symm
      _ ≤ Real.exp (-a) * (b - a) :=
          mul_le_mul_of_nonneg_left h_exp_step (le_of_lt (Real.exp_pos _))
      _ ≤ (b - a) * (Real.exp (-a) + Real.exp (-b)) := by
          nlinarith [Real.exp_pos (-b), sub_nonneg.mpr hab]
  · have h_le : Real.exp (-a) ≤ Real.exp (-b) := Real.exp_le_exp.mpr (by linarith)
    have h_abs1 : |Real.exp (-b) - Real.exp (-a)| = Real.exp (-b) - Real.exp (-a) :=
      abs_of_nonneg (sub_nonneg.mpr h_le)
    have h_abs2 : |a - b| = a - b := abs_of_nonneg (sub_nonneg.mpr hba)
    have h_exp_step : 1 - Real.exp (-(a - b)) ≤ a - b := by
      linarith [Real.add_one_le_exp (-(a - b))]
    have h_mul : Real.exp (-b) * (1 - Real.exp (-(a - b))) = Real.exp (-b) - Real.exp (-a) := by
      rw [mul_sub, mul_one, ← Real.exp_add]; ring_nf
    rw [h_abs1, h_abs2]
    calc Real.exp (-b) - Real.exp (-a)
      _ = Real.exp (-b) * (1 - Real.exp (-(a - b))) := h_mul.symm
      _ ≤ Real.exp (-b) * (a - b) :=
          mul_le_mul_of_nonneg_left h_exp_step (le_of_lt (Real.exp_pos _))
      _ ≤ (a - b) * (Real.exp (-a) + Real.exp (-b)) := by
          nlinarith [Real.exp_pos (-a), sub_nonneg.mpr hba]

private lemma gibbsBoltzmannOp_zero_eq_one {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    (H : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site) (hH : IsSelfAdjoint H) :
    gibbsBoltzmannOp (opEigenbasis H hH) (opEigenvalues H hH) 0 = 1 := by
  unfold gibbsBoltzmannOp
  simp only [neg_zero, zero_mul, Real.exp_zero, Complex.ofReal_one, one_smul]
  exact onb_sum_ketBra_eq_one (opEigenbasis H hH)
    (opEigenbasis_orthonormal H hH) (opEigenbasis_parseval H hH)

private lemma abs_sub_eigenvalue_mul_norm_inner_eq {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    (H0 H : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site)
    (hH0 : IsSelfAdjoint H0) (hH : IsSelfAdjoint H)
    (α ω : ManyBodyConfig Site) :
    let φ := opEigenbasis H0 hH0
    let lam := opEigenvalues H0 hH0
    let ψ := opEigenbasis H hH
    let E := opEigenvalues H hH
    |lam α - E ω| * ‖inner ℂ (φ α) (ψ ω)‖ = ‖inner ℂ (φ α) ((H - H0) (ψ ω))‖ := by
  intro φ lam ψ E
  have hH0_adj : H0† = H0 := ContinuousLinearMap.isSelfAdjoint_iff'.mp hH0
  have h_eig0 : H0 (φ α) = (lam α : ℂ) • (φ α) := opEigenbasis_apply_H H0 hH0 α
  have h_eigH : H (ψ ω) = (E ω : ℂ) • (ψ ω) := opEigenbasis_apply_H H hH ω
  have h_in0 : inner ℂ (φ α) (H0 (ψ ω)) = (lam α : ℂ) * inner ℂ (φ α) (ψ ω) := by
    calc inner ℂ (φ α) (H0 (ψ ω))
      _ = inner ℂ ((H0†) (φ α)) (ψ ω) := (ContinuousLinearMap.adjoint_inner_left H0 (ψ ω) (φ α)).symm
      _ = inner ℂ (H0 (φ α)) (ψ ω) := by rw [hH0_adj]
      _ = inner ℂ ((lam α : ℂ) • (φ α)) (ψ ω) := by rw [h_eig0]
      _ = (lam α : ℂ) * inner ℂ (φ α) (ψ ω) := by rw [inner_smul_left, Complex.conj_ofReal]
  have h_inH : inner ℂ (φ α) (H (ψ ω)) = (E ω : ℂ) * inner ℂ (φ α) (ψ ω) := by
    rw [h_eigH, inner_smul_right]
  have h_eq : (((lam α - E ω : ℝ) : ℂ) * inner ℂ (φ α) (ψ ω)) =
      -inner ℂ (φ α) ((H - H0) (ψ ω)) := by
    rw [ContinuousLinearMap.sub_apply, inner_sub_right, h_inH, h_in0, Complex.ofReal_sub]
    ring
  have h_norm := congrArg norm h_eq
  rwa [norm_mul, Complex.norm_real, Real.norm_eq_abs, norm_neg] at h_norm

/-- **Duhamel–Weyl Relative Partition Ratio Bound (`duhamelWeyl_relative_partition_ratio_bound`, Part II, Lemma 3.1 (`lem:duhamel-weyl-ratio`), Equation `eq:duhamel-weyl-tail-bridge`)**:
For any self-adjoint `H_short, V_tail` on `ManyBodyHilbertSpace Site` and any star-projection `Π`
(not necessarily commuting with `H_short` or `V_tail`), for all `β ≥ 0`:
1. `Real.exp (-β * ‖V_tail‖) * gibbsPartitionZ (opEigenvalues H_short hH_short) β ≤ gibbsPartitionZ (opEigenvalues (H_short + V_tail) hH_full) β`.
2. `gibbsFailureProb (H_short + V_tail) hH_full β Π ≤ Real.exp (2 * β * ‖V_tail‖) * gibbsFailureProb H_short hH_short β Π + (Real.exp (2 * β * ‖V_tail‖) - 1)`. -/
theorem duhamelWeyl_relative_partition_ratio_bound {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    [∀ x, Nonempty (Site x)]
    (β : ℝ) (H_short V_tail P : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site)
    (hβ : 0 ≤ β) (hH_short : IsSelfAdjoint H_short) (hV_tail : IsSelfAdjoint V_tail)
    (hH_full : IsSelfAdjoint (H_short + V_tail)) (hP : IsStarProjection P) :
    Real.exp (-β * ‖V_tail‖) * gibbsPartitionZ (opEigenvalues H_short hH_short) β ≤
      gibbsPartitionZ (opEigenvalues (H_short + V_tail) hH_full) β ∧
    gibbsFailureProb (H_short + V_tail) hH_full β P ≤
      Real.exp (2 * β * ‖V_tail‖) * gibbsFailureProb H_short hH_short β P +
        (Real.exp (2 * β * ‖V_tail‖) - 1) := by
  let φ := opEigenbasis H_short hH_short
  let lam := opEigenvalues H_short hH_short
  let ψ := opEigenbasis (H_short + V_tail) hH_full
  let E := opEigenvalues (H_short + V_tail) hH_full
  have h_sub_H : (H_short + V_tail) - H_short = V_tail := add_sub_cancel_left H_short V_tail
  have h_part1 : Real.exp (-β * ‖V_tail‖) * gibbsPartitionZ lam β ≤ gibbsPartitionZ E β := by
    unfold gibbsPartitionZ
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun ω _ => ?_
    have h_weyl := sortedEigenvalues_le_add_norm_sub_local (H_short + V_tail) H_short
      hH_full hH_short (configFinEquiv Site ω)
    rw [h_sub_H] at h_weyl
    change E ω ≤ lam ω + ‖V_tail‖ at h_weyl
    rw [← Real.exp_add]
    exact Real.exp_le_exp.mpr (by nlinarith)
  refine ⟨h_part1, ?_⟩
  have h_tr_full :
      hilbertTrace (gibbsBoltzmannOp ψ E β * P) =
        ∑ α : ManyBodyConfig Site, ∑ ω : ManyBodyConfig Site,
          Real.exp (-β * E ω) *
            RCLike.re (inner ℂ (ψ ω) (P (φ α)) * inner ℂ (φ α) (ψ ω)) := by
    rw [hilbertTrace_gibbsBoltzmannOp_mul_eq]
    have h_inner : ∀ ω : ManyBodyConfig Site,
        Real.exp (-β * E ω) * RCLike.re (inner ℂ (ψ ω) (P (ψ ω))) =
          ∑ α : ManyBodyConfig Site,
            Real.exp (-β * E ω) *
              RCLike.re (inner ℂ (ψ ω) (P (φ α)) * inner ℂ (φ α) (ψ ω)) := fun ω => by
      have h_P_exp : P (ψ ω) = ∑ α : ManyBodyConfig Site, inner ℂ (φ α) (ψ ω) • P (φ α) := by
        calc P (ψ ω)
          _ = P (∑ α : ManyBodyConfig Site, inner ℂ (φ α) (ψ ω) • φ α) :=
              congrArg P (eq_sum_opEigenbasis H_short hH_short (ψ ω))
          _ = ∑ α : ManyBodyConfig Site, inner ℂ (φ α) (ψ ω) • P (φ α) := by
              rw [map_sum]; exact Finset.sum_congr rfl fun α _ => map_smul P _ _
      rw [h_P_exp, inner_sum, map_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun α _ => ?_
      rw [inner_smul_right, mul_comm (inner ℂ (φ α) (ψ ω))]
    trans (∑ ω : ManyBodyConfig Site, ∑ α : ManyBodyConfig Site,
      Real.exp (-β * E ω) * RCLike.re (inner ℂ (ψ ω) (P (φ α)) * inner ℂ (φ α) (ψ ω)))
    · exact Finset.sum_congr rfl fun ω _ => h_inner ω
    · exact Finset.sum_comm
  have h_tr_short :
      hilbertTrace (gibbsBoltzmannOp φ lam β * P) =
        ∑ α : ManyBodyConfig Site, ∑ ω : ManyBodyConfig Site,
          Real.exp (-β * lam α) *
            RCLike.re (inner ℂ (ψ ω) (P (φ α)) * inner ℂ (φ α) (ψ ω)) := by
    rw [hilbertTrace_gibbsBoltzmannOp_mul_eq]
    refine Finset.sum_congr rfl fun α _ => ?_
    have h_in_exp :
        inner ℂ (φ α) (P (φ α)) =
          ∑ ω : ManyBodyConfig Site,
            inner ℂ (ψ ω) (P (φ α)) * inner ℂ (φ α) (ψ ω) := by
      calc inner ℂ (φ α) (P (φ α))
        _ = inner ℂ (∑ ω : ManyBodyConfig Site, inner ℂ (ψ ω) (φ α) • ψ ω) (P (φ α)) :=
            congrArg (fun x => inner ℂ x (P (φ α)))
              (eq_sum_opEigenbasis (H_short + V_tail) hH_full (φ α))
        _ = ∑ ω : ManyBodyConfig Site,
              inner ℂ (ψ ω) (P (φ α)) * inner ℂ (φ α) (ψ ω) := by
            rw [sum_inner]
            refine Finset.sum_congr rfl fun ω _ => ?_
            rw [inner_smul_left, inner_conj_symm (φ α) (ψ ω), mul_comm]
    rw [h_in_exp, map_sum, Finset.mul_sum]
  let w (α ω : ManyBodyConfig Site) : ℝ :=
    ‖inner ℂ (φ α) (V_tail (ψ ω))‖ * ‖inner ℂ (ψ ω) (P (φ α))‖
  have h_term_le : ∀ α ω : ManyBodyConfig Site,
      (Real.exp (-β * E ω) - Real.exp (-β * lam α)) *
        RCLike.re (inner ℂ (ψ ω) (P (φ α)) * inner ℂ (φ α) (ψ ω)) ≤
      β * (Real.exp (-β * lam α) * w α ω + Real.exp (-β * E ω) * w α ω) := fun α ω => by
    have h_exp_diff : |Real.exp (-β * E ω) - Real.exp (-β * lam α)| ≤
        β * |lam α - E ω| * (Real.exp (-β * lam α) + Real.exp (-β * E ω)) := by
      have h0 := abs_exp_neg_sub_le_abs_sub_mul_add (β * lam α) (β * E ω)
      have h_sub : β * lam α - β * E ω = β * (lam α - E ω) := by ring
      rw [h_sub, abs_mul, abs_of_nonneg hβ] at h0
      simpa [neg_mul] using h0
    have h_re : |RCLike.re (inner ℂ (ψ ω) (P (φ α)) * inner ℂ (φ α) (ψ ω))| ≤
        ‖inner ℂ (φ α) (ψ ω)‖ * ‖inner ℂ (ψ ω) (P (φ α))‖ := by
      calc |RCLike.re (inner ℂ (ψ ω) (P (φ α)) * inner ℂ (φ α) (ψ ω))|
        _ ≤ ‖inner ℂ (ψ ω) (P (φ α)) * inner ℂ (φ α) (ψ ω)‖ := RCLike.abs_re_le_norm _
        _ = ‖inner ℂ (φ α) (ψ ω)‖ * ‖inner ℂ (ψ ω) (P (φ α))‖ := by rw [norm_mul, mul_comm]
    have h_eig := abs_sub_eigenvalue_mul_norm_inner_eq H_short (H_short + V_tail) hH_short hH_full α ω
    dsimp only [φ, lam, ψ, E] at h_eig
    rw [h_sub_H] at h_eig
    calc (Real.exp (-β * E ω) - Real.exp (-β * lam α)) *
          RCLike.re (inner ℂ (ψ ω) (P (φ α)) * inner ℂ (φ α) (ψ ω))
      _ ≤ |(Real.exp (-β * E ω) - Real.exp (-β * lam α)) *
            RCLike.re (inner ℂ (ψ ω) (P (φ α)) * inner ℂ (φ α) (ψ ω))| := le_abs_self _
      _ = |Real.exp (-β * E ω) - Real.exp (-β * lam α)| *
            |RCLike.re (inner ℂ (ψ ω) (P (φ α)) * inner ℂ (φ α) (ψ ω))| := abs_mul _ _
      _ ≤ (β * |lam α - E ω| * (Real.exp (-β * lam α) + Real.exp (-β * E ω))) *
            (‖inner ℂ (φ α) (ψ ω)‖ * ‖inner ℂ (ψ ω) (P (φ α))‖) :=
          mul_le_mul h_exp_diff h_re (abs_nonneg _) (by positivity)
      _ = β * (Real.exp (-β * lam α) + Real.exp (-β * E ω)) *
            ((|lam α - E ω| * ‖inner ℂ (φ α) (ψ ω)‖) * ‖inner ℂ (ψ ω) (P (φ α))‖) := by ring
      _ = β * (Real.exp (-β * lam α) * w α ω + Real.exp (-β * E ω) * w α ω) := by
          rw [h_eig]; dsimp [w]; ring
  obtain ⟨h_alpha_sum, h_omega_sum⟩ :=
    sum_norm_inner_uncommuted_proj_le H_short (H_short + V_tail) V_tail P hH_short hH_full hV_tail hP
  have h_diff_le :
      hilbertTrace (gibbsBoltzmannOp ψ E β * P) - hilbertTrace (gibbsBoltzmannOp φ lam β * P) ≤
        β * (‖V_tail‖ * gibbsPartitionZ lam β + ‖V_tail‖ * gibbsPartitionZ E β) := by
    rw [h_tr_full, h_tr_short, ← Finset.sum_sub_distrib]
    have h_inner_sub : ∀ α : ManyBodyConfig Site,
        (∑ ω : ManyBodyConfig Site,
          Real.exp (-β * E ω) * RCLike.re (inner ℂ (ψ ω) (P (φ α)) * inner ℂ (φ α) (ψ ω))) -
        (∑ ω : ManyBodyConfig Site,
          Real.exp (-β * lam α) * RCLike.re (inner ℂ (ψ ω) (P (φ α)) * inner ℂ (φ α) (ψ ω))) =
        ∑ ω : ManyBodyConfig Site,
          (Real.exp (-β * E ω) - Real.exp (-β * lam α)) *
            RCLike.re (inner ℂ (ψ ω) (P (φ α)) * inner ℂ (φ α) (ψ ω)) := fun α => by
      rw [← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun ω _ => by ring
    simp_rw [h_inner_sub]
    have h_sum_step :
        (∑ α : ManyBodyConfig Site, ∑ ω : ManyBodyConfig Site,
          (Real.exp (-β * E ω) - Real.exp (-β * lam α)) *
            RCLike.re (inner ℂ (ψ ω) (P (φ α)) * inner ℂ (φ α) (ψ ω))) ≤
        β * ((∑ α : ManyBodyConfig Site, Real.exp (-β * lam α) * ∑ ω : ManyBodyConfig Site, w α ω) +
          (∑ ω : ManyBodyConfig Site, Real.exp (-β * E ω) * ∑ α : ManyBodyConfig Site, w α ω)) := by
      refine le_trans (Finset.sum_le_sum fun α _ => Finset.sum_le_sum fun ω _ => h_term_le α ω) ?_
      simp_rw [← Finset.mul_sum, Finset.sum_add_distrib, ← Finset.mul_sum]
      rw [Finset.sum_comm (f := fun α ω => Real.exp (-β * E ω) * w α ω)]
      simp_rw [← Finset.mul_sum]; exact le_rfl
    refine le_trans h_sum_step (mul_le_mul_of_nonneg_left (add_le_add ?_ ?_) hβ)
    · rw [gibbsPartitionZ, Finset.mul_sum]
      refine Finset.sum_le_sum fun α _ => ?_
      linarith [mul_le_mul_of_nonneg_left (h_alpha_sum α) (le_of_lt (Real.exp_pos (-β * lam α)))]
    · rw [gibbsPartitionZ, Finset.mul_sum]
      refine Finset.sum_le_sum fun ω _ => ?_
      linarith [mul_le_mul_of_nonneg_left (h_omega_sum ω) (le_of_lt (Real.exp_pos (-β * E ω)))]
  have h_tr_le :
      hilbertTrace (gibbsBoltzmannOp ψ E β * P) ≤
        hilbertTrace (gibbsBoltzmannOp φ lam β * P) +
          β * ‖V_tail‖ * (gibbsPartitionZ lam β + gibbsPartitionZ E β) := by
    linarith
  have hZ_short_pos : 0 < gibbsPartitionZ lam β := gibbsPartitionZ_pos lam β
  have hZ_full_pos : 0 < gibbsPartitionZ E β := gibbsPartitionZ_pos E β
  have hZ_ratio : (gibbsPartitionZ E β)⁻¹ * gibbsPartitionZ lam β ≤ Real.exp (β * ‖V_tail‖) := by
    rw [inv_mul_le_iff₀ hZ_full_pos]
    calc gibbsPartitionZ lam β
      _ = Real.exp (β * ‖V_tail‖) * (Real.exp (-β * ‖V_tail‖) * gibbsPartitionZ lam β) := by
          rw [← mul_assoc, ← Real.exp_add]; ring_nf; rw [Real.exp_zero, one_mul]
      _ ≤ Real.exp (β * ‖V_tail‖) * gibbsPartitionZ E β :=
          mul_le_mul_of_nonneg_left h_part1 (le_of_lt (Real.exp_pos _))
      _ = gibbsPartitionZ E β * Real.exp (β * ‖V_tail‖) := mul_comm _ _
  have h_tr_short_nn : 0 ≤ hilbertTrace (gibbsBoltzmannOp φ lam β * P) := by
    rw [hilbertTrace_gibbsBoltzmannOp_mul_eq]
    refine Finset.sum_nonneg fun ω _ => mul_nonneg (le_of_lt (Real.exp_pos _)) ?_
    rw [isStarProjection_re_inner_eq_norm_sq hP (φ ω)]
    exact sq_nonneg _
  have hp_short_nn : 0 ≤ gibbsFailureProb H_short hH_short β P := by
    rw [perturbed_gibbsFailureProb_eq_inv_gibbsPartitionZ_mul_boltzmann_trace H_short hH_short β P]
    exact mul_nonneg (inv_nonneg.mpr (le_of_lt hZ_short_pos)) h_tr_short_nn
  have h_first_term :
      (gibbsPartitionZ E β)⁻¹ * hilbertTrace (gibbsBoltzmannOp φ lam β * P) ≤
        Real.exp (2 * β * ‖V_tail‖) * gibbsFailureProb H_short hH_short β P := by
    have h_eq : (gibbsPartitionZ E β)⁻¹ * hilbertTrace (gibbsBoltzmannOp φ lam β * P) =
        ((gibbsPartitionZ E β)⁻¹ * gibbsPartitionZ lam β) * gibbsFailureProb H_short hH_short β P := by
      rw [perturbed_gibbsFailureProb_eq_inv_gibbsPartitionZ_mul_boltzmann_trace H_short hH_short β P]
      dsimp only [φ, lam]
      rw [mul_assoc, ← mul_assoc (gibbsPartitionZ lam β),
        mul_inv_cancel₀ (ne_of_gt hZ_short_pos), one_mul]
    have h_exp_le : Real.exp (β * ‖V_tail‖) ≤ Real.exp (2 * β * ‖V_tail‖) :=
      Real.exp_le_exp.mpr (by nlinarith [norm_nonneg V_tail])
    rw [h_eq]
    exact mul_le_mul_of_nonneg_right (le_trans hZ_ratio h_exp_le) hp_short_nn
  have h_second_term :
      (gibbsPartitionZ E β)⁻¹ * (β * ‖V_tail‖ * (gibbsPartitionZ lam β + gibbsPartitionZ E β)) ≤
        Real.exp (2 * β * ‖V_tail‖) - 1 := by
    let x := β * ‖V_tail‖
    have hx_nn : 0 ≤ x := mul_nonneg hβ (norm_nonneg V_tail)
    have h_alg : (gibbsPartitionZ E β)⁻¹ * (x * (gibbsPartitionZ lam β + gibbsPartitionZ E β)) =
        x * ((gibbsPartitionZ E β)⁻¹ * gibbsPartitionZ lam β + 1) := by
      calc (gibbsPartitionZ E β)⁻¹ * (x * (gibbsPartitionZ lam β + gibbsPartitionZ E β))
        _ = x * ((gibbsPartitionZ E β)⁻¹ * gibbsPartitionZ lam β +
              (gibbsPartitionZ E β)⁻¹ * gibbsPartitionZ E β) := by ring
        _ = x * ((gibbsPartitionZ E β)⁻¹ * gibbsPartitionZ lam β + 1) := by
            rw [inv_mul_cancel₀ (ne_of_gt hZ_full_pos)]
    have hx_exp : x ≤ Real.exp x - 1 := by linarith [Real.add_one_le_exp x]
    have h_2x : Real.exp (2 * x) - 1 = (Real.exp x - 1) * (Real.exp x + 1) := by
      have : Real.exp (2 * x) = Real.exp x * Real.exp x := by
        rw [← Real.exp_add]; ring_nf
      rw [this]; ring
    rw [h_alg]
    calc x * ((gibbsPartitionZ E β)⁻¹ * gibbsPartitionZ lam β + 1)
      _ ≤ x * (Real.exp x + 1) :=
          mul_le_mul_of_nonneg_left (by linarith [hZ_ratio]) hx_nn
      _ ≤ (Real.exp x - 1) * (Real.exp x + 1) :=
          mul_le_mul_of_nonneg_right hx_exp (by positivity)
      _ = Real.exp (2 * β * ‖V_tail‖) - 1 := by
          rw [← h_2x]; dsimp [x]; ring_nf
  rw [perturbed_gibbsFailureProb_eq_inv_gibbsPartitionZ_mul_boltzmann_trace
    (H_short + V_tail) hH_full β P]
  (try dsimp only [ψ, E])
  calc (gibbsPartitionZ E β)⁻¹ * hilbertTrace (gibbsBoltzmannOp ψ E β * P)
    _ ≤ (gibbsPartitionZ E β)⁻¹ *
          (hilbertTrace (gibbsBoltzmannOp φ lam β * P) +
            β * ‖V_tail‖ * (gibbsPartitionZ lam β + gibbsPartitionZ E β)) :=
        mul_le_mul_of_nonneg_left h_tr_le (inv_nonneg.mpr (le_of_lt hZ_full_pos))
    _ = (gibbsPartitionZ E β)⁻¹ * hilbertTrace (gibbsBoltzmannOp φ lam β * P) +
          (gibbsPartitionZ E β)⁻¹ * (β * ‖V_tail‖ * (gibbsPartitionZ lam β + gibbsPartitionZ E β)) :=
        mul_add _ _ _
    _ ≤ Real.exp (2 * β * ‖V_tail‖) * gibbsFailureProb H_short hH_short β P +
          (Real.exp (2 * β * ‖V_tail‖) - 1) :=
        add_le_add h_first_term h_second_term

/-- **Positive Witness Gibbs Defect Sum Bound (`positiveWitness_gibbs_defect_sum_le`, Part II, Lemma 3.2 (`lem:positive-witness-bound`))**:
If `W_cover` is a positive check witness cover for `S_safe` (`IsPositiveCheckWitnessCover S_safe W_cover`)
and each witness `W ∈ W_cover` has Gibbs expectation bounded by `w_bound W`, then
`gibbsFailureProb H_full hH_full β (1 - indexedBareFailureProjector sys S_safe) ≤ ∑ W ∈ W_cover, w_bound W`. -/
theorem positiveWitness_gibbs_defect_sum_le {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    [∀ x, Nonempty (Site x)]
    {ι_chk : Type} [Fintype ι_chk] [DecidableEq ι_chk]
    (sys : IndexedCommutingProjectorHamiltonian D L Site ι_chk)
    (H_full : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site)
    (hH_full : IsSelfAdjoint H_full) (β : ℝ)
    (S_safe : Finset (ι_chk → Bool))
    (W_cover : Finset (Finset ι_chk))
    (w_bound : Finset ι_chk → ℝ)
    (h_cover : IsPositiveCheckWitnessCover S_safe W_cover)
    (h_witness_le : ∀ W ∈ W_cover,
      gibbsFailureProb H_full hH_full β (positiveCheckWitnessProj sys W) ≤ w_bound W) :
    gibbsFailureProb H_full hH_full β (1 - indexedBareFailureProjector sys S_safe) ≤
      ∑ W ∈ W_cover, w_bound W := by
  have h_dom := (hilbertTrace_gibbsBoltzmannOp_unsafe_le_sum_positiveCheckWitnessProj
    sys H_full hH_full β h_cover).2.2
  exact le_trans h_dom (Finset.sum_le_sum h_witness_le)

/-- Lower bound `7 ≤ Real.log klarnerAnimalConst` (`klarnerAnimalConst = 28512 * e ≥ 16384 = 2^14 ≥ e^7`). -/
lemma seven_le_log_klarnerAnimalConst :
    7 ≤ Real.log klarnerAnimalConst := by
  have h_half : (1 / 2 : ℝ) ≤ Real.exp (-(1 / 2 : ℝ)) := by
    linarith [Real.add_one_le_exp (-(1 / 2 : ℝ))]
  have h_prod : Real.exp (1 / 2 : ℝ) * Real.exp (-(1 / 2 : ℝ)) = 1 := by
    rw [← Real.exp_add]; norm_num
  have h_e_half : Real.exp (1 / 2 : ℝ) ≤ 2 := by
    have h_pos : 0 < Real.exp (1 / 2 : ℝ) := Real.exp_pos _
    have h_mul := mul_le_mul_of_nonneg_left h_half (le_of_lt h_pos)
    linarith
  have h_e7 : Real.exp 7 ≤ klarnerAnimalConst := by
    have h_eq : Real.exp 7 = (Real.exp (1 / 2 : ℝ)) ^ 14 := by
      rw [← Real.exp_nat_mul]; norm_num
    have h_pow : (Real.exp (1 / 2 : ℝ)) ^ 14 ≤ (2 : ℝ) ^ 14 :=
      pow_le_pow_left₀ (le_of_lt (Real.exp_pos _)) h_e_half 14
    have h_e1 : (1 : ℝ) ≤ Real.exp 1 := Real.one_le_exp zero_le_one
    unfold klarnerAnimalConst
    rw [h_eq]
    linarith
  calc (7 : ℝ)
    _ = Real.log (Real.exp 7) := (Real.log_exp 7).symm
    _ ≤ Real.log klarnerAnimalConst := Real.log_le_log (Real.exp_pos 7) h_e7

/-- For `0 < Δ_0 ≤ 1 / 4`, `24 ≤ criticalInverseTempHier Δ_0`. -/
lemma twenty_four_le_criticalInverseTempHier {Δ_0 : ℝ}
    (hΔ_pos : 0 < Δ_0) (hΔ_le : Δ_0 ≤ 1 / 4) :
    24 ≤ criticalInverseTempHier Δ_0 := by
  unfold criticalInverseTempHier
  have h_log := seven_le_log_klarnerAnimalConst
  have h_denom_pos : 0 < (3 / 2 : ℝ) * Δ_0 := by positivity
  rw [le_div_iff₀ h_denom_pos]
  linarith

/-- **Klarner Animal Peierls Geometric Series Bound (`klarner_animal_peierls_geometric_series_bound`, Part II, Lemma 3.3 (`lem:klarner-bound`))**:
When the Peierls suppression rate `κ` exceeds `log klarnerAnimalConst + 1`, we have
`klarnerAnimalConst * exp(-κ) ≤ exp(-1) < 1 / 2`, and the animal-weighted geometric series over
witness sizes `d_min + s` (`s : ℕ`) is bounded by `2 * exp(-(κ - log klarnerAnimalConst) * d_min)`. -/
theorem klarner_animal_peierls_geometric_series_bound
    (d_min : ℕ) (κ : ℝ)
    (hκ : Real.log klarnerAnimalConst + 1 ≤ κ) :
    klarnerAnimalConst * Real.exp (-κ) ≤ 1 / 2 ∧
    (∑' s : ℕ, (klarnerAnimalConst * Real.exp (-κ)) ^ (d_min + s)) ≤
      2 * Real.exp (-(κ - Real.log klarnerAnimalConst) * (d_min : ℝ)) := by
  have hK_pos : 0 < klarnerAnimalConst := by
    unfold klarnerAnimalConst
    positivity
  let q := klarnerAnimalConst * Real.exp (-κ)
  have hq_eq : q = Real.exp (-(κ - Real.log klarnerAnimalConst)) := by
    calc q
      _ = Real.exp (Real.log klarnerAnimalConst) * Real.exp (-κ) := by
          dsimp [q]; rw [Real.exp_log hK_pos]
      _ = Real.exp (-(κ - Real.log klarnerAnimalConst)) := by
          rw [← Real.exp_add]; ring_nf
  have hq_nn : 0 ≤ q := by dsimp [q]; positivity
  have hq_le_half : q ≤ 1 / 2 := by
    have h_exp1 : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
    have h_le_e1 : q ≤ Real.exp (-1) := by
      rw [hq_eq]
      exact Real.exp_le_exp.mpr (by linarith)
    have h_e1_inv : Real.exp (-1) ≤ 1 / 2 := by
      rw [Real.exp_neg, one_div]
      exact inv_anti₀ (by positivity) h_exp1
    exact le_trans h_le_e1 h_e1_inv
  refine ⟨hq_le_half, ?_⟩
  have hq_lt_one : q < 1 := by linarith
  have h_pow_eq : q ^ d_min = Real.exp (-(κ - Real.log klarnerAnimalConst) * (d_min : ℝ)) := by
    rw [hq_eq, ← Real.exp_nat_mul, mul_comm]
  have h_inv_le : (1 - q)⁻¹ ≤ 2 := by
    rw [inv_le_comm₀ (by linarith) (by positivity)]
    linarith
  calc (∑' s : ℕ, q ^ (d_min + s))
    _ = ∑' s : ℕ, q ^ d_min * q ^ s := by
        refine tsum_congr fun s => pow_add q d_min s
    _ = q ^ d_min * (∑' s : ℕ, q ^ s) := tsum_mul_left
    _ = q ^ d_min * (1 - q)⁻¹ := by rw [tsum_geometric_of_lt_one hq_nn hq_lt_one]
    _ ≤ q ^ d_min * 2 := mul_le_mul_of_nonneg_left h_inv_le (pow_nonneg hq_nn d_min)
    _ = 2 * Real.exp (-(κ - Real.log klarnerAnimalConst) * (d_min : ℝ)) := by
        rw [h_pow_eq, mul_comm]

/-- **Klarner Animal Shell Sum Bound (`klarner_animal_shell_sum_bound`, Part II, Lemma 3.3 (`lem:klarner-bound`))**:
For any finite witness family `W_cover : Finset (Finset ι_chk)` with minimum witness size
`∀ W ∈ W_cover, d_min ≤ W.card` and Klarner lattice-animal shell multiplicity
`∀ s : ℕ, ((W_cover.filter (fun W => W.card = d_min + s)).card : ℝ) ≤ klarnerAnimalConst ^ (d_min + s)`,
whenever `Real.log klarnerAnimalConst + 1 ≤ κ`, the finite witness sum is bounded by the
animal-weighted geometric series `∑' s : ℕ, (klarnerAnimalConst * Real.exp (-κ)) ^ (d_min + s)` and hence by
`2 * Real.exp (-(κ - Real.log klarnerAnimalConst) * (d_min : ℝ))`. -/
theorem klarner_animal_shell_sum_bound
    {ι_chk : Type*} [DecidableEq ι_chk]
    (W_cover : Finset (Finset ι_chk)) (d_min : ℕ) (κ : ℝ)
    (h_d_min : ∀ W ∈ W_cover, d_min ≤ W.card)
    (h_shell : ∀ s : ℕ,
      ((W_cover.filter (fun W => W.card = d_min + s)).card : ℝ) ≤
        klarnerAnimalConst ^ (d_min + s))
    (hκ : Real.log klarnerAnimalConst + 1 ≤ κ) :
    (∑ W ∈ W_cover, Real.exp (-κ * (W.card : ℝ))) ≤
      (∑' s : ℕ, (klarnerAnimalConst * Real.exp (-κ)) ^ (d_min + s)) ∧
    (∑ W ∈ W_cover, Real.exp (-κ * (W.card : ℝ))) ≤
      2 * Real.exp (-(κ - Real.log klarnerAnimalConst) * (d_min : ℝ)) := by
  have hK_pos : 0 < klarnerAnimalConst := by
    unfold klarnerAnimalConst
    positivity
  have h_peierls := klarner_animal_peierls_geometric_series_bound d_min κ hκ
  have h_rate : klarnerAnimalConst * Real.exp (-κ) ≤ 1 / 2 := h_peierls.1
  let q := klarnerAnimalConst * Real.exp (-κ)
  have hq_nn : 0 ≤ q := by dsimp [q]; positivity
  have hq_lt_one : q < 1 := by linarith
  let M := W_cover.sup Finset.card + 1
  have h_maps : ∀ W ∈ W_cover, W.card - d_min ∈ Finset.range M := by
    intro W hW
    have h_le : W.card ≤ W_cover.sup Finset.card := Finset.le_sup (f := Finset.card) hW
    rw [Finset.mem_range]
    dsimp [M]
    omega
  have h_fiber := (Finset.sum_fiberwise_of_maps_to h_maps
    (fun W => Real.exp (-κ * (W.card : ℝ)))).symm
  have h_shell_term : ∀ s : ℕ,
      (∑ W ∈ W_cover.filter (fun W => W.card - d_min = s), Real.exp (-κ * (W.card : ℝ))) ≤
        q ^ (d_min + s) := by
    intro s
    have h_filt_eq :
        W_cover.filter (fun W => W.card - d_min = s) =
          W_cover.filter (fun W => W.card = d_min + s) := by
      refine Finset.filter_congr fun W hW => ?_
      have hd := h_d_min W hW
      omega
    rw [h_filt_eq]
    have h_const :
        (∑ W ∈ W_cover.filter (fun W => W.card = d_min + s), Real.exp (-κ * (W.card : ℝ))) =
          ((W_cover.filter (fun W => W.card = d_min + s)).card : ℝ) *
            (Real.exp (-κ)) ^ (d_min + s) := by
      have h_congr :
          (∑ W ∈ W_cover.filter (fun W => W.card = d_min + s), Real.exp (-κ * (W.card : ℝ))) =
            ∑ _W ∈ W_cover.filter (fun W => W.card = d_min + s),
              (Real.exp (-κ)) ^ (d_min + s) := by
        refine Finset.sum_congr rfl fun W hW => ?_
        have hW_card : W.card = d_min + s := (Finset.mem_filter.mp hW).2
        rw [hW_card, ← Real.exp_nat_mul]
        congr 1
        ring
      rw [h_congr, Finset.sum_const, nsmul_eq_mul]
    rw [h_const]
    calc ((W_cover.filter (fun W => W.card = d_min + s)).card : ℝ) *
          (Real.exp (-κ)) ^ (d_min + s)
      _ ≤ klarnerAnimalConst ^ (d_min + s) * (Real.exp (-κ)) ^ (d_min + s) :=
          mul_le_mul_of_nonneg_right (h_shell s) (by positivity)
      _ = q ^ (d_min + s) := by
          dsimp [q]; rw [← mul_pow]
  have h_sum_geom : Summable (fun s : ℕ => q ^ (d_min + s)) := by
    have h_eq_fn : (fun s : ℕ => q ^ (d_min + s)) = (fun s : ℕ => q ^ d_min * q ^ s) := by
      funext s; exact pow_add q d_min s
    rw [h_eq_fn]
    exact (summable_geometric_of_lt_one hq_nn hq_lt_one).mul_left (q ^ d_min)
  have h_part1 :
      (∑ W ∈ W_cover, Real.exp (-κ * (W.card : ℝ))) ≤
        ∑' s : ℕ, q ^ (d_min + s) := by
    calc (∑ W ∈ W_cover, Real.exp (-κ * (W.card : ℝ)))
      _ = ∑ s ∈ Finset.range M,
            ∑ W ∈ W_cover.filter (fun W => W.card - d_min = s), Real.exp (-κ * (W.card : ℝ)) :=
          h_fiber
      _ ≤ ∑ s ∈ Finset.range M, q ^ (d_min + s) :=
          Finset.sum_le_sum fun s _ => h_shell_term s
      _ ≤ ∑' s : ℕ, q ^ (d_min + s) :=
          h_sum_geom.sum_le_tsum (Finset.range M) (fun s _ => pow_nonneg hq_nn _)
  exact ⟨h_part1, le_trans h_part1 h_peierls.2⟩

/-- **Pauli Diagonal/Off-Diagonal Decomposition and Local Shift Bound (`pauliDiagOffDecomposition_local_shift_le`, Part II, Proposition 3.4 (`prop:pauli-diag-off`))**:
Under `HasQuasiLocalDecayBound V J f` with `0 ≤ J`:
1. For any cutoff `R_cut : ℕ`, `V.V_tot = scaleSplitTruncatedOp V R_cut + scaleSplitTailOp V R_cut`.
2. Both `scaleSplitTruncatedOp V R_cut` and `scaleSplitTailOp V R_cut` are self-adjoint.
3. The tail operator norm satisfies
   `‖scaleSplitTailOp V R_cut‖ ≤ J * ((L ^ 3 : ℕ) : ℝ) * perturbationTailSeries f R_cut`.
4. Each local term decomposes as `V.term r A = syndromePinchOp sys (V.term r A) + pauliOffDiagonalTerm sys V r A`
   where `syndromePinchOp sys (V.term r A)` commutes with all syndrome projectors `sys.syndromeProjector σ`,
   `pauliOffDiagonalTerm sys V r A` is strictly off-diagonal (`sys.syndromeProjector σ * pauliOffDiagonalTerm sys V r A * sys.syndromeProjector σ = 0`),
   and for any two syndrome sectors `σ, τ` and unit vectors `ψ, φ`, the diagonal expectation shift is
   bounded by `2 * J * f r`. -/
theorem pauliDiagOffDecomposition_local_shift_le {L N_checks : ℕ}
    {Site0 : Type} [Fintype Site0] [DecidableEq Site0]
    (sys : ℋ_CP[L, Site0, N_checks])
    (V : 𝒱_pert[L, Site0]) (J : ℝ) (f : ℕ → ℝ) (R_cut : ℕ)
    (hJ : 0 ≤ J) (hf_nonneg : ∀ r : ℕ, 0 ≤ f r)
    (h_summable : Summable f)
    (h_ql : HasQuasiLocalDecayBound V J f) :
    V.totalPerturbation = scaleSplitTruncatedOp V R_cut + scaleSplitTailOp V R_cut ∧
    IsSelfAdjoint (scaleSplitTruncatedOp V R_cut) ∧
    IsSelfAdjoint (scaleSplitTailOp V R_cut) ∧
    ‖scaleSplitTailOp V R_cut‖ ≤
      J * ((L ^ 3 : ℕ) : ℝ) * perturbationTailSeries f R_cut ∧
    scaleSplitTruncatedOp V R_cut =
      pauliDiagonalPart sys V R_cut + pauliOffDiagonalPart sys V R_cut ∧
    (∀ r A, V.term r A = syndromePinchOp sys (V.term r A) + pauliOffDiagonalTerm sys V r A) ∧
    (∀ r A σ, Commute (syndromePinchOp sys (V.term r A)) (sys.syndromeProjector σ)) ∧
    (∀ r A σ,
      sys.syndromeProjector σ * pauliOffDiagonalTerm sys V r A * sys.syndromeProjector σ = 0) ∧
    (∀ r ∈ Finset.Icc 1 L, ∀ A ∈ boxCubes 3 L r,
      ∀ σ τ : Fin N_checks → Bool, ∀ ψ φ : ℋ[L, Site0],
        ‖ψ‖ ≤ 1 → ‖φ‖ ≤ 1 →
        |RCLike.re (inner ℂ (sys.syndromeProjector σ ψ)
            (syndromePinchOp sys (V.term r A) (sys.syndromeProjector σ ψ))) -
          RCLike.re (inner ℂ (sys.syndromeProjector τ φ)
            (syndromePinchOp sys (V.term r A) (sys.syndromeProjector τ φ)))| ≤
          2 * J * f r) := by
  have h_filter_le : Finset.Icc 1 (min R_cut L) =
      (Finset.Icc 1 L).filter (fun r => r ≤ R_cut) := by
    ext r
    simp only [Finset.mem_Icc, Finset.mem_filter, le_min_iff]
    omega
  have h_filter_gt : (Finset.Icc 1 L).filter (fun r => R_cut < r) =
      (Finset.Icc 1 L).filter (fun r => ¬ r ≤ R_cut) := by
    ext r
    simp only [Finset.mem_filter, not_le]
  have h_res := _root_.syndrome_resolution_indexed sys
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold QuasiLocalPerturbation.totalPerturbation scaleSplitTruncatedOp scaleSplitTailOp
    rw [h_filter_le, h_filter_gt, Finset.sum_filter_add_sum_filter_not]
  · unfold scaleSplitTruncatedOp
    exact _root_.isSelfAdjoint_finset_sum _ _ fun r _ =>
      _root_.isSelfAdjoint_finset_sum _ _ fun A _ => V.is_selfAdjoint r A
  · unfold scaleSplitTailOp
    exact _root_.isSelfAdjoint_finset_sum _ _ fun r _ =>
      _root_.isSelfAdjoint_finset_sum _ _ fun A _ => V.is_selfAdjoint r A
  · unfold scaleSplitTailOp perturbationTailSeries
    let S_tail := (Finset.Icc 1 L).filter (fun r => R_cut < r)
    have h_tail_summable : Summable (fun r : ℕ => if R_cut < r then f r else 0) :=
      Summable.of_nonneg_of_le
        (fun r => by split_ifs <;> [exact hf_nonneg r; exact le_rfl])
        (fun r => by split_ifs <;> [exact le_rfl; exact hf_nonneg r])
        h_summable
    have h_step1 : ‖∑ r ∈ S_tail, ∑ A ∈ boxCubes 3 L r, V.term r A‖ ≤
        ∑ r ∈ S_tail, ∑ A ∈ boxCubes 3 L r, ‖V.term r A‖ :=
      le_trans (norm_sum_le S_tail _)
        (Finset.sum_le_sum fun r _ => norm_sum_le (boxCubes 3 L r) _)
    have h_step2 : (∑ r ∈ S_tail, ∑ A ∈ boxCubes 3 L r, ‖V.term r A‖) ≤
        ∑ r ∈ S_tail, J * ((L ^ 3 : ℕ) : ℝ) * (if R_cut < r then f r else 0) := by
      refine Finset.sum_le_sum fun r hr => ?_
      have hr_mem := Finset.mem_filter.mp hr
      rw [if_pos hr_mem.2]
      exact h_ql.2 r hr_mem.1
    have h_step3 : (∑ r ∈ S_tail, J * ((L ^ 3 : ℕ) : ℝ) * (if R_cut < r then f r else 0)) ≤
        J * ((L ^ 3 : ℕ) : ℝ) * (∑' r : ℕ, if R_cut < r then f r else 0) := by
      rw [← Finset.mul_sum]
      refine mul_le_mul_of_nonneg_left ?_ (by positivity)
      exact h_tail_summable.sum_le_tsum S_tail
        (fun r _ => by split_ifs <;> [exact hf_nonneg r; exact le_rfl])
    exact le_trans h_step1 (le_trans h_step2 h_step3)
  · unfold scaleSplitTruncatedOp pauliDiagonalPart pauliOffDiagonalPart
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun r _ => ?_
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun A _ => (add_sub_cancel _ _).symm
  · intro r A
    unfold pauliOffDiagonalTerm
    exact (add_sub_cancel _ _).symm
  · intro r A σ
    exact (syndromePinchOp_isSelfAdjoint_and_commute_checkProj sys (V.is_selfAdjoint r A)).2.1 σ |>.2.2
  · intro r A σ
    unfold pauliOffDiagonalTerm
    have h_pinch :=
      (syndromePinchOp_isSelfAdjoint_and_commute_checkProj sys (V.is_selfAdjoint r A)).2.1 σ |>.2.1
    have h_idem : sys.syndromeProjector σ * sys.syndromeProjector σ = sys.syndromeProjector σ :=
      (h_res.2.1 σ).isIdempotentElem
    rw [mul_sub, sub_mul, h_pinch, mul_assoc (sys.syndromeProjector σ * V.term r A), h_idem, sub_self]
  · intro r hr A hA σ τ ψ φ hψ hφ
    have h_norm_V : ‖V.term r A‖ ≤ J * f r := (h_ql.1 r hr A hA).2
    have h_single : ∀ (ν : Fin N_checks → Bool) (χ : ℋ[L, Site0]),
        ‖χ‖ ≤ 1 →
        |RCLike.re (inner ℂ (sys.syndromeProjector ν χ)
            (syndromePinchOp sys (V.term r A) (sys.syndromeProjector ν χ)))| ≤
          J * f r := by
      intro ν χ hχ
      let ξ := sys.syndromeProjector ν χ
      have h_proj_ν := h_res.2.1 ν
      have h_pinch_ν :=
        (syndromePinchOp_isSelfAdjoint_and_commute_checkProj sys (V.is_selfAdjoint r A)).2.1 ν |>.1
      have h_act : syndromePinchOp sys (V.term r A) ξ =
          sys.syndromeProjector ν (V.term r A ξ) := by
        change (syndromePinchOp sys (V.term r A) * sys.syndromeProjector ν) χ = _
        rw [h_pinch_ν]
        rfl
      have h_adj : (sys.syndromeProjector ν)† = sys.syndromeProjector ν :=
        ContinuousLinearMap.isSelfAdjoint_iff'.mp h_proj_ν.isSelfAdjoint
      have h_idem_ξ : sys.syndromeProjector ν ξ = ξ :=
        isStarProjection_apply_self h_proj_ν χ
      have h_inner_eq :
          inner ℂ ξ (syndromePinchOp sys (V.term r A) ξ) =
            inner ℂ ξ (V.term r A ξ) := by
        rw [h_act, ← ContinuousLinearMap.adjoint_inner_left, h_adj, h_idem_ξ]
      have h_ξ_sq : ‖ξ‖ ^ 2 ≤ 1 := by
        have h1 : ‖ξ‖ ^ 2 ≤ ‖χ‖ ^ 2 := isStarProjection_norm_sq_apply_le h_proj_ν χ
        have h2 : ‖χ‖ ^ 2 ≤ 1 ^ 2 := pow_le_pow_left₀ (norm_nonneg χ) hχ 2
        linarith
      rw [h_inner_eq]
      calc |RCLike.re (inner ℂ ξ (V.term r A ξ))|
        _ ≤ ‖V.term r A‖ * ‖ξ‖ ^ 2 := abs_re_inner_le_opNorm_mul_norm_sq (V.term r A) ξ
        _ ≤ ‖V.term r A‖ * 1 := mul_le_mul_of_nonneg_left h_ξ_sq (norm_nonneg _)
        _ ≤ J * f r := by linarith
    have h1 := h_single σ ψ hψ
    have h2 := h_single τ φ hφ
    calc |RCLike.re (inner ℂ (sys.syndromeProjector σ ψ)
            (syndromePinchOp sys (V.term r A) (sys.syndromeProjector σ ψ))) -
          RCLike.re (inner ℂ (sys.syndromeProjector τ φ)
            (syndromePinchOp sys (V.term r A) (sys.syndromeProjector τ φ)))|
      _ ≤ |RCLike.re (inner ℂ (sys.syndromeProjector σ ψ)
            (syndromePinchOp sys (V.term r A) (sys.syndromeProjector σ ψ)))| +
          |RCLike.re (inner ℂ (sys.syndromeProjector τ φ)
            (syndromePinchOp sys (V.term r A) (sys.syndromeProjector τ φ)))| :=
          abs_sub _ _
      _ ≤ J * f r + J * f r := add_le_add h1 h2
      _ = 2 * J * f r := by ring

/-- **Connected Check-Witness Cover Cardinality and Klarner Bound (`connected_check_witness_cover_card_and_klarner_bound`, Part II, Lemma 3.3 (`lem:klarner-bound`))**:
Derives the minimum witness size `∀ W ∈ W_cover, d_min ≤ W.card` and the Klarner shell animal bound
`∀ s : ℕ, ((W_cover.filter (fun W => W.card = d_min + s)).card : ℝ) ≤ klarnerAnimalConst ^ (d_min + s)`
directly from `IsConnectedCheckWitnessCover` and `kp_klarner_connected_polymer_count_le`. -/
theorem connected_check_witness_cover_card_and_klarner_bound
    {ι_chk : Type} [Fintype ι_chk] [DecidableEq ι_chk]
    (adj : ι_chk → ι_chk → Prop) [DecidableRel adj]
    (S_safe : Finset (ι_chk → Bool)) (W_cover : Finset (Finset ι_chk))
    (v_0 : ι_chk) (Δ_adj d_min : ℕ)
    (h_conn_cover : IsConnectedCheckWitnessCover adj S_safe W_cover v_0 Δ_adj d_min) :
    (∀ W ∈ W_cover, d_min ≤ W.card) ∧
    (∀ s : ℕ,
      ((W_cover.filter (fun W => W.card = d_min + s)).card : ℝ) ≤
        klarnerAnimalConst ^ (d_min + s)) := by
  refine ⟨fun W hW => (h_conn_cover.2.2.2.2 W hW).1, fun s => ?_⟩
  have hK_pos : 0 < klarnerAnimalConst := by unfold klarnerAnimalConst; positivity
  by_cases h_ne : (W_cover.filter (fun W => W.card = d_min + s)).Nonempty
  · rcases h_ne with ⟨W₀, hW₀⟩
    rcases Finset.mem_filter.mp hW₀ with ⟨hW₀_mem, hW₀_card⟩
    have hv₀_W₀ : v_0 ∈ W₀ := (h_conn_cover.2.2.2.2 W₀ hW₀_mem).2.1
    have h_card_pos : 1 ≤ d_min + s := by
      have : 0 < W₀.card := Finset.card_pos.mpr ⟨v_0, hv₀_W₀⟩
      omega
    let Δ := max 4 Δ_adj
    have hΔ4 : 4 ≤ Δ := le_max_left 4 Δ_adj
    have hΔ_le : Δ ≤ 168 := max_le (by norm_num) h_conn_cover.2.2.1
    have h_deg : ∀ u : ι_chk, (Finset.univ.filter (adj u)).card ≤ Δ := fun u =>
      le_trans (h_conn_cover.2.2.2.1 u) (le_max_right 4 Δ_adj)
    have h_sub : W_cover.filter (fun W => W.card = d_min + s) ⊆
        Finset.univ.filter (fun S : Finset ι_chk =>
          v_0 ∈ S ∧ S.card = d_min + s ∧ KPIsConnectedSubgraph adj S) := by
      intro W hW
      rcases Finset.mem_filter.mp hW with ⟨hW_mem, hW_card⟩
      have hW_prop := h_conn_cover.2.2.2.2 W hW_mem
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ W, hW_prop.2.1, hW_card, hW_prop.2.2⟩
    have h_card_sub :
        ((W_cover.filter (fun W => W.card = d_min + s)).card : ℝ) ≤
          ((Finset.univ.filter (fun S : Finset ι_chk =>
            v_0 ∈ S ∧ S.card = d_min + s ∧ KPIsConnectedSubgraph adj S)).card : ℝ) := by
      exact_mod_cast Finset.card_le_card h_sub
    have h_klarner := (kp_klarner_connected_polymer_count_le adj h_conn_cover.2.1 hΔ4 h_deg v_0
      h_card_pos (ε := 0) le_rfl).1
    have h_base_le : ((Δ : ℝ) ^ 2) ≤ klarnerAnimalConst := by
      unfold klarnerAnimalConst
      have hΔ_real : (Δ : ℝ) ≤ 168 := by exact_mod_cast hΔ_le
      have hΔ_nn : (0 : ℝ) ≤ (Δ : ℝ) := Nat.cast_nonneg Δ
      have h_sq : (Δ : ℝ) ^ 2 ≤ 28224 := by nlinarith
      have h_exp : (1 : ℝ) ≤ Real.exp 1 := Real.one_le_exp zero_le_one
      linarith
    have h_pow_le : ((Δ : ℝ) ^ 2) ^ (d_min + s) ≤ klarnerAnimalConst ^ (d_min + s) :=
      pow_le_pow_left₀ (by positivity) h_base_le (d_min + s)
    exact le_trans h_card_sub (le_trans h_klarner h_pow_le)
  · rw [Finset.not_nonempty_iff_eq_empty.mp h_ne, Finset.card_empty, Nat.cast_zero]
    positivity

/-- For any `f` in `InPerturbationClassSuper`, `f r ≤ 1` for all `r : ℕ`. -/
lemma inPerturbationClassSuper_le_one {f : ℕ → ℝ} (h_f : InPerturbationClassSuper f) (r : ℕ) :
    f r ≤ 1 := by
  have h1 := h_f.2.1 0 r (Nat.zero_le r)
  rwa [h_f.2.2.1] at h1

/-- The truncated perturbation at cutoff scale `R_cut`, packaged as a `QuasiLocalPerturbation`. -/
def scaleSplitTruncatedPerturbation {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    (V : QuasiLocalPerturbation D L Site) (R_cut : ℕ) :
    QuasiLocalPerturbation D L Site where
  term r A := if r ≤ R_cut then V.term r A else 0
  is_selfAdjoint r A := by
    split_ifs
    · exact V.is_selfAdjoint r A
    · exact ContinuousLinearMap.isSelfAdjoint_iff'.mpr (map_zero _)
  is_supported r hr A hA := by
    split_ifs
    · exact V.is_supported r hr A hA
    · exact ⟨0, by ext ψ σ; rfl⟩

/-- The total operator `.V_tot` of `scaleSplitTruncatedPerturbation V R_cut` is `scaleSplitTruncatedOp V R_cut`. -/
lemma scaleSplitTruncatedPerturbation_V_tot {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    (V : QuasiLocalPerturbation D L Site) (R_cut : ℕ) :
    (scaleSplitTruncatedPerturbation V R_cut).totalPerturbation = scaleSplitTruncatedOp V R_cut := by
  unfold QuasiLocalPerturbation.totalPerturbation scaleSplitTruncatedOp scaleSplitTruncatedPerturbation
  (try dsimp only)
  have h_filter_le : Finset.Icc 1 (min R_cut L) =
      (Finset.Icc 1 L).filter (fun r => r ≤ R_cut) := by
    ext r
    simp only [Finset.mem_Icc, Finset.mem_filter, le_min_iff]
    omega
  have h_filter_gt : ∀ r ∈ (Finset.Icc 1 L).filter (fun r => ¬ r ≤ R_cut),
      (∑ A ∈ boxCubes D L r, if r ≤ R_cut then V.term r A else 0) = 0 := by
    intro r hr
    have h_not : ¬ r ≤ R_cut := (Finset.mem_filter.mp hr).2
    refine Finset.sum_eq_zero fun A _ => ?_
    rw [if_neg h_not]
  rw [← Finset.sum_filter_add_sum_filter_not (Finset.Icc 1 L) (fun r => r ≤ R_cut)]
  rw [Finset.sum_eq_zero h_filter_gt, add_zero, ← h_filter_le]
  refine Finset.sum_congr rfl fun r hr => Finset.sum_congr rfl fun A _ => ?_
  have hr_le : r ≤ R_cut := le_trans (Finset.mem_Icc.mp hr).2 (min_le_left R_cut L)
  rw [if_pos hr_le]

/-- `pauliDiagonalPart` of `scaleSplitTruncatedPerturbation V R_cut` at scale `R_cut` equals `pauliDiagonalPart sys V R_cut`. -/
lemma scaleSplitTruncatedPerturbation_pauliDiagonalPart {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    {ι_chk : Type} [Fintype ι_chk] [DecidableEq ι_chk]
    (sys : IndexedCommutingProjectorHamiltonian D L Site ι_chk)
    (V : QuasiLocalPerturbation D L Site) (R_cut : ℕ) :
    pauliDiagonalPart sys (scaleSplitTruncatedPerturbation V R_cut) R_cut =
      pauliDiagonalPart sys V R_cut := by
  unfold pauliDiagonalPart scaleSplitTruncatedPerturbation
  refine Finset.sum_congr rfl fun r hr => Finset.sum_congr rfl fun A _ => ?_
  have hr_le : r ≤ R_cut := le_trans (Finset.mem_Icc.mp hr).2 (min_le_left R_cut L)
  (try dsimp only)
  rw [if_pos hr_le]

/-- Under `InPerturbationClassSuper f` and `HasQuasiLocalDecayBound V J f`, `scaleSplitTruncatedPerturbation V R_cut`
    satisfies `HasFiniteRangeBound _ R_cut J`. -/
lemma scaleSplitTruncatedPerturbation_hasFiniteRangeBound {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    (V : QuasiLocalPerturbation D L Site) (R_cut : ℕ) (J : ℝ) (f : ℕ → ℝ)
    (hJ : 0 ≤ J) (h_f : InPerturbationClassSuper f)
    (h_ql : HasQuasiLocalDecayBound V J f) :
    HasFiniteRangeBound (scaleSplitTruncatedPerturbation V R_cut) R_cut J := by
  intro r hr A hA
  refine ⟨fun hr_le => ?_, fun hr_gt => ?_⟩
  · unfold scaleSplitTruncatedPerturbation
    (try dsimp only)
    rw [if_pos hr_le]
    calc ‖V.term r A‖
      _ ≤ J * f r := (h_ql.1 r hr A hA).2
      _ ≤ J * 1 := mul_le_mul_of_nonneg_left (inPerturbationClassSuper_le_one h_f r) hJ
      _ = J := mul_one J
  · unfold scaleSplitTruncatedPerturbation
    (try dsimp only)
    exact if_neg (not_le_of_gt hr_gt)

/-- When `InPerturbationClassFin f r_pert` and `r_pert ≤ R_cut`, `scaleSplitTailOp V R_cut = 0` and
    `V.V_tot = scaleSplitTruncatedOp V R_cut`. -/
lemma scaleSplitTailOp_eq_zero_of_inPerturbationClassFin {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    (V : QuasiLocalPerturbation D L Site) (r_pert R_cut : ℕ) (J : ℝ) (f : ℕ → ℝ)
    (h_ql : HasQuasiLocalDecayBound V J f)
    (h_fin : InPerturbationClassFin f r_pert) (hr_le : r_pert ≤ R_cut) :
    scaleSplitTailOp V R_cut = 0 ∧ V.totalPerturbation = scaleSplitTruncatedOp V R_cut := by
  have h_tail_zero : scaleSplitTailOp V R_cut = 0 := by
    unfold scaleSplitTailOp
    refine Finset.sum_eq_zero fun r hr => Finset.sum_eq_zero fun A hA => ?_
    rcases Finset.mem_filter.mp hr with ⟨hr_Icc, hr_gt⟩
    have hf_zero : f r = 0 := h_fin.2 r (lt_of_le_of_lt hr_le hr_gt)
    have h_norm : ‖V.term r A‖ ≤ 0 := by
      calc ‖V.term r A‖
        _ ≤ J * f r := (h_ql.1 r hr_Icc A hA).2
        _ = 0 := by rw [hf_zero, mul_zero]
    exact norm_le_zero_iff.mp h_norm
  refine ⟨h_tail_zero, ?_⟩
  have h_filter_le : Finset.Icc 1 (min R_cut L) =
      (Finset.Icc 1 L).filter (fun r => r ≤ R_cut) := by
    ext r; simp only [Finset.mem_Icc, Finset.mem_filter, le_min_iff]; omega
  have h_filter_gt : (Finset.Icc 1 L).filter (fun r => R_cut < r) =
      (Finset.Icc 1 L).filter (fun r => ¬ r ≤ R_cut) := by
    ext r; simp only [Finset.mem_filter, not_le]
  have h_split : V.totalPerturbation = scaleSplitTruncatedOp V R_cut + scaleSplitTailOp V R_cut := by
    unfold QuasiLocalPerturbation.totalPerturbation scaleSplitTruncatedOp scaleSplitTailOp
    rw [h_filter_le, h_filter_gt, Finset.sum_filter_add_sum_filter_not]
  rw [h_split, h_tail_zero, add_zero]

/-- **Super-Polynomial Collar and Scale-Split Decomposition (`superpolynomial_collar_and_scale_split_decomp`)**:
Combines Part II, Lemma 2.4 (`lem:D-super-closure`) (`rcaCollarConstant_le_pi_sq_div_six_mul_moment5`),
Part II, Lemma 3.3 (`lem:klarner-bound`) (`connected_check_witness_cover_card_and_klarner_bound` and `klarner_animal_shell_sum_bound`),
and Part II, Proposition 3.4 (`prop:pauli-diag-off`) (`pauliDiagOffDecomposition_local_shift_le`). -/
theorem superpolynomial_collar_and_scale_split_decomp {L N_checks : ℕ}
    {Site0 : Type} [Fintype Site0] [DecidableEq Site0]
    (sys : ℋ_CP[L, Site0, N_checks])
    (V : 𝒱_pert[L, Site0])
    (f : ℕ → ℝ) (c_chk r_0 R_cut Δ_adj d_min : ℕ) (C_RCA M_5 J κ : ℝ)
    (adj : Fin N_checks → Fin N_checks → Prop) [DecidableRel adj]
    (S_safe : Finset (Fin N_checks → Bool))
    (W_cover : Finset (Finset (Fin N_checks)))
    (v_0 : Fin N_checks)
    (hc_chk : 1 ≤ c_chk) (hr_0 : 1 ≤ r_0) (hC_RCA : 0 ≤ C_RCA)
    (hM5 : HasDecayMomentBound f 5 M_5) (h_summable : Summable f)
    (hJ : 0 ≤ J) (h_ql : HasQuasiLocalDecayBound V J f)
    (h_conn_cover : IsConnectedCheckWitnessCover adj S_safe W_cover v_0 Δ_adj d_min)
    (hκ : Real.log klarnerAnimalConst + 1 ≤ κ) :
    ((∀ r : ℕ,
      (activeCheckFootprintBound c_chk r_0 (rcaCollarRadius C_RCA r_0 r) : ℝ) ≤
        rcaCollarEnvelopeConst c_chk r_0 C_RCA * ((1 + (r : ℝ)) ^ 3)) ∧
    (∀ L_star : ℕ, rcaCollarFiniteSum f c_chk r_0 L_star C_RCA ≤ rcaCollarSeries f c_chk r_0 C_RCA) ∧
    rcaCollarSeries f c_chk r_0 C_RCA ≤
      (Real.pi ^ 2 / 6) * rcaCollarEnvelopeConst c_chk r_0 C_RCA * M_5 ∧
    (∀ R : ℕ, 1 ≤ R →
      perturbationTailSeries f R ≤ (Real.pi ^ 2 / 6) * M_5 / ((R : ℝ) ^ 3)) ∧
    (∀ r_pert R : ℕ, InPerturbationClassFin f r_pert → r_pert ≤ R →
      perturbationTailSeries f R = 0)) ∧
    ((∀ W ∈ W_cover, d_min ≤ W.card) ∧
    (∀ s : ℕ,
      ((W_cover.filter (fun W => W.card = d_min + s)).card : ℝ) ≤
        klarnerAnimalConst ^ (d_min + s)) ∧
    (∑ W ∈ W_cover, Real.exp (-κ * (W.card : ℝ))) ≤
      (∑' s : ℕ, (klarnerAnimalConst * Real.exp (-κ)) ^ (d_min + s)) ∧
    (∑ W ∈ W_cover, Real.exp (-κ * (W.card : ℝ))) ≤
      2 * Real.exp (-(κ - Real.log klarnerAnimalConst) * (d_min : ℝ))) ∧
    (V.totalPerturbation = scaleSplitTruncatedOp V R_cut + scaleSplitTailOp V R_cut ∧
    IsSelfAdjoint (scaleSplitTruncatedOp V R_cut) ∧
    IsSelfAdjoint (scaleSplitTailOp V R_cut) ∧
    ‖scaleSplitTailOp V R_cut‖ ≤
      J * ((L ^ 3 : ℕ) : ℝ) * perturbationTailSeries f R_cut ∧
    scaleSplitTruncatedOp V R_cut =
      pauliDiagonalPart sys V R_cut + pauliOffDiagonalPart sys V R_cut ∧
    (∀ r A, V.term r A = syndromePinchOp sys (V.term r A) + pauliOffDiagonalTerm sys V r A) ∧
    (∀ r A σ, Commute (syndromePinchOp sys (V.term r A)) (sys.syndromeProjector σ)) ∧
    (∀ r A σ,
      sys.syndromeProjector σ * pauliOffDiagonalTerm sys V r A * sys.syndromeProjector σ = 0) ∧
    (∀ r ∈ Finset.Icc 1 L, ∀ A ∈ boxCubes 3 L r, ∀ σ τ : Fin N_checks → Bool,
      ∀ ψ φ : ℋ[L, Site0], ‖ψ‖ ≤ 1 → ‖φ‖ ≤ 1 →
        |RCLike.re (inner ℂ (sys.syndromeProjector σ ψ)
            (syndromePinchOp sys (V.term r A) (sys.syndromeProjector σ ψ))) -
          RCLike.re (inner ℂ (sys.syndromeProjector τ φ)
            (syndromePinchOp sys (V.term r A) (sys.syndromeProjector τ φ)))| ≤
          2 * J * f r)) := by
  have h_conn := connected_check_witness_cover_card_and_klarner_bound
    adj S_safe W_cover v_0 Δ_adj d_min h_conn_cover
  have h_shell := klarner_animal_shell_sum_bound W_cover d_min κ h_conn.1 h_conn.2 hκ
  exact ⟨rcaCollarConstant_le_pi_sq_div_six_mul_moment5 f c_chk r_0 C_RCA M_5 hc_chk hr_0 hC_RCA hM5,
    ⟨h_conn.1, h_conn.2, h_shell.1, h_shell.2⟩,
    pauliDiagOffDecomposition_local_shift_le sys V J f R_cut hJ hM5.1 h_summable h_ql⟩

/-- Witness collar partition and operator norm bound `‖W_in‖ ≤ 3 * J * Δ_RCA * W.card`
    for `pauliDiagonalPart sys V R_cut`. -/
lemma exists_pauliDiagonal_witness_collar_split
    {L q_code r_0 m_max w_0 R_cut : ℕ} [NeZero L]
    (D_field : Box3D L → LocalCSSDescriptor q_code r_0 m_max)
    (sys : IndexedCommutingProjectorHamiltonian 3 L
      (UniformSite3D L (CodeSlotConfig q_code)) (StaticCSSCheckIdx L q_code m_max))
    (h_sys_checks : ∀ idx, sys.checkProj idx = staticCSSCheckProj D_field idx ∧
      sys.support idx = staticCSSCheckSupport D_field idx ∧ sys.weight idx = 1)
    (V : QuasiLocalPerturbation 3 L (UniformSite3D L (CodeSlotConfig q_code))) (f : ℕ → ℝ)
    (C_RCA Δ_RCA J : ℝ)
    (hC_RCA : 0 ≤ C_RCA) (hJ_nn : 0 ≤ J) (hΔ_RCA : 0 < Δ_RCA)
    (hf_super : InPerturbationClassSuper f) (h_ql : HasQuasiLocalDecayBound V J f)
    (h_rca_cal : rcaDiagonalCoercivityConstant 3 R_cut r_0 w_0 C_RCA ≤ Δ_RCA)
    (W : Finset (StaticCSSCheckIdx L q_code m_max)) :
    ∃ W_out W_in : ManyBodyHilbertSpace (UniformSite3D L (CodeSlotConfig q_code)) →L[ℂ]
        ManyBodyHilbertSpace (UniformSite3D L (CodeSlotConfig q_code)),
      IsSelfAdjoint W_out ∧ IsSelfAdjoint W_in ∧
      pauliDiagonalPart sys V R_cut = W_out + W_in ∧
      (∀ σ, Commute W_out (sys.syndromeProjector σ) ∧ Commute W_in (sys.syndromeProjector σ)) ∧
      ‖W_in‖ ≤ 3 * J * Δ_RCA * (W.card : ℝ) := by
  let D_loc (r : ℕ) (A : Finset (Box3D L)) := syndromePinchOp sys (V.term r A)
  let W_out := collarSpectatorPart sys C_RCA R_cut D_loc W
  let W_in := collarWitnessPart sys C_RCA R_cut D_loc W
  have hD_props : ∀ r A, IsSelfAdjoint (D_loc r A) ∧
      ∀ σ, Commute (D_loc r A) (sys.syndromeProjector σ) := fun r A => by
    have h := syndromePinchOp_isSelfAdjoint_and_commute_checkProj sys (V.is_selfAdjoint r A)
    exact ⟨h.1, fun σ => (h.2.1 σ).2.2⟩
  have h_split := (local_collar_partition_split_around_witness sys C_RCA R_cut D_loc W).1
  refine ⟨W_out, W_in,
    _root_.isSelfAdjoint_finset_sum _ _ fun r _ =>
      _root_.isSelfAdjoint_finset_sum _ _ fun A _ => (hD_props r A).1,
    _root_.isSelfAdjoint_finset_sum _ _ fun r _ =>
      _root_.isSelfAdjoint_finset_sum _ _ fun A _ => (hD_props r A).1,
    by unfold pauliDiagonalPart; rw [h_split, add_comm],
    fun σ => ⟨Commute.sum_left _ _ _ fun r _ => Commute.sum_left _ _ _ fun A _ => (hD_props r A).2 σ,
      Commute.sum_left _ _ _ fun r _ => Commute.sum_left _ _ _ fun A _ => (hD_props r A).2 σ⟩,
    ?_⟩
  let K_geom : ℕ :=
    (2 * (R_cut + 2 * linearExpansionRadius C_RCA R_cut + r_0) + 1) ^ 3 * (w_0 + 1)
  have h_r_bound : ∀ r ∈ Finset.Icc 1 (min R_cut L),
      ‖∑ A ∈ (boxCubes 3 L r).filter (fun A => ¬Disjoint (rcaCollarChecks sys C_RCA r A) W),
        D_loc r A‖ ≤ ((W.card * K_geom : ℕ) : ℝ) * J := by
    intro r hr
    have hr_IccL : r ∈ Finset.Icc 1 L := Finset.mem_Icc.mpr
      ⟨(Finset.mem_Icc.mp hr).1, le_trans (Finset.mem_Icc.mp hr).2 (Nat.min_le_right R_cut L)⟩
    let S_r := (boxCubes 3 L r).filter (fun A => ¬Disjoint (rcaCollarChecks sys C_RCA r A) W)
    have h_sub : S_r ⊆ W.biUnion (fun c =>
        (boxCubes 3 L r).filter (fun A => c ∈ rcaCollarChecks sys C_RCA r A)) := by
      intro A hA
      rcases Finset.mem_filter.mp hA with ⟨hA_mem, h_nd⟩
      rcases Finset.not_disjoint_iff.mp h_nd with ⟨c, hc_col, hc_W⟩
      exact Finset.mem_biUnion.mpr ⟨c, hc_W, Finset.mem_filter.mpr ⟨hA_mem, hc_col⟩⟩
    have h_card : S_r.card ≤ W.card * K_geom := by
      calc S_r.card
        _ ≤ (W.biUnion (fun c =>
              (boxCubes 3 L r).filter (fun A => c ∈ rcaCollarChecks sys C_RCA r A))).card :=
            Finset.card_le_card h_sub
        _ ≤ ∑ c ∈ W, ((boxCubes 3 L r).filter (fun A => c ∈ rcaCollarChecks sys C_RCA r A)).card :=
            Finset.card_biUnion_le
        _ ≤ W.card • K_geom := Finset.sum_le_card_nsmul W _ K_geom
            (fun c _ => card_filter_mem_rcaCollarChecks_le D_field sys h_sys_checks hC_RCA hr c)
        _ = W.card * K_geom := smul_eq_mul _ _
    have h_term : ∀ A ∈ S_r, ‖D_loc r A‖ ≤ J := by
      intro A hA
      have hA_cube : A ∈ boxCubes 3 L r := (Finset.mem_filter.mp hA).1
      have h_pinch := (syndromePinchOp_norm_and_isSupportedOn_of_staticCSSCheck
        D_field sys h_sys_checks A (V.is_supported r hr_IccL A hA_cube)).1
      have h_V := (h_ql.1 r hr_IccL A hA_cube).2
      have h_f := inPerturbationClassSuper_le_one hf_super r
      calc ‖D_loc r A‖
        _ ≤ ‖V.term r A‖ := h_pinch
        _ ≤ J * f r := h_V
        _ ≤ J * 1 := mul_le_mul_of_nonneg_left h_f hJ_nn
        _ = J := mul_one J
    calc ‖∑ A ∈ S_r, D_loc r A‖
      _ ≤ ∑ A ∈ S_r, ‖D_loc r A‖ := norm_sum_le S_r _
      _ ≤ S_r.card • J := Finset.sum_le_card_nsmul S_r _ J h_term
      _ = (S_r.card : ℝ) * J := nsmul_eq_mul _ _
      _ ≤ ((W.card * K_geom : ℕ) : ℝ) * J :=
          mul_le_mul_of_nonneg_right (by exact_mod_cast h_card) hJ_nn
  have h_sum_r : ‖W_in‖ ≤ ((Finset.Icc 1 (min R_cut L)).card : ℝ) * (((W.card * K_geom : ℕ) : ℝ) * J) := by
    unfold W_in collarWitnessPart
    calc ‖∑ r ∈ Finset.Icc 1 (min R_cut L),
            ∑ A ∈ (boxCubes 3 L r).filter (fun A => ¬Disjoint (rcaCollarChecks sys C_RCA r A) W), D_loc r A‖
      _ ≤ ∑ r ∈ Finset.Icc 1 (min R_cut L),
            ‖∑ A ∈ (boxCubes 3 L r).filter (fun A => ¬Disjoint (rcaCollarChecks sys C_RCA r A) W), D_loc r A‖ :=
          norm_sum_le _ _
      _ ≤ (Finset.Icc 1 (min R_cut L)).card • (((W.card * K_geom : ℕ) : ℝ) * J) :=
          Finset.sum_le_card_nsmul _ _ _ h_r_bound
      _ = ((Finset.Icc 1 (min R_cut L)).card : ℝ) * (((W.card * K_geom : ℕ) : ℝ) * J) :=
          nsmul_eq_mul _ _
  have h_card_Icc : ((Finset.Icc 1 (min R_cut L)).card : ℝ) ≤ (R_cut : ℝ) := by
    have h_nat : (Finset.Icc 1 (min R_cut L)).card ≤ R_cut := by
      rw [Nat.card_Icc]; have := Nat.min_le_left R_cut L; omega
    exact_mod_cast h_nat
  have h_le_rca : ‖W_in‖ ≤ rcaDiagonalCoercivityConstant 3 R_cut r_0 w_0 C_RCA * J * (W.card : ℝ) := by
    have h1 := le_trans h_sum_r (mul_le_mul_of_nonneg_right h_card_Icc (by positivity))
    have h_eq : (R_cut : ℝ) * (((W.card * K_geom : ℕ) : ℝ) * J) =
        rcaDiagonalCoercivityConstant 3 R_cut r_0 w_0 C_RCA * J * (W.card : ℝ) := by
      unfold rcaDiagonalCoercivityConstant
      dsimp [K_geom]; push_cast; ring
    linarith
  have h_cal_mul :
      rcaDiagonalCoercivityConstant 3 R_cut r_0 w_0 C_RCA * J * (W.card : ℝ) ≤
        3 * J * Δ_RCA * (W.card : ℝ) := by
    have h1 : rcaDiagonalCoercivityConstant 3 R_cut r_0 w_0 C_RCA ≤ 3 * Δ_RCA := by linarith
    have h2 : rcaDiagonalCoercivityConstant 3 R_cut r_0 w_0 C_RCA * J ≤ 3 * J * Δ_RCA := by
      calc rcaDiagonalCoercivityConstant 3 R_cut r_0 w_0 C_RCA * J
        _ ≤ (3 * Δ_RCA) * J := mul_le_mul_of_nonneg_right h1 hJ_nn
        _ = 3 * J * Δ_RCA := by ring
    exact mul_le_mul_of_nonneg_right h2 (Nat.cast_nonneg _)
  exact le_trans h_le_rca h_cal_mul

set_option maxRecDepth 200000
set_option maxHeartbeats 3200000

local notation "SiteCSS[" L ", " q_code "]" => UniformSite3D L (CodeSlotConfig q_code)
local notation "ℋ_CSS[" L ", " q_code "]" => ManyBodyHilbertSpace (SiteCSS[L, q_code])
local notation "ℬ_CSS[" L ", " q_code "]" => ℋ_CSS[L, q_code] →L[ℂ] ℋ_CSS[L, q_code]
local notation "IdxCSS[" L ", " q_code ", " m_max "]" => StaticCSSCheckIdx L q_code m_max
local notation "SysCSS[" L ", " q_code ", " m_max "]" =>
  IndexedCommutingProjectorHamiltonian 3 L (SiteCSS[L, q_code]) (IdxCSS[L, q_code, m_max])

/-- **Witness Coset Trace Diagonal Reduction (`witnessCoset_trace_diagonal_reduction`, Part II, Proposition 3.5 (`prop:witness-coset-reduction`))**:
Given a syndrome set `W_event` corresponding to a positive check witness of cardinality `m`,
an injective coset clearing map `τ_W : ι_synd ↪ ι_synd` that drops the bare syndrome energy `E_0`
by at least `2 * Δ_0 * m`, and a multi-scale diagonal perturbation `V_diag` whose scale-`r` terms
`V_term r A` only change when `W` intersects the `r`-collar of `A` (counted by `collarHitCount r A`
with total hits per scale `r` at most `m * activeCheckFootprintBound c_chk r_0 (rcaCollarRadius C_RCA r_0 r)`),
the total diagonal shift is bounded by `|V_diag σ - V_diag (τ_W σ)| ≤ 2 * J * Δ_RCA * m`
whenever `rcaCollarFiniteSum f c_chk r_0 L_star C_RCA ≤ Δ_RCA`, and the restricted diagonal
Boltzmann sum over `W_event` is bounded by `exp(-β * (2 * Δ_0 - 2 * J * Δ_RCA) * m)` times the
full diagonal partition sum. -/
theorem witnessCoset_trace_diagonal_reduction
    {ι_synd : Type*} [Fintype ι_synd] [DecidableEq ι_synd]
    {ι_cube : ℕ → Type*} [∀ r, Fintype (ι_cube r)] [∀ r, DecidableEq (ι_cube r)]
    (W_event : Finset ι_synd)
    (τ_W : ι_synd ↪ ι_synd)
    (E_0 V_diag : ι_synd → ℝ)
    (V_term : (r : ℕ) → ι_cube r → ι_synd → ℝ)
    (collarHitCount : (r : ℕ) → ι_cube r → ℕ)
    (f : ℕ → ℝ) (c_chk r_0 L_star : ℕ) (C_RCA β Δ_0 J Δ_RCA : ℝ) (m : ℕ)
    (hβ : 0 ≤ β) (hJ : 0 ≤ J) (hf : ∀ r, 0 ≤ f r)
    (h_energy_drop : ∀ σ ∈ W_event, E_0 (τ_W σ) ≤ E_0 σ - 2 * Δ_0 * (m : ℝ))
    (h_V_decomp : ∀ σ : ι_synd,
      V_diag σ = ∑ r ∈ Finset.Icc 1 L_star, ∑ A : ι_cube r, V_term r A σ)
    (h_local_collar : ∀ r ∈ Finset.Icc 1 L_star, ∀ A : ι_cube r, ∀ σ ∈ W_event,
      |V_term r A σ - V_term r A (τ_W σ)| ≤ 2 * J * f r * (collarHitCount r A : ℝ))
    (h_hit_sum : ∀ r ∈ Finset.Icc 1 L_star,
      (∑ A : ι_cube r, collarHitCount r A) ≤
        m * activeCheckFootprintBound c_chk r_0 (rcaCollarRadius C_RCA r_0 r))
    (h_collar_le : rcaCollarFiniteSum f c_chk r_0 L_star C_RCA ≤ Δ_RCA) :
    (∀ σ ∈ W_event, |V_diag σ - V_diag (τ_W σ)| ≤ 2 * J * Δ_RCA * (m : ℝ)) ∧
    (∑ σ ∈ W_event, Real.exp (-β * (E_0 σ + V_diag σ))) ≤
      Real.exp (-β * (2 * Δ_0 - 2 * J * Δ_RCA) * (m : ℝ)) *
        (∑ σ : ι_synd, Real.exp (-β * (E_0 σ + V_diag σ))) := by
  have h_shift : ∀ σ ∈ W_event, |V_diag σ - V_diag (τ_W σ)| ≤ 2 * J * Δ_RCA * (m : ℝ) := by
    intro σ hσ
    rw [h_V_decomp σ, h_V_decomp (τ_W σ), ← Finset.sum_sub_distrib]
    have h1 :
        |∑ r ∈ Finset.Icc 1 L_star, (∑ A : ι_cube r, V_term r A σ - ∑ A : ι_cube r, V_term r A (τ_W σ))| ≤
          ∑ r ∈ Finset.Icc 1 L_star, |∑ A : ι_cube r, V_term r A σ - ∑ A : ι_cube r, V_term r A (τ_W σ)| :=
      Finset.abs_sum_le_sum_abs _ _
    have h2 : ∀ r ∈ Finset.Icc 1 L_star,
        |∑ A : ι_cube r, V_term r A σ - ∑ A : ι_cube r, V_term r A (τ_W σ)| ≤
          2 * J * (m : ℝ) * (f r * (activeCheckFootprintBound c_chk r_0 (rcaCollarRadius C_RCA r_0 r) : ℝ)) := by
      intro r hr
      rw [← Finset.sum_sub_distrib]
      have h_tri :
          |∑ A : ι_cube r, (V_term r A σ - V_term r A (τ_W σ))| ≤
            ∑ A : ι_cube r, |V_term r A σ - V_term r A (τ_W σ)| :=
        Finset.abs_sum_le_sum_abs _ _
      have h_loc :
          (∑ A : ι_cube r, |V_term r A σ - V_term r A (τ_W σ)|) ≤
            ∑ A : ι_cube r, 2 * J * f r * (collarHitCount r A : ℝ) :=
        Finset.sum_le_sum (fun A _ => h_local_collar r hr A σ hσ)
      have h_factor :
          (∑ A : ι_cube r, 2 * J * f r * (collarHitCount r A : ℝ)) =
            2 * J * f r * ((∑ A : ι_cube r, collarHitCount r A : ℕ) : ℝ) := by
        rw [← Finset.mul_sum, Nat.cast_sum]
      have h_hits_real :
          ((∑ A : ι_cube r, collarHitCount r A : ℕ) : ℝ) ≤
            (m : ℝ) * (activeCheckFootprintBound c_chk r_0 (rcaCollarRadius C_RCA r_0 r) : ℝ) := by
        exact_mod_cast h_hit_sum r hr
      have h_nonneg : 0 ≤ 2 * J * f r := by
        have := hf r
        positivity
      calc |∑ A : ι_cube r, (V_term r A σ - V_term r A (τ_W σ))|
        _ ≤ ∑ A : ι_cube r, |V_term r A σ - V_term r A (τ_W σ)| := h_tri
        _ ≤ ∑ A : ι_cube r, 2 * J * f r * (collarHitCount r A : ℝ) := h_loc
        _ = 2 * J * f r * ((∑ A : ι_cube r, collarHitCount r A : ℕ) : ℝ) := h_factor
        _ ≤ 2 * J * f r * ((m : ℝ) * (activeCheckFootprintBound c_chk r_0 (rcaCollarRadius C_RCA r_0 r) : ℝ)) :=
            mul_le_mul_of_nonneg_left h_hits_real h_nonneg
        _ = 2 * J * (m : ℝ) * (f r * (activeCheckFootprintBound c_chk r_0 (rcaCollarRadius C_RCA r_0 r) : ℝ)) := by ring
    calc |∑ r ∈ Finset.Icc 1 L_star, (∑ A : ι_cube r, V_term r A σ - ∑ A : ι_cube r, V_term r A (τ_W σ))|
      _ ≤ ∑ r ∈ Finset.Icc 1 L_star, |∑ A : ι_cube r, V_term r A σ - ∑ A : ι_cube r, V_term r A (τ_W σ)| := h1
      _ ≤ ∑ r ∈ Finset.Icc 1 L_star,
            2 * J * (m : ℝ) * (f r * (activeCheckFootprintBound c_chk r_0 (rcaCollarRadius C_RCA r_0 r) : ℝ)) :=
          Finset.sum_le_sum h2
      _ = 2 * J * (m : ℝ) * rcaCollarFiniteSum f c_chk r_0 L_star C_RCA := by
          unfold rcaCollarFiniteSum
          rw [← Finset.mul_sum]
      _ ≤ 2 * J * (m : ℝ) * Δ_RCA :=
          mul_le_mul_of_nonneg_left h_collar_le (by positivity)
      _ = 2 * J * Δ_RCA * (m : ℝ) := by ring
  refine ⟨h_shift, ?_⟩
  have h_term : ∀ σ ∈ W_event,
      Real.exp (-β * (E_0 σ + V_diag σ)) ≤
        Real.exp (-β * (2 * Δ_0 - 2 * J * Δ_RCA) * (m : ℝ)) *
          Real.exp (-β * (E_0 (τ_W σ) + V_diag (τ_W σ))) := by
    intro σ hσ
    have hE := h_energy_drop σ hσ
    have hV := (abs_le.mp (h_shift σ hσ)).1
    have h_sum_le :
        E_0 (τ_W σ) + V_diag (τ_W σ) ≤
          E_0 σ + V_diag σ - (2 * Δ_0 - 2 * J * Δ_RCA) * (m : ℝ) := by
      linarith
    have h_mul := mul_le_mul_of_nonneg_left h_sum_le hβ
    have h_exp_arg :
        -β * (E_0 σ + V_diag σ) ≤
          -β * (2 * Δ_0 - 2 * J * Δ_RCA) * (m : ℝ) + (-β * (E_0 (τ_W σ) + V_diag (τ_W σ))) := by
      linarith
    rw [← Real.exp_add]
    exact Real.exp_le_exp.mpr h_exp_arg
  calc (∑ σ ∈ W_event, Real.exp (-β * (E_0 σ + V_diag σ)))
    _ ≤ ∑ σ ∈ W_event,
          Real.exp (-β * (2 * Δ_0 - 2 * J * Δ_RCA) * (m : ℝ)) *
            Real.exp (-β * (E_0 (τ_W σ) + V_diag (τ_W σ))) :=
        Finset.sum_le_sum h_term
    _ = Real.exp (-β * (2 * Δ_0 - 2 * J * Δ_RCA) * (m : ℝ)) *
          (∑ σ ∈ W_event, Real.exp (-β * (E_0 (τ_W σ) + V_diag (τ_W σ)))) := by
        rw [← Finset.mul_sum]
    _ = Real.exp (-β * (2 * Δ_0 - 2 * J * Δ_RCA) * (m : ℝ)) *
          (∑ τ ∈ W_event.map τ_W, Real.exp (-β * (E_0 τ + V_diag τ))) := by
        rw [Finset.sum_map]
    _ ≤ Real.exp (-β * (2 * Δ_0 - 2 * J * Δ_RCA) * (m : ℝ)) *
          (∑ σ : ι_synd, Real.exp (-β * (E_0 σ + V_diag σ))) := by
        apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
        exact Finset.sum_le_univ_sum_of_nonneg (fun _ => (Real.exp_pos _).le)

/-- **Effective Coset Energy Gap and Suppression Rate Lower Bound
(`walshHadamard_coset_effective_energy_gap_ge`, Part II, Proposition 3.6 (`prop:walsh-coset-dominance`))**:
When `0 < Δ_0`, `0 < Δ_RCA`, `0 < c_wt`, `J ≤ worldlineCouplingThreshold Δ_0 Δ_RCA`, and
`criticalInverseTempHier Δ_0 < β`, we have:
1. `(13 / 8) * Δ_0 ≤ 2 * Δ_0 - 6 * J * Δ_RCA` (and in particular `(3 / 2) * Δ_0 ≤ 2 * Δ_0 - 6 * J * Δ_RCA`),
2. `c_wt * (3 / 2) * Δ_0 * (β - criticalInverseTempHier Δ_0) ≤ worldlineSuppressionRate c_wt Δ_0 Δ_RCA β J`,
3. `Real.log klarnerAnimalConst + 1 ≤ worldlineSuppressionRate c_wt Δ_0 Δ_RCA β J / c_wt + Real.log klarnerAnimalConst`. -/
theorem walshHadamard_coset_effective_energy_gap_ge
    (c_wt Δ_0 Δ_RCA β J : ℝ)
    (hc_wt : 0 < c_wt) (hΔ_0 : 0 < Δ_0) (hΔ_RCA : 0 < Δ_RCA)
    (hJ : J ≤ worldlineCouplingThreshold Δ_0 Δ_RCA)
    (hβ : criticalInverseTempHier Δ_0 < β) :
    (13 / 8 : ℝ) * Δ_0 ≤ 2 * Δ_0 - 6 * J * Δ_RCA ∧
    c_wt * (3 / 2 : ℝ) * Δ_0 * (β - criticalInverseTempHier Δ_0) ≤
      worldlineSuppressionRate c_wt Δ_0 Δ_RCA β J ∧
    Real.log klarnerAnimalConst + 1 ≤
      worldlineSuppressionRate c_wt Δ_0 Δ_RCA β J / c_wt + Real.log klarnerAnimalConst := by
  unfold worldlineCouplingThreshold at hJ
  have h16_pos : (0 : ℝ) < 16 * Δ_RCA := by positivity
  have hJ_mul : J * (16 * Δ_RCA) ≤ Δ_0 := (le_div_iff₀ h16_pos).mp hJ
  have h_gap_13_8 : (13 / 8 : ℝ) * Δ_0 ≤ 2 * Δ_0 - 6 * J * Δ_RCA := by linarith
  have h_gap_3_2 : (3 / 2 : ℝ) * Δ_0 ≤ 2 * Δ_0 - 6 * J * Δ_RCA := by linarith
  have h_klarner_ge_one : 1 ≤ klarnerAnimalConst := by
    unfold klarnerAnimalConst
    linarith [Real.one_le_exp zero_le_one]
  have h_log_nonneg : 0 ≤ Real.log klarnerAnimalConst := Real.log_nonneg h_klarner_ge_one
  have h_denom_pos : (0 : ℝ) < (3 / 2 : ℝ) * Δ_0 := by positivity
  have h_βc_pos : 0 < criticalInverseTempHier Δ_0 := by
    unfold criticalInverseTempHier
    exact div_pos (by linarith) h_denom_pos
  have hβ_pos : 0 < β := lt_trans h_βc_pos hβ
  have h_βc_mul :
      ((3 / 2 : ℝ) * Δ_0) * criticalInverseTempHier Δ_0 =
        Real.log klarnerAnimalConst + 2 := by
    unfold criticalInverseTempHier
    exact mul_div_cancel₀ (Real.log klarnerAnimalConst + 2) h_denom_pos.ne'
  have h_β_mul_le :
      β * ((3 / 2 : ℝ) * Δ_0) ≤ β * (2 * Δ_0 - 6 * J * Δ_RCA) :=
    mul_le_mul_of_nonneg_left h_gap_3_2 hβ_pos.le
  have h_prod_pos : 0 < ((3 / 2 : ℝ) * Δ_0) * (β - criticalInverseTempHier Δ_0) :=
    mul_pos h_denom_pos (sub_pos.mpr hβ)
  have h_core_le :
      ((3 / 2 : ℝ) * Δ_0) * (β - criticalInverseTempHier Δ_0) + 1 ≤
        β * (2 * Δ_0 - 6 * J * Δ_RCA) - Real.log klarnerAnimalConst - 1 := by
    linarith
  have h_rate_bound :
      c_wt * (3 / 2 : ℝ) * Δ_0 * (β - criticalInverseTempHier Δ_0) ≤
        worldlineSuppressionRate c_wt Δ_0 Δ_RCA β J := by
    unfold worldlineSuppressionRate
    have h_le :
        ((3 / 2 : ℝ) * Δ_0) * (β - criticalInverseTempHier Δ_0) ≤
          β * (2 * Δ_0 - 6 * J * Δ_RCA) - Real.log klarnerAnimalConst - 1 := by
      linarith
    have h_mul := mul_le_mul_of_nonneg_left h_le hc_wt.le
    linarith
  have h_klarner_thresh :
      Real.log klarnerAnimalConst + 1 ≤
        worldlineSuppressionRate c_wt Δ_0 Δ_RCA β J / c_wt + Real.log klarnerAnimalConst := by
    unfold worldlineSuppressionRate
    rw [mul_div_cancel_left₀ _ hc_wt.ne']
    linarith
  exact ⟨h_gap_13_8, h_rate_bound, h_klarner_thresh⟩

private lemma hdiag_mul_projector_eq_smul_local {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    {H0 P_diag P : E →L[ℂ] E} {E_vac E_sum e0 d_sum : ℝ}
    (h_H0 : H0 * P = ((e0 : ℝ) : ℂ) • P)
    (h_shift : (P_diag - ((E_sum : ℝ) : ℂ) • 1) * P = ((d_sum : ℝ) : ℂ) • P) :
    (H0 + P_diag - ((E_vac : ℝ) : ℂ) • 1) * P = (((e0 + d_sum + (E_sum - E_vac) : ℝ) : ℂ)) • P := by
  have h_decomp : H0 + P_diag - ((E_vac : ℝ) : ℂ) • (1 : E →L[ℂ] E) =
      H0 + (P_diag - ((E_sum : ℝ) : ℂ) • 1) + (((E_sum - E_vac : ℝ) : ℂ)) • 1 := by
    ext x; simp [sub_smul]; abel
  rw [h_decomp, add_mul, add_mul, h_H0, h_shift, smul_mul_assoc, one_mul]; ext x; simp [add_smul]

private lemma exp_eigenvalue_sector_eq {β lam_ω E_σ t : ℝ}
    (h_eq : lam_ω * t = E_σ * t) :
    Real.exp (-β * lam_ω) * t = Real.exp (-β * E_σ) * t := by
  have h_zero : (lam_ω - E_σ) * t = 0 := by linarith
  rcases mul_eq_zero.mp h_zero with hE | ht
  · rw [sub_eq_zero.mp hE]
  · rw [ht, mul_zero, mul_zero]

private lemma exp_eigenvalue_sector_le {β E_ω E_σ V_norm t : ℝ}
    (hβ : 0 ≤ β) (ht_nn : 0 ≤ t)
    (h_abs : |(E_ω - E_σ) * t| ≤ V_norm * t) :
    Real.exp (-β * E_ω) * t ≤ Real.exp (β * V_norm) * Real.exp (-β * E_σ) * t := by
  rcases eq_or_lt_of_le ht_nn with ht0 | ht_pos
  · rw [← ht0, mul_zero, mul_zero]
  · have h1 : (E_σ - E_ω) * t ≤ V_norm * t := by linarith [(abs_le.mp h_abs).1]
    have h_diff : E_σ - E_ω ≤ V_norm := le_of_mul_le_mul_right h1 ht_pos
    have h_exp : Real.exp (-β * E_ω) ≤ Real.exp (β * V_norm) * Real.exp (-β * E_σ) := by
      rw [← Real.exp_add]; exact Real.exp_le_exp.mpr (by nlinarith)
    exact mul_le_mul_of_nonneg_right h_exp ht_nn

private lemma inv_mul_le_exp_two_mul_of_bounds {Z_full Z_diag T_full T_diag β V_norm : ℝ}
    (hZ_full : 0 < Z_full) (hZ_diag : 0 < Z_diag) (_hT_diag : 0 ≤ T_diag)
    (h_num : T_full ≤ Real.exp (β * V_norm) * T_diag)
    (h_den : Real.exp (-β * V_norm) * Z_diag ≤ Z_full) :
    Z_full⁻¹ * T_full ≤ Real.exp (2 * β * V_norm) * (Z_diag⁻¹ * T_diag) := by
  have hZ_inv_le : Z_full⁻¹ ≤ Real.exp (β * V_norm) * Z_diag⁻¹ := by
    rw [inv_le_iff_one_le_mul₀ hZ_full]
    have h_exp_cancel : Real.exp (β * V_norm) * Real.exp (-β * V_norm) = 1 := by
      rw [← Real.exp_add, show β * V_norm + -β * V_norm = 0 by ring, Real.exp_zero]
    calc (1 : ℝ)
      _ = (Real.exp (β * V_norm) * Real.exp (-β * V_norm)) * (Z_diag * Z_diag⁻¹) := by
          rw [h_exp_cancel, one_mul, mul_inv_cancel₀ hZ_diag.ne']
      _ = Real.exp (β * V_norm) * Z_diag⁻¹ * (Real.exp (-β * V_norm) * Z_diag) := by ring
      _ ≤ Real.exp (β * V_norm) * Z_diag⁻¹ * Z_full :=
          mul_le_mul_of_nonneg_left h_den (by positivity)
  have h_exp2 : Real.exp (β * V_norm) * Real.exp (β * V_norm) = Real.exp (2 * β * V_norm) := by
    rw [← Real.exp_add]; ring_nf
  calc Z_full⁻¹ * T_full
    _ ≤ Z_full⁻¹ * (Real.exp (β * V_norm) * T_diag) :=
        mul_le_mul_of_nonneg_left h_num (inv_nonneg.mpr hZ_full.le)
    _ ≤ (Real.exp (β * V_norm) * Z_diag⁻¹) * (Real.exp (β * V_norm) * T_diag) :=
        mul_le_mul_of_nonneg_right hZ_inv_le (by positivity)
    _ = (Real.exp (β * V_norm) * Real.exp (β * V_norm)) * (Z_diag⁻¹ * T_diag) := by ring
    _ = Real.exp (2 * β * V_norm) * (Z_diag⁻¹ * T_diag) := by rw [h_exp2]

private lemma zero_mul_eq_zero_smul_local {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (P H : E →L[ℂ] E) (hP : P = 0) : P * H = ((0 : ℝ) : ℂ) • P := by
  rw [hP]; ext x; simp

/-- Adding a self-adjoint tail `V_tail` commuting with all syndrome projectors `sys.syndromeProjector σ`
    to any Hamiltonian `H_diag` that acts as a scalar `E_scalar σ` on every syndrome sector
    scales the witness Gibbs failure probability by at most `exp(2 * β * ‖V_tail‖)`. -/
lemma gibbsFailureProb_add_commuting_tail_le_of_sector_scalar
    {D L : ℕ} {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    [∀ x, Nonempty (Site x)] {ι : Type} [Fintype ι] [DecidableEq ι]
    (sys : IndexedCommutingProjectorHamiltonian D L Site ι)
    {β : ℝ} (hβ : 0 ≤ β)
    (H_diag V_tail : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site)
    (hH_diag : IsSelfAdjoint H_diag) (hV_tail : IsSelfAdjoint V_tail)
    (hH_full : IsSelfAdjoint (H_diag + V_tail))
    (h_tail_comm : ∀ σ : ι → Bool, Commute V_tail (sys.syndromeProjector σ))
    (E_scalar : (ι → Bool) → ℝ)
    (h_H_scalar : ∀ σ : ι → Bool,
      sys.syndromeProjector σ * H_diag = ((E_scalar σ : ℝ) : ℂ) • sys.syndromeProjector σ)
    (W : Finset ι) :
    gibbsFailureProb (H_diag + V_tail) hH_full β (positiveCheckWitnessProj sys W) ≤
      Real.exp (2 * β * ‖V_tail‖) *
        gibbsFailureProb H_diag hH_diag β (positiveCheckWitnessProj sys W) := by
  have h_res := _root_.syndrome_resolution_indexed sys
  have h_sec_le : ∀ σ : ι → Bool,
      hilbertTrace (gibbsBoltzmannOp (opEigenbasis (H_diag + V_tail) hH_full)
          (opEigenvalues (H_diag + V_tail) hH_full) β * sys.syndromeProjector σ) ≤
        Real.exp (β * ‖V_tail‖) *
          hilbertTrace (gibbsBoltzmannOp (opEigenbasis H_diag hH_diag)
            (opEigenvalues H_diag hH_diag) β * sys.syndromeProjector σ) := by
    intro σ
    let E_σ := E_scalar σ
    have h_P_Hdiag : sys.syndromeProjector σ * H_diag = ((E_σ : ℝ) : ℂ) • sys.syndromeProjector σ :=
      h_H_scalar σ
    have h_diag_tr :
        hilbertTrace (gibbsBoltzmannOp (opEigenbasis H_diag hH_diag)
            (opEigenvalues H_diag hH_diag) β * sys.syndromeProjector σ) =
          Real.exp (-β * E_σ) * hilbertTrace (sys.syndromeProjector σ) := by
      rw [hilbertTrace_gibbsBoltzmannOp_mul_eq,
        hilbertTrace_eq_sum_opEigenbasis H_diag hH_diag (sys.syndromeProjector σ),
        Finset.mul_sum]
      refine Finset.sum_congr rfl fun ω _ => ?_
      let ψ_ω := opEigenbasis H_diag hH_diag ω
      let lam_ω := opEigenvalues H_diag hH_diag ω
      let t := RCLike.re (inner ℂ ψ_ω (sys.syndromeProjector σ ψ_ω))
      have h1 : (sys.syndromeProjector σ * H_diag) ψ_ω = (lam_ω : ℂ) • sys.syndromeProjector σ ψ_ω := by
        rw [ContinuousLinearMap.mul_apply, opEigenbasis_apply_H H_diag hH_diag ω, map_smul]
      have h2 : (sys.syndromeProjector σ * H_diag) ψ_ω = ((E_σ : ℝ) : ℂ) • sys.syndromeProjector σ ψ_ω := by
        rw [h_P_Hdiag, ContinuousLinearMap.smul_apply]
      have h_in := congr_arg (fun v => RCLike.re (inner ℂ ψ_ω v)) (h1.symm.trans h2)
      have h_eq_re : lam_ω * t = E_σ * t := by simpa only [t, inner_smul_right, re_ofReal_mul] using h_in
      exact exp_eigenvalue_sector_eq h_eq_re
    rw [h_diag_tr, hilbertTrace_gibbsBoltzmannOp_mul_eq,
      hilbertTrace_eq_sum_opEigenbasis (H_diag + V_tail) hH_full (sys.syndromeProjector σ),
      ← mul_assoc, Finset.mul_sum]
    refine Finset.sum_le_sum fun ω _ => ?_
    let χ_ω := opEigenbasis (H_diag + V_tail) hH_full ω
    let E_ω := opEigenvalues (H_diag + V_tail) hH_full ω
    let φ := sys.syndromeProjector σ χ_ω
    let t := RCLike.re (inner ℂ χ_ω φ)
    have ht_eq : t = ‖φ‖ ^ 2 := isStarProjection_re_inner_eq_norm_sq (h_res.2.1 σ) χ_ω
    have ht_nn : 0 ≤ t := by rw [ht_eq]; exact sq_nonneg _
    have h_full_act : (sys.syndromeProjector σ * (H_diag + V_tail)) χ_ω = (E_ω : ℂ) • φ := by
      rw [ContinuousLinearMap.mul_apply, opEigenbasis_apply_H (H_diag + V_tail) hH_full ω, map_smul]
    have h_split_act : (sys.syndromeProjector σ * (H_diag + V_tail)) χ_ω =
        ((E_σ : ℝ) : ℂ) • φ + V_tail φ := by
      rw [mul_add, ContinuousLinearMap.add_apply, h_P_Hdiag, ContinuousLinearMap.smul_apply,
        ← (h_tail_comm σ).eq, ContinuousLinearMap.mul_apply]
    have h_V_φ : V_tail φ = ((E_ω - E_σ : ℝ) : ℂ) • φ := by
      rw [Complex.ofReal_sub, sub_smul]
      exact eq_sub_of_add_eq' (h_split_act.symm.trans h_full_act)
    have h_re_V : RCLike.re (inner ℂ φ (V_tail φ)) = (E_ω - E_σ) * t := by
      rw [h_V_φ, inner_smul_right, re_ofReal_mul, inner_self_eq_norm_sq, ← ht_eq]
    have h_abs_V : |(E_ω - E_σ) * t| ≤ ‖V_tail‖ * t := by
      rw [← h_re_V, ht_eq]
      exact abs_re_inner_le_opNorm_mul_norm_sq V_tail φ
    exact exp_eigenvalue_sector_le hβ ht_nn h_abs_V
  have h_num_le :
      hilbertTrace (gibbsBoltzmannOp (opEigenbasis (H_diag + V_tail) hH_full)
          (opEigenvalues (H_diag + V_tail) hH_full) β * positiveCheckWitnessProj sys W) ≤
        Real.exp (β * ‖V_tail‖) *
          hilbertTrace (gibbsBoltzmannOp (opEigenbasis H_diag hH_diag)
            (opEigenvalues H_diag hH_diag) β * positiveCheckWitnessProj sys W) := by
    unfold positiveCheckWitnessProj
    rw [Finset.mul_sum, hilbertTrace_sum, Finset.mul_sum, hilbertTrace_sum, Finset.mul_sum]
    exact Finset.sum_le_sum fun σ _ => h_sec_le σ
  have hP_W : IsStarProjection (positiveCheckWitnessProj sys W) :=
    (isStarProjection_positiveCheckWitnessProj sys W).1
  have h_den := (duhamelWeyl_relative_partition_ratio_bound β H_diag V_tail
    (positiveCheckWitnessProj sys W) hβ hH_diag hV_tail hH_full hP_W).1
  have hZ_diag_pos : 0 < gibbsPartitionZ (opEigenvalues H_diag hH_diag) β := gibbsPartitionZ_pos _ β
  have hZ_full_pos : 0 < gibbsPartitionZ (opEigenvalues (H_diag + V_tail) hH_full) β :=
    gibbsPartitionZ_pos _ β
  have h_tr_diag_nn :
      0 ≤ hilbertTrace (gibbsBoltzmannOp (opEigenbasis H_diag hH_diag)
        (opEigenvalues H_diag hH_diag) β * positiveCheckWitnessProj sys W) := by
    rw [hilbertTrace_gibbsBoltzmannOp_mul_eq]
    refine Finset.sum_nonneg fun ω _ => mul_nonneg (Real.exp_pos _).le ?_
    rw [isStarProjection_re_inner_eq_norm_sq hP_W]
    exact sq_nonneg _
  rw [perturbed_gibbsFailureProb_eq_inv_gibbsPartitionZ_mul_boltzmann_trace
    (H_diag + V_tail) hH_full β (positiveCheckWitnessProj sys W),
    perturbed_gibbsFailureProb_eq_inv_gibbsPartitionZ_mul_boltzmann_trace
    H_diag hH_diag β (positiveCheckWitnessProj sys W)]
  exact inv_mul_le_exp_two_mul_of_bounds hZ_full_pos hZ_diag_pos h_tr_diag_nn h_num_le h_den

/-- **Diagonal Coset Peeling Bound under Worldline Coupling Threshold
(`pauliDiagonal_witness_coset_peeling_of_worldlineCouplingThreshold`, Part II, Proposition 3.6 (`prop:walsh-coset-dominance`) and Proposition 3.8 (`prop:diagonal-peeling`, Equation `eq:main-C-diag`))**:
For any nonempty positive check witness `W` in a static 3D CSS system satisfying TQO-1 (`SatisfiesTQO1`) and
sector-filtered linear TQO-2 (`SatisfiesSectorFilteredLinearTQO2`), if `J ≤ worldlineCouplingThreshold Δ_0 Δ_RCA`, `16 ≤ β`, and
`rcaDiagonalCoercivityConstant 3 R_cut r_0 w_0 C_RCA ≤ Δ_RCA`, the diagonal Gibbs expectation of
`positiveCheckWitnessProj sys W` under `sys.H0 + pauliDiagonalPart sys V R_cut` is bounded by
`Real.exp (-((β / 2 + 7 / 2) * (W.card : ℝ)))`. -/
lemma pauliDiagonal_witness_coset_peeling_of_worldlineCouplingThreshold
    {L q_code r_0 m_max w_0 c_chk L_star R_cut : ℕ} [NeZero L]
    (D_field : Box3D L → LocalCSSDescriptor q_code r_0 m_max) (h_valid : ValidDescriptorField D_field)
    (sys : SysCSS[L, q_code, m_max])
    (h_sys_checks : ∀ idx, sys.checkProj idx = staticCSSCheckProj D_field idx ∧
      sys.support idx = staticCSSCheckSupport D_field idx ∧ sys.weight idx = 1)
    (h_geom : sys.IsGeometricallyLocal r_0 w_0)
    (C_RCA Δ_0 Δ_RCA β J : ℝ)
    (h_tqo1 : SatisfiesTQO1 sys L_star) (h_tqo2 : SatisfiesSectorFilteredLinearTQO2 sys 1 L_star C_RCA)
    (V : QuasiLocalPerturbation 3 L (SiteCSS[L, q_code])) (f : ℕ → ℝ)
    (hH_diag : IsSelfAdjoint (sys.H0 + pauliDiagonalPart sys V R_cut))
    (hR_cut : 1 ≤ R_cut) (hR_le : R_cut ≤ L_star) (hC_RCA : 0 ≤ C_RCA)
    (hf_super : InPerturbationClassSuper f) (h_ql : HasQuasiLocalDecayBound V J f)
    (h_collar_le : rcaCollarFiniteSum f c_chk r_0 R_cut C_RCA ≤ Δ_RCA)
    (h_rca_cal : rcaDiagonalCoercivityConstant 3 R_cut r_0 w_0 C_RCA ≤ Δ_RCA)
    (hΔ_0 : 0 < Δ_0) (hΔ_0_le : Δ_0 ≤ 1 / 5) (hΔ_RCA : 0 < Δ_RCA)
    (hJ_nn : 0 ≤ J) (hJ : J ≤ worldlineCouplingThreshold Δ_0 Δ_RCA)
    (hJ_walsh : J ≤ collarWalshCouplingThreshold R_cut r_0 w_0 C_RCA)
    (hβ : criticalInverseTempHier Δ_0 < β)
    (W : Finset (IdxCSS[L, q_code, m_max])) (hW_ne : W.Nonempty) :
    gibbsFailureProb (sys.H0 + pauliDiagonalPart sys V R_cut) hH_diag β
      (positiveCheckWitnessProj sys W) ≤
      Real.exp (-((β / 2 + 7 / 2) * (W.card : ℝ))) := by
  have _ := h_collar_le; have _ := h_rca_cal; have _ := hΔ_RCA; have _ := hJ; have _ := hW_ne
  have h_crit_ge : 24 ≤ criticalInverseTempHier Δ_0 := twenty_four_le_criticalInverseTempHier hΔ_0 (by linarith)
  have hβc_ge : 16 ≤ β - 1 := by linarith
  have hβ_gt : β > β - 1 := by linarith
  let V_trunc := scaleSplitTruncatedPerturbation V R_cut
  have hV_range : HasFiniteRangeBound V_trunc R_cut J :=
    scaleSplitTruncatedPerturbation_hasFiniteRangeBound V R_cut J f hJ_nn hf_super h_ql
  have h_diag_eq : pauliDiagonalPart sys V_trunc R_cut = pauliDiagonalPart sys V R_cut :=
    scaleSplitTruncatedPerturbation_pauliDiagonalPart sys V R_cut
  have hH_diag_shift_eq : sys.H0 + pauliDiagonalPart sys V_trunc R_cut - ((0 : ℝ) : ℂ) • 1 =
      sys.H0 + pauliDiagonalPart sys V R_cut := by ext x; simp [h_diag_eq]
  have h_res := _root_.syndrome_resolution_indexed sys
  have hH_diag_comm : ∀ σ : IdxCSS[L, q_code, m_max] → Bool,
      Commute (sys.H0 + pauliDiagonalPart sys V R_cut) (sys.syndromeProjector σ) := fun σ =>
    (Commute.sum_left _ _ _ fun c _ => (h_res.2.2.2.2.2.2.1 σ c).smul_left _).add_left
      (Commute.sum_left _ _ _ fun r _ => Commute.sum_left _ _ _ fun A _ =>
        (syndromePinchOp_isSelfAdjoint_and_commute_checkProj sys (V.is_selfAdjoint r A)).2.1 σ |>.2.2)
  have hH_diag_shift_sa : IsSelfAdjoint (sys.H0 + pauliDiagonalPart sys V_trunc R_cut - ((0 : ℝ) : ℂ) • 1) :=
    hH_diag_shift_eq.symm ▸ hH_diag
  have hH_diag_shift_comm : ∀ σ : IdxCSS[L, q_code, m_max] → Bool,
      Commute (sys.H0 + pauliDiagonalPart sys V_trunc R_cut - ((0 : ℝ) : ℂ) • 1) (sys.syndromeProjector σ) :=
    fun σ => hH_diag_shift_eq.symm ▸ hH_diag_comm σ
  have h_peel := gibbsFailureProb_pauliDiagonal_collar_peeling_le
    D_field h_valid sys h_sys_checks h_geom hR_cut hR_le hC_RCA hβc_ge hβ_gt
    hJ_nn hJ_walsh h_tqo1 h_tqo2 V_trunc hV_range hH_diag_shift_sa hH_diag_shift_comm W
  have h_lhs_eq : ∀ (h_sa : IsSelfAdjoint (sys.H0 + pauliDiagonalPart sys V_trunc R_cut - ((0 : ℝ) : ℂ) • 1)),
      gibbsFailureProb (sys.H0 + pauliDiagonalPart sys V_trunc R_cut - ((0 : ℝ) : ℂ) • 1)
        h_sa β (positiveCheckWitnessProj sys W) =
      gibbsFailureProb (sys.H0 + pauliDiagonalPart sys V R_cut) hH_diag β (positiveCheckWitnessProj sys W) := by
    rw [hH_diag_shift_eq]; intro _; rfl
  have h_min_eq : min (β - (β - 1)) 1 = 1 := by rw [show β - (β - 1) = 1 by ring, min_self]
  have h_rhs_eq : Real.exp (-(((β - 1) / 2 + min (β - (β - 1)) 1 + 3) * (W.card : ℝ))) =
      Real.exp (-((β / 2 + 7 / 2) * (W.card : ℝ))) := by rw [h_min_eq]; congr 1; ring
  rwa [h_lhs_eq hH_diag_shift_sa, h_rhs_eq] at h_peel

/-- **Pauli-Diagonal Witness Peeling Gibbs Bound (`pauli_diagonal_witness_peeling_gibbs_bound`, Part II, Proposition 3.8 (`prop:diagonal-peeling`), Equation `eq:main-C-diag`)**:
Establishes the RCA collar decomposition `pauliDiagonalPart sys V R_cut = W_out + W_in` with `‖W_in‖ ≤ 3 * J * Δ_RCA * W.card`,
absorption of `V_diag_tail` into the witness energy penalty, and the exact zero-tail `gibbsFailureProb` bound. -/
theorem pauli_diagonal_witness_peeling_gibbs_bound
    {L q_code r_0 m_max w_0 c_chk L_star R_cut Δ_adj d_min : ℕ} [NeZero L]
    (D_field : Box3D L → LocalCSSDescriptor q_code r_0 m_max) (h_valid : ValidDescriptorField D_field)
    (sys : SysCSS[L, q_code, m_max])
    (h_sys_checks : ∀ idx, sys.checkProj idx = staticCSSCheckProj D_field idx ∧
      sys.support idx = staticCSSCheckSupport D_field idx ∧ sys.weight idx = 1)
    (h_geom : sys.IsGeometricallyLocal r_0 w_0)
    (C_RCA c_wt Δ_0 Δ_RCA β J η : ℝ)
    (h_tqo1 : SatisfiesTQO1 sys L_star) (h_tqo2 : SatisfiesSectorFilteredLinearTQO2 sys 1 L_star C_RCA)
    (V : QuasiLocalPerturbation 3 L (SiteCSS[L, q_code])) (f : ℕ → ℝ) (V_diag_tail : ℬ_CSS[L, q_code])
    (hH_diag : IsSelfAdjoint (sys.H0 + pauliDiagonalPart sys V R_cut)) (hV_tail : IsSelfAdjoint V_diag_tail)
    (hH_full : IsSelfAdjoint ((sys.H0 + pauliDiagonalPart sys V R_cut) + V_diag_tail))
    (adj : IdxCSS[L, q_code, m_max] → IdxCSS[L, q_code, m_max] → Prop) [DecidableRel adj]
    (S_safe : Finset (IdxCSS[L, q_code, m_max] → Bool))
    (W_cover : Finset (Finset (IdxCSS[L, q_code, m_max]))) (v_0 : IdxCSS[L, q_code, m_max])
    (hR_cut : 1 ≤ R_cut) (hR_le : R_cut ≤ L_star) (hC_RCA : 0 ≤ C_RCA)
    (hf_super : InPerturbationClassSuper f) (h_ql : HasQuasiLocalDecayBound V J f)
    (h_collar_le : rcaCollarFiniteSum f c_chk r_0 R_cut C_RCA ≤ Δ_RCA)
    (h_rca_cal : rcaDiagonalCoercivityConstant 3 R_cut r_0 w_0 C_RCA ≤ Δ_RCA)
    (hc_wt : 0 < c_wt) (hΔ_0 : 0 < Δ_0) (hΔ_0_le : Δ_0 ≤ 1 / 5) (hΔ_RCA : 0 < Δ_RCA)
    (hd_min_pos : 1 ≤ d_min) (hJ_nn : 0 ≤ J) (hJ : J ≤ worldlineCouplingThreshold Δ_0 Δ_RCA)
    (hJ_walsh : J ≤ collarWalshCouplingThreshold R_cut r_0 w_0 C_RCA)
    (hβ : criticalInverseTempHier Δ_0 < β) (hd_min : c_wt * (((L ^ 3 : ℕ) : ℝ) ^ η) ≤ (d_min : ℝ))
    (h_tail_comm : ∀ σ : IdxCSS[L, q_code, m_max] → Bool, Commute V_diag_tail (sys.syndromeProjector σ))
    (h_tail_norm : ‖V_diag_tail‖ ≤ (1 / 16 : ℝ) * Δ_0)
    (h_conn_cover : IsConnectedCheckWitnessCover adj S_safe W_cover v_0 Δ_adj d_min) :
    (∀ W ∈ W_cover, ∃ W_out W_in : ℬ_CSS[L, q_code],
      IsSelfAdjoint W_out ∧ IsSelfAdjoint W_in ∧
      pauliDiagonalPart sys V R_cut = W_out + W_in ∧
      (∀ σ, Commute W_out (sys.syndromeProjector σ) ∧ Commute W_in (sys.syndromeProjector σ)) ∧
      ‖W_in‖ ≤ 3 * J * Δ_RCA * (W.card : ℝ)) ∧
    (13 / 8 : ℝ) * Δ_0 ≤ 2 * Δ_0 - 6 * J * Δ_RCA ∧
    c_wt * (3 / 2 : ℝ) * Δ_0 * (β - criticalInverseTempHier Δ_0) ≤
      worldlineSuppressionRate c_wt Δ_0 Δ_RCA β J ∧
    gibbsFailureProb (sys.H0 + pauliDiagonalPart sys V R_cut) hH_diag β
      (1 - indexedBareFailureProjector sys S_safe) ≤
      2 * Real.exp (-worldlineSuppressionRate c_wt Δ_0 Δ_RCA β J * (((L ^ 3 : ℕ) : ℝ) ^ η)) ∧
    gibbsFailureProb (sys.H0 + pauliDiagonalPart sys V R_cut) hH_diag β
      (1 - indexedBareFailureProjector sys S_safe) ≤
      2 * Real.exp (-(c_wt * (3 / 2 : ℝ) * Δ_0 * (β - criticalInverseTempHier Δ_0)) *
        (((L ^ 3 : ℕ) : ℝ) ^ η)) ∧
    gibbsFailureProb ((sys.H0 + pauliDiagonalPart sys V R_cut) + V_diag_tail) hH_full β
      (1 - indexedBareFailureProjector sys S_safe) ≤
      2 * Real.exp (-(c_wt * (3 / 2 : ℝ) * Δ_0 * (β - criticalInverseTempHier Δ_0)) *
        (((L ^ 3 : ℕ) : ℝ) ^ η)) := by
  have h_part1 : ∀ W ∈ W_cover, ∃ W_out W_in : ℬ_CSS[L, q_code],
      IsSelfAdjoint W_out ∧ IsSelfAdjoint W_in ∧
      pauliDiagonalPart sys V R_cut = W_out + W_in ∧
      (∀ σ, Commute W_out (sys.syndromeProjector σ) ∧ Commute W_in (sys.syndromeProjector σ)) ∧
      ‖W_in‖ ≤ 3 * J * Δ_RCA * (W.card : ℝ) :=
    fun W _ => exists_pauliDiagonal_witness_collar_split D_field sys h_sys_checks V f
      C_RCA Δ_RCA J hC_RCA hJ_nn hΔ_RCA hf_super h_ql h_rca_cal W
  have h_gap := walshHadamard_coset_effective_energy_gap_ge c_wt Δ_0 Δ_RCA β J hc_wt hΔ_0 hΔ_RCA hJ hβ
  have h_crit_ge : 24 ≤ criticalInverseTempHier Δ_0 := twenty_four_le_criticalInverseTempHier hΔ_0 (by linarith)
  have hβ_pos : 0 < β := by linarith
  let V_trunc := scaleSplitTruncatedPerturbation V R_cut
  have hV_range : HasFiniteRangeBound V_trunc R_cut J :=
    scaleSplitTruncatedPerturbation_hasFiniteRangeBound V R_cut J f hJ_nn hf_super h_ql
  have h_diag_eq : pauliDiagonalPart sys V_trunc R_cut = pauliDiagonalPart sys V R_cut :=
    scaleSplitTruncatedPerturbation_pauliDiagonalPart sys V R_cut
  have hH_diag_shift_eq : sys.H0 + pauliDiagonalPart sys V_trunc R_cut - ((0 : ℝ) : ℂ) • 1 =
      sys.H0 + pauliDiagonalPart sys V R_cut := by ext x; simp [h_diag_eq]
  have h_res := _root_.syndrome_resolution_indexed sys
  have hH_diag_comm : ∀ σ : IdxCSS[L, q_code, m_max] → Bool,
      Commute (sys.H0 + pauliDiagonalPart sys V R_cut) (sys.syndromeProjector σ) := fun σ =>
    (Commute.sum_left _ _ _ fun c _ => (h_res.2.2.2.2.2.2.1 σ c).smul_left _).add_left
      (Commute.sum_left _ _ _ fun r _ => Commute.sum_left _ _ _ fun A _ =>
        (syndromePinchOp_isSelfAdjoint_and_commute_checkProj sys (V.is_selfAdjoint r A)).2.1 σ |>.2.2)
  have hH_diag_shift_comm : ∀ σ : IdxCSS[L, q_code, m_max] → Bool,
      Commute (sys.H0 + pauliDiagonalPart sys V_trunc R_cut - ((0 : ℝ) : ℂ) • 1) (sys.syndromeProjector σ) :=
    fun σ => hH_diag_shift_eq.symm ▸ hH_diag_comm σ
  rcases exists_pauliDiagonal_local_collar_decomposition
      D_field sys h_sys_checks hR_le h_tqo2 V_trunc hV_range with ⟨e_loc, he_decomp⟩
  rcases exists_local_collar_scalar_family_of_tqo2
      D_field h_valid sys h_sys_checks h_geom hR_cut hR_le hC_RCA hJ_nn
      h_tqo1 h_tqo2 V_trunc hV_range e_loc he_decomp with ⟨d_loc, h_scalar⟩
  let E_sum := ∑ r ∈ Finset.Icc 1 (min R_cut L), ∑ A ∈ boxCubes 3 L r, e_loc r A
  let E_scalar : (IdxCSS[L, q_code, m_max] → Bool) → ℝ := fun σ =>
    if σ ∈ realizableSyndromes D_field then
      pauliDiagonalSectorEnergy sys R_cut d_loc σ + (E_sum - 0)
    else 0
  have h_H_scalar : ∀ σ, sys.syndromeProjector σ * (sys.H0 + pauliDiagonalPart sys V R_cut) =
      ((E_scalar σ : ℝ) : ℂ) • sys.syndromeProjector σ := by
    intro σ
    dsimp only [E_scalar]
    split_ifs with hσ
    · have h_shift_act :
          (pauliDiagonalPart sys V_trunc R_cut - ((E_sum : ℝ) : ℂ) • 1) * sys.syndromeProjector σ =
            ((∑ r ∈ Finset.Icc 1 (min R_cut L), ∑ A ∈ boxCubes 3 L r, d_loc r A σ : ℝ) : ℂ) •
              sys.syndromeProjector σ := by
        rw [he_decomp.1, Finset.sum_mul, Complex.ofReal_sum, clm_sum_smul]
        refine Finset.sum_congr rfl fun r hr => ?_
        rw [Finset.sum_mul, Complex.ofReal_sum, clm_sum_smul]
        exact Finset.sum_congr rfl fun A hA => (h_scalar r hr A hA).1.1 σ hσ
      rw [← hH_diag_shift_eq]
      exact (hH_diag_shift_comm σ).symm.eq.trans
        (hdiag_mul_projector_eq_smul_local (h_res.2.2.2.2.1 σ) h_shift_act)
    · have h_zero : sys.syndromeProjector σ = 0 := by
        by_contra h_ne
        obtain ⟨⟨a, b, hab⟩, _⟩ :=
          hilbertTrace_syndromeProjector_eq_P0_of_ne_zero D_field h_valid sys h_sys_checks σ h_ne
        exact hσ (Finset.mem_filter.mpr ⟨Finset.mem_univ σ, a, b, hab⟩)
      exact zero_mul_eq_zero_smul_local _ _ h_zero
  have h_conn := connected_check_witness_cover_card_and_klarner_bound
    adj S_safe W_cover v_0 Δ_adj d_min h_conn_cover
  let κ := worldlineSuppressionRate c_wt Δ_0 Δ_RCA β J / c_wt + Real.log klarnerAnimalConst
  have h_κ_eq : κ = β * (2 * Δ_0 - 6 * J * Δ_RCA) - 1 := by
    dsimp [κ]; unfold worldlineSuppressionRate
    rw [mul_div_cancel_left₀ _ hc_wt.ne']
    ring
  have h_wit_bounds : ∀ W ∈ W_cover,
      gibbsFailureProb (sys.H0 + pauliDiagonalPart sys V R_cut) hH_diag β
        (positiveCheckWitnessProj sys W) ≤ Real.exp (-κ * (W.card : ℝ)) ∧
      gibbsFailureProb ((sys.H0 + pauliDiagonalPart sys V R_cut) + V_diag_tail) hH_full β
        (positiveCheckWitnessProj sys W) ≤ Real.exp (-κ * (W.card : ℝ)) := by
    intro W hW
    have hW_card_ge1 : 1 ≤ W.card := le_trans hd_min_pos (h_conn.1 W hW)
    have hW_ne : W.Nonempty := Finset.card_pos.mp (by omega)
    have h_peel_diag :
        gibbsFailureProb (sys.H0 + pauliDiagonalPart sys V R_cut) hH_diag β
          (positiveCheckWitnessProj sys W) ≤
          Real.exp (-((β / 2 + 7 / 2) * (W.card : ℝ))) :=
      pauliDiagonal_witness_coset_peeling_of_worldlineCouplingThreshold
        D_field h_valid sys h_sys_checks h_geom C_RCA Δ_0 Δ_RCA β J
        h_tqo1 h_tqo2 V f hH_diag hR_cut hR_le hC_RCA hf_super h_ql
        h_collar_le h_rca_cal hΔ_0 hΔ_0_le hΔ_RCA hJ_nn hJ hJ_walsh hβ W hW_ne
    have h_card_real : (1 : ℝ) ≤ (W.card : ℝ) := by exact_mod_cast hW_card_ge1
    have h_tail_le : 2 * β * ‖V_diag_tail‖ ≤ (1 / 40 : ℝ) * β * (W.card : ℝ) := by
      have h1 : 2 * β * ‖V_diag_tail‖ ≤ (1 / 40 : ℝ) * β := by nlinarith
      nlinarith
    have h_exp_arg_tail :
        2 * β * ‖V_diag_tail‖ + -((β / 2 + 7 / 2) * (W.card : ℝ)) ≤
          -κ * (W.card : ℝ) := by
      rw [h_κ_eq]
      have h_gap_upper : 2 * Δ_0 - 6 * J * Δ_RCA ≤ 2 / 5 := by nlinarith
      have h_β_gap : β * (2 * Δ_0 - 6 * J * Δ_RCA) ≤ (2 / 5 : ℝ) * β := by nlinarith
      nlinarith
    have h_exp_arg_diag :
        -((β / 2 + 7 / 2) * (W.card : ℝ)) ≤ -κ * (W.card : ℝ) := by
      have : 0 ≤ 2 * β * ‖V_diag_tail‖ := by positivity
      linarith
    have h_diag_bound :
        gibbsFailureProb (sys.H0 + pauliDiagonalPart sys V R_cut) hH_diag β
          (positiveCheckWitnessProj sys W) ≤ Real.exp (-κ * (W.card : ℝ)) :=
      le_trans h_peel_diag (Real.exp_le_exp.mpr h_exp_arg_diag)
    have h_full_step :=
      gibbsFailureProb_add_commuting_tail_le_of_sector_scalar
        sys hβ_pos.le (sys.H0 + pauliDiagonalPart sys V R_cut) V_diag_tail
        hH_diag hV_tail hH_full h_tail_comm E_scalar h_H_scalar W
    have h_full_bound :
        gibbsFailureProb ((sys.H0 + pauliDiagonalPart sys V R_cut) + V_diag_tail) hH_full β
          (positiveCheckWitnessProj sys W) ≤ Real.exp (-κ * (W.card : ℝ)) := by
      calc gibbsFailureProb ((sys.H0 + pauliDiagonalPart sys V R_cut) + V_diag_tail) hH_full β
            (positiveCheckWitnessProj sys W)
        _ ≤ Real.exp (2 * β * ‖V_diag_tail‖) *
              gibbsFailureProb (sys.H0 + pauliDiagonalPart sys V R_cut) hH_diag β
                (positiveCheckWitnessProj sys W) := h_full_step
        _ ≤ Real.exp (2 * β * ‖V_diag_tail‖) *
              Real.exp (-((β / 2 + 7 / 2) * (W.card : ℝ))) :=
            mul_le_mul_of_nonneg_left h_peel_diag (Real.exp_pos _).le
        _ = Real.exp (2 * β * ‖V_diag_tail‖ +
              -((β / 2 + 7 / 2) * (W.card : ℝ))) :=
            (Real.exp_add _ _).symm
        _ ≤ Real.exp (-κ * (W.card : ℝ)) :=
            Real.exp_le_exp.mpr h_exp_arg_tail
    exact ⟨h_diag_bound, h_full_bound⟩
  have h_shell := (klarner_animal_shell_sum_bound W_cover d_min κ
    h_conn.1 h_conn.2 h_gap.2.2).2
  have h_sum_diag := positiveWitness_gibbs_defect_sum_le sys
    (sys.H0 + pauliDiagonalPart sys V R_cut) hH_diag β S_safe W_cover
    (fun W => Real.exp (-κ * (W.card : ℝ)))
    h_conn_cover.1 (fun W hW => (h_wit_bounds W hW).1)
  have h_sum_full := positiveWitness_gibbs_defect_sum_le sys
    ((sys.H0 + pauliDiagonalPart sys V R_cut) + V_diag_tail) hH_full β S_safe W_cover
    (fun W => Real.exp (-κ * (W.card : ℝ)))
    h_conn_cover.1 (fun W hW => (h_wit_bounds W hW).2)
  have h_rate_pos : 0 < worldlineSuppressionRate c_wt Δ_0 Δ_RCA β J := by
    have h_sub_pos : 0 < β - criticalInverseTempHier Δ_0 := sub_pos.mpr hβ
    have h_lhs_pos : 0 < c_wt * (3 / 2 : ℝ) * Δ_0 * (β - criticalInverseTempHier Δ_0) := by
      positivity
    exact lt_of_lt_of_le h_lhs_pos h_gap.2.1
  have h_div_nonneg : 0 ≤ worldlineSuppressionRate c_wt Δ_0 Δ_RCA β J / c_wt :=
    div_nonneg h_rate_pos.le hc_wt.le
  have h_dmin_le :
      2 * Real.exp (-(κ - Real.log klarnerAnimalConst) * (d_min : ℝ)) ≤
        2 * Real.exp (-worldlineSuppressionRate c_wt Δ_0 Δ_RCA β J * (((L ^ 3 : ℕ) : ℝ) ^ η)) := by
    have h_κ_sub : κ - Real.log klarnerAnimalConst =
        worldlineSuppressionRate c_wt Δ_0 Δ_RCA β J / c_wt := by
      dsimp [κ]; ring
    rw [h_κ_sub]
    have h_mul :
        worldlineSuppressionRate c_wt Δ_0 Δ_RCA β J * (((L ^ 3 : ℕ) : ℝ) ^ η) ≤
          (worldlineSuppressionRate c_wt Δ_0 Δ_RCA β J / c_wt) * (d_min : ℝ) := by
      have h1 := mul_le_mul_of_nonneg_left hd_min h_div_nonneg
      have h_eq :
          (worldlineSuppressionRate c_wt Δ_0 Δ_RCA β J / c_wt) *
            (c_wt * (((L ^ 3 : ℕ) : ℝ) ^ η)) =
            worldlineSuppressionRate c_wt Δ_0 Δ_RCA β J * (((L ^ 3 : ℕ) : ℝ) ^ η) := by
        field_simp [hc_wt.ne']
      linarith
    exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by linarith)) (by norm_num)
  have h_exp_le :
      2 * Real.exp (-worldlineSuppressionRate c_wt Δ_0 Δ_RCA β J * (((L ^ 3 : ℕ) : ℝ) ^ η)) ≤
        2 * Real.exp (-(c_wt * (3 / 2 : ℝ) * Δ_0 * (β - criticalInverseTempHier Δ_0)) *
          (((L ^ 3 : ℕ) : ℝ) ^ η)) := by
    have h_vol_nn : (0 : ℝ) ≤ (((L ^ 3 : ℕ) : ℝ) ^ η) := by positivity
    have h_neg := mul_le_mul_of_nonneg_right (neg_le_neg h_gap.2.1) h_vol_nn
    exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr h_neg) (by norm_num)
  have h_diag_wl := le_trans h_sum_diag (le_trans h_shell h_dmin_le)
  have h_diag_hier := le_trans h_diag_wl h_exp_le
  have h_full_hier := le_trans h_sum_full (le_trans h_shell (le_trans h_dmin_le h_exp_le))
  exact ⟨h_part1, h_gap.1, h_gap.2.1, h_diag_wl, h_diag_hier, h_full_hier⟩

end DirectWorldlineCluster

end
