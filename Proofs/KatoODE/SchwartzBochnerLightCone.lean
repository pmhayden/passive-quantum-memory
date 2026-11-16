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

import Proofs.KatoODE.SchwartzCollarLightCone

open scoped Classical InnerProduct ComplexConjugate BigOperators Nat
open Filter Topology Asymptotics ContinuousLinearMap MeasureTheory
open KMSPinchedGibbs PerturbedThermalBarrier WeldedHierarchy WeldedHierarchy.BDLDecoder
open InhomogeneousMemoryChallenge

noncomputable section

set_option maxRecDepth 200000
set_option maxHeartbeats 800000

/-!
# Scale-Splitting Centered-Ball Light-Cone Bounds for Schwartz Bochner Filters

Establishes system-size-independent centered-ball conditional expectation tail profiles (`bdlSchwartzSumTailProfile`, `bdlSchwartzPerturbationBoxBallTailProfile`, `bdlSchwartzCheckBoxBallTailProfile`) for `bochnerFilteredOp` and `katoHastingsGeneratorOp` with Schwartz kernels `bandpassFilterWeight` and `bandpassContinuationWeight`.

## References

* Part I, Section 6.2 (`subsec:bochner-lr`), Proposition 6.3 (`prop:bochner-time-convolution`), Equations (71)–(72) (`eq:bochner-bare-V-tail`, `eq:bochner-bare-Q-tail`)
-/

attribute [local irreducible] collarConstRCABDL bdlLambda qCodeBDL r0BDL mMaxBDL LatticeHamiltonian.s1

/-- For $x \in \mathrm{boxBall}(u, r_1)$ and $y \notin \mathrm{boxBall}(u, r_2)$,
    $r_2 + 1 - r_1 \le \mathrm{boxDist}(x, y)$. -/
lemma boxDist_ge_of_mem_boxBall_of_not_mem_boxBall {D L : ℕ}
    (u : BoxD D L) {r_1 r_2 : ℕ} {x y : BoxD D L}
    (hx : x ∈ boxBall u r_1) (hy : y ∉ boxBall u r_2) :
    r_2 + 1 - r_1 ≤ boxDist x y := by
  simp only [boxBall, Finset.mem_filter, Finset.mem_univ, true_and, not_le] at hx hy
  have h_tri := boxDist_triangle u x y; omega

/-- Universal ($L$-independent) `boxBall u (j / 2)` tail profile for `bochnerFilteredOp H_s w`
    applied to a scale-decomposed sum $\sum_{q=1}^L T_q$ with support offset `r_offset` and decay `f_T`. -/
def bdlSchwartzSumTailProfile (w : ℝ → ℂ) (f : ℕ → ℝ) (r_offset : ℕ) (f_T : ℕ → ℝ) (j : ℕ) : ℝ :=
  if j < 4 * r_offset then 2 * (1 + ∫ t : ℝ, ‖w t‖) * ∑' q : ℕ, f_T q
  else (1 + ∫ t : ℝ, ‖w t‖) * bdlInhomogeneousBarePerturbationTailProfile (j / 4) f_T
    (((2 * (r_offset + j / 4) + 1 : ℕ) : ℝ) ^ 3 * ((2 * (j / 2) + 1 : ℕ) : ℝ) ^ 3 *
      bdlSchwartzCollarEnvelope w f (fun r => r / 2 + 1 - (r_offset + r / 4)) j)

theorem isSuperpolynomialDecay_bdlSchwartzSumTailProfile {w : ℝ → ℂ} {f f_T : ℕ → ℝ}
    (hf : IsSuperpolynomialDecay f) (hf_T : IsSuperpolynomialDecay f_T)
    (hw_tail : ∀ {c : ℝ}, 0 < c →
      IsSuperpolynomialDecay (fun R : ℕ => ∫ t in {t : ℝ | c * (R : ℝ) ≤ |t|}, ‖w t‖))
    (r_offset : ℕ) :
    IsSuperpolynomialDecay (bdlSchwartzSumTailProfile w f r_offset f_T) := by
  let d_off : ℕ → ℕ := fun r => r / 2 + 1 - (r_offset + r / 4)
  have h_env : IsSuperpolynomialDecay (bdlSchwartzCollarEnvelope w f d_off) :=
    isSuperpolynomialDecay_bdlSchwartzCollarEnvelope hf hw_tail ⟨8, by decide, by
      filter_upwards [Filter.eventually_ge_atTop (8 * r_offset)] with r hr; dsimp [d_off]; omega⟩
  have h_pow6 : IsSuperpolynomialDecay
      (fun j : ℕ => (j : ℝ) ^ 6 * bdlSchwartzCollarEnvelope w f d_off j) :=
    isSuperpolynomialDecay_mul_pow h_env 6
  have h_low : IsSuperpolynomialDecay
      (fun j : ℕ => (((2 * (r_offset + j / 4) + 1 : ℕ) : ℝ) ^ 3 * ((2 * (j / 2) + 1 : ℕ) : ℝ) ^ 3 *
        bdlSchwartzCollarEnvelope w f d_off j) * ∑' q : ℕ, f_T q) := by
    have h_tsum_nn : 0 ≤ ∑' q : ℕ, f_T q := tsum_nonneg hf_T.1
    have h_dom : IsSuperpolynomialDecay (fun j : ℕ => (216 * ∑' q : ℕ, f_T q) *
        ((j : ℝ) ^ 6 * bdlSchwartzCollarEnvelope w f d_off j)) :=
      isSuperpolynomialDecay_const_mul h_pow6 (by positivity)
    refine ⟨fun j => mul_nonneg (mul_nonneg (by positivity)
      (bdlSchwartzCollarEnvelope_nonneg w hf d_off j)) h_tsum_nn, fun n => ?_⟩
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds (h_dom.2 n)
      (Eventually.of_forall fun j => by have := bdlSchwartzCollarEnvelope_nonneg w hf d_off j; positivity) ?_
    filter_upwards [Filter.eventually_ge_atTop (4 * r_offset + 1)] with j hj
    have h_card1 : ((2 * (r_offset + j / 4) + 1 : ℕ) : ℝ) ^ 3 ≤ 27 * (j : ℝ) ^ 3 := by
      have h1 : ((2 * (r_offset + j / 4) + 1 : ℕ) : ℝ) ≤ 3 * (j : ℝ) := by
        exact_mod_cast (show 2 * (r_offset + j / 4) + 1 ≤ 3 * j by omega)
      calc ((2 * (r_offset + j / 4) + 1 : ℕ) : ℝ) ^ 3
        _ ≤ (3 * (j : ℝ)) ^ 3 := pow_le_pow_left₀ (by positivity) h1 3
        _ = 27 * (j : ℝ) ^ 3 := by ring
    have h_card2 : ((2 * (j / 2) + 1 : ℕ) : ℝ) ^ 3 ≤ 8 * (j : ℝ) ^ 3 := by
      have h2 : ((2 * (j / 2) + 1 : ℕ) : ℝ) ≤ 2 * (j : ℝ) := by
        exact_mod_cast (show 2 * (j / 2) + 1 ≤ 2 * j by omega)
      calc ((2 * (j / 2) + 1 : ℕ) : ℝ) ^ 3
        _ ≤ (2 * (j : ℝ)) ^ 3 := pow_le_pow_left₀ (by positivity) h2 3
        _ = 8 * (j : ℝ) ^ 3 := by ring
    have h_prod : ((2 * (r_offset + j / 4) + 1 : ℕ) : ℝ) ^ 3 *
        ((2 * (j / 2) + 1 : ℕ) : ℝ) ^ 3 ≤ 216 * (j : ℝ) ^ 6 := by
      have hm := mul_le_mul h_card1 h_card2 (by positivity) (by positivity)
      linarith [show (27 * (j : ℝ) ^ 3) * (8 * (j : ℝ) ^ 3) = 216 * (j : ℝ) ^ 6 by ring]
    have h_env_nn := bdlSchwartzCollarEnvelope_nonneg w hf d_off j
    calc (j : ℝ) ^ n * ((((2 * (r_offset + j / 4) + 1 : ℕ) : ℝ) ^ 3 *
            ((2 * (j / 2) + 1 : ℕ) : ℝ) ^ 3 *
            bdlSchwartzCollarEnvelope w f d_off j) * ∑' q : ℕ, f_T q)
      _ ≤ (j : ℝ) ^ n * (((216 * (j : ℝ) ^ 6) *
            bdlSchwartzCollarEnvelope w f d_off j) * ∑' q : ℕ, f_T q) := by
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right h_prod h_env_nn) h_tsum_nn
      _ = (j : ℝ) ^ n * ((216 * ∑' q : ℕ, f_T q) *
            ((j : ℝ) ^ 6 * bdlSchwartzCollarEnvelope w f d_off j)) := by ring
  have h_high : IsSuperpolynomialDecay
      (fun j : ℕ => 2 * ∑' q : ℕ, if j / 4 < q then f_T q else 0) :=
    isSuperpolynomialDecay_two_mul_tsum_tail hf_T
      ⟨4, by decide, Eventually.of_forall fun j => by omega⟩
  have hw_nn : 0 ≤ 1 + ∫ t : ℝ, ‖w t‖ :=
    add_nonneg zero_le_one (integral_nonneg fun _ => norm_nonneg _)
  have h_comb := isSuperpolynomialDecay_const_mul (isSuperpolynomialDecay_add h_low h_high) hw_nn
  have hC0 : 0 ≤ 2 * (1 + ∫ t : ℝ, ‖w t‖) * ∑' q : ℕ, f_T q :=
    mul_nonneg (mul_nonneg zero_le_two hw_nn) (tsum_nonneg hf_T.1)
  exact isSuperpolynomialDecay_ite_lt h_comb (4 * r_offset) hC0

/-- **Unified Scale-Splitting `boxBall u (j / 2)` Conditional Expectation Bound
    (`norm_bochnerFilteredOp_sum_boxBall_sub_condExp_le`)**. -/
theorem norm_bochnerFilteredOp_sum_boxBall_sub_condExp_le
    {L : ℕ} [NeZero L]
    {c_star C β_c c_F η_mem c_mem J s : ℝ} {w : ℝ → ℂ} {f f_T : ℕ → ℝ}
    (mem : Inhomogeneous3DMemoryRealization L qCodeBDL r0BDL mMaxBDL c_star C β_c c_F η_mem c_mem)
    (V : QuasiLocalPerturbation 3 L (UniformSite3D L (CodeSlotConfig qCodeBDL)))
    (hw : Integrable w)
    (hJ0 : 0 ≤ J) (hJ1 : J ≤ 1) (hs : s ∈ Set.Icc (-1 : ℝ) 1)
    (hf : IsSuperpolynomialDecay f) (hf_T : IsSuperpolynomialDecay f_T)
    (hV : V.SatisfiesDecayBound J f)
    (r_offset : ℕ) (u : Box3D L) (j : ℕ) (hj_cut : j / 4 ≤ L)
    (T_q : ℕ → (ManyBodyHilbertSpace (UniformSite3D L (CodeSlotConfig qCodeBDL)) →L[ℂ]
      ManyBodyHilbertSpace (UniformSite3D L (CodeSlotConfig qCodeBDL))))
    (h_norm_q : ∀ q ∈ Finset.Icc 1 L, ‖T_q q‖ ≤ J * f_T q)
    (h_supp_q : ∀ q ∈ Finset.Icc 1 (j / 4),
      IsSupportedOn (UniformSite3D L (CodeSlotConfig qCodeBDL))
        (boxBall u (r_offset + j / 4)) (T_q q)) :
    let Site := UniformSite3D L (CodeSlotConfig qCodeBDL)
    let H_s := mem.sys.H0 + (scaleQuasiLocalPerturbation s V).totalPerturbation
    let B_T := bochnerFilteredOp H_s w (∑ q ∈ Finset.Icc 1 L, T_q q)
    ‖B_T - condExp Site (boxBall u (j / 2)) B_T‖ ≤
      J * bdlSchwartzSumTailProfile w f r_offset f_T j := by
  intro Site H_s B_T
  haveI : NeZero 3 := ⟨by decide⟩
  have hHs_sa : IsSelfAdjoint H_s :=
    isSelfAdjoint_add_clm mem.sys.isSelfAdjoint_H0
      (scaleQuasiLocalPerturbation s V).isSelfAdjoint_totalPerturbation
  have hw_nn : 0 ≤ ∫ t : ℝ, ‖w t‖ := integral_nonneg fun _ => norm_nonneg _
  have hw1_nn : 0 ≤ 1 + ∫ t : ℝ, ‖w t‖ := by linarith
  unfold bdlSchwartzSumTailProfile
  split_ifs with hj_lt
  · have h_ce : ‖B_T - condExp Site (boxBall u (j / 2)) B_T‖ ≤ 2 * ‖B_T‖ :=
      norm_sub_condExp_le_two_mul_norm (boxBall u (j / 2)) B_T
    have h_boch : ‖B_T‖ ≤ (1 + ∫ t : ℝ, ‖w t‖) * ‖∑ q ∈ Finset.Icc 1 L, T_q q‖ :=
      le_trans (norm_bochnerFilteredOp_le hHs_sa w _)
        (mul_le_mul_of_nonneg_right (by linarith) (norm_nonneg _))
    have h_sum_le : ‖∑ q ∈ Finset.Icc 1 L, T_q q‖ ≤ J * ∑' q : ℕ, f_T q := by
      have h1 : ‖∑ q ∈ Finset.Icc 1 L, T_q q‖ ≤ J * ∑ q ∈ Finset.Icc 1 L, f_T q := by
        calc ‖∑ q ∈ Finset.Icc 1 L, T_q q‖
          _ ≤ ∑ q ∈ Finset.Icc 1 L, ‖T_q q‖ := norm_sum_le _ _
          _ ≤ ∑ q ∈ Finset.Icc 1 L, (J * f_T q) := Finset.sum_le_sum h_norm_q
          _ = J * ∑ q ∈ Finset.Icc 1 L, f_T q := by rw [← Finset.mul_sum]
      have h2 : ∑ q ∈ Finset.Icc 1 L, f_T q ≤ ∑' q : ℕ, f_T q :=
        (summable_of_isSuperpolynomialDecay hf_T).sum_le_tsum (Finset.Icc 1 L) (fun q _ => hf_T.1 q)
      exact le_trans h1 (mul_le_mul_of_nonneg_left h2 hJ0)
    have h_mult := mul_le_mul_of_nonneg_left h_sum_le hw1_nn
    linarith
  · have hj_ge : 4 * r_offset ≤ j := not_lt.mp hj_lt
    let r_cut := j / 4
    let r_bare := j / 2
    let r_X := r_offset + r_cut
    let d_off : ℕ → ℕ := fun r => r / 2 + 1 - (r_offset + r / 4)
    let ε_LR : ℝ := ((2 * r_X + 1 : ℕ) : ℝ) ^ 3 * ((2 * r_bare + 1 : ℕ) : ℝ) ^ 3 *
      bdlSchwartzCollarEnvelope w f d_off j
    have hε_nn : 0 ≤ ε_LR :=
      mul_nonneg (by positivity) (bdlSchwartzCollarEnvelope_nonneg w hf d_off j)
    let Ψ : (ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site) →L[ℂ]
        (ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site) :=
      ContinuousLinearMap.id ℂ _ - condExpCLM Site (boxBall u r_bare)
    have hΨ_sum : Ψ B_T = ∑ q ∈ Finset.Icc 1 L, Ψ (bochnerFilteredOp H_s w (T_q q)) := by
      change Ψ (bochnerFilteredOp H_s w (∑ q ∈ Finset.Icc 1 L, T_q q)) = _
      rw [bochnerFilteredOp_finset_sum (Finset.Icc 1 L) H_s w T_q
        (fun q _ => integrable_smul_heisenbergFlow_of_integrable hHs_sa hw (T_q q)), map_sum]
    have h_low_lr : ∀ q ∈ Finset.Icc 1 r_cut,
        ‖Ψ (bochnerFilteredOp H_s w (T_q q))‖ ≤
          (1 + ∫ t : ℝ, ‖w t‖) * (ε_LR * (J * f_T q)) := by
      intro q hq
      rcases Finset.mem_Icc.mp hq with ⟨hq1, hq_cut⟩
      have hq_L : q ∈ Finset.Icc 1 L := Finset.mem_Icc.mpr ⟨hq1, le_trans hq_cut hj_cut⟩
      have hX_ne : (boxBall u r_X).Nonempty := ⟨u, mem_boxBall_self u r_X⟩
      have hXB : boxBall u r_X ⊆ boxBall u r_bare := boxBall_mono u (by omega : r_X ≤ r_bare)
      have hd_pos : 0 < d_off j := by dsimp [d_off]; omega
      have h_col : ∀ x ∈ boxBall u r_X, ∀ y : Box3D L, y ∉ boxBall u r_bare →
          d_off j ≤ boxDist x y :=
        fun x hx y hy => boxDist_ge_of_mem_boxBall_of_not_mem_boxBall u hx hy
      have h_sch := norm_bochnerFilteredOp_interpolated_sub_condExp_schwartz_le
        mem V hw hJ0 hJ1 hs hf hV hX_ne hXB d_off j hd_pos h_col (T_q q) (h_supp_q q hq)
      have h_cardX : ((boxBall u r_X).card : ℝ) ≤ ((2 * r_X + 1 : ℕ) : ℝ) ^ 3 := by
        exact_mod_cast card_boxBall_le_pow u r_X
      have h_cardB : ((boxBall u r_bare).card : ℝ) ≤ ((2 * r_bare + 1 : ℕ) : ℝ) ^ 3 := by
        exact_mod_cast card_boxBall_le_pow u r_bare
      have h_cards : ((boxBall u r_X).card : ℝ) * ((boxBall u r_bare).card : ℝ) ≤
          ((2 * r_X + 1 : ℕ) : ℝ) ^ 3 * ((2 * r_bare + 1 : ℕ) : ℝ) ^ 3 :=
        mul_le_mul h_cardX h_cardB (by positivity) (by positivity)
      have h_env_nn := bdlSchwartzCollarEnvelope_nonneg w hf d_off j
      have h_step1 : ‖Ψ (bochnerFilteredOp H_s w (T_q q))‖ ≤ ε_LR * (J * f_T q) := by
        calc ‖Ψ (bochnerFilteredOp H_s w (T_q q))‖
          _ ≤ (((boxBall u r_X).card : ℝ) * ((boxBall u r_bare).card : ℝ) *
                bdlSchwartzCollarEnvelope w f d_off j) * ‖T_q q‖ := h_sch
          _ ≤ ε_LR * ‖T_q q‖ :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right h_cards h_env_nn) (norm_nonneg _)
          _ ≤ ε_LR * (J * f_T q) :=
            mul_le_mul_of_nonneg_left (h_norm_q q hq_L) hε_nn
      exact le_trans h_step1
        (le_mul_of_one_le_left (mul_nonneg hε_nn (mul_nonneg hJ0 (hf_T.1 q))) (by linarith))
    have h_high_triv : ∀ q ∈ Finset.Icc (r_cut + 1) L,
        ‖Ψ (bochnerFilteredOp H_s w (T_q q))‖ ≤
          (1 + ∫ t : ℝ, ‖w t‖) * (2 * (J * f_T q)) := by
      intro q hq
      have hq_L : q ∈ Finset.Icc 1 L :=
        Finset.mem_Icc.mpr ⟨by have := (Finset.mem_Icc.mp hq).1; omega, (Finset.mem_Icc.mp hq).2⟩
      have h_ce : ‖Ψ (bochnerFilteredOp H_s w (T_q q))‖ ≤
          2 * ‖bochnerFilteredOp H_s w (T_q q)‖ :=
        norm_sub_condExp_le_two_mul_norm (boxBall u r_bare) (bochnerFilteredOp H_s w (T_q q))
      have h_boch : ‖bochnerFilteredOp H_s w (T_q q)‖ ≤
          (1 + ∫ t : ℝ, ‖w t‖) * (J * f_T q) :=
        le_trans (norm_bochnerFilteredOp_le hHs_sa w (T_q q))
          (mul_le_mul (by linarith) (h_norm_q q hq_L) (norm_nonneg _) hw1_nn)
      linarith
    have h_union : Finset.Icc 1 L = Finset.Icc 1 r_cut ∪ Finset.Icc (r_cut + 1) L := by
      ext q; simp only [Finset.mem_Icc, Finset.mem_union]; omega
    have h_disj : Disjoint (Finset.Icc 1 r_cut) (Finset.Icc (r_cut + 1) L) := by
      rw [Finset.disjoint_left]; intro q hq1 hq2; simp only [Finset.mem_Icc] at hq1 hq2; omega
    have h1 : ‖∑ q ∈ Finset.Icc 1 r_cut, Ψ (bochnerFilteredOp H_s w (T_q q))‖ ≤
        J * ((1 + ∫ t : ℝ, ‖w t‖) * (ε_LR * ∑ q ∈ Finset.Icc 1 r_cut, f_T q)) := by
      calc ‖∑ q ∈ Finset.Icc 1 r_cut, Ψ (bochnerFilteredOp H_s w (T_q q))‖
        _ ≤ ∑ q ∈ Finset.Icc 1 r_cut, ‖Ψ (bochnerFilteredOp H_s w (T_q q))‖ := norm_sum_le _ _
        _ ≤ ∑ q ∈ Finset.Icc 1 r_cut, (1 + ∫ t : ℝ, ‖w t‖) * (ε_LR * (J * f_T q)) :=
          Finset.sum_le_sum h_low_lr
        _ = J * ((1 + ∫ t : ℝ, ‖w t‖) * (ε_LR * ∑ q ∈ Finset.Icc 1 r_cut, f_T q)) := by
          rw [← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum]; ring
    have h2 : ‖∑ q ∈ Finset.Icc (r_cut + 1) L, Ψ (bochnerFilteredOp H_s w (T_q q))‖ ≤
        J * ((1 + ∫ t : ℝ, ‖w t‖) * (2 * ∑ q ∈ Finset.Icc (r_cut + 1) L, f_T q)) := by
      calc ‖∑ q ∈ Finset.Icc (r_cut + 1) L, Ψ (bochnerFilteredOp H_s w (T_q q))‖
        _ ≤ ∑ q ∈ Finset.Icc (r_cut + 1) L, ‖Ψ (bochnerFilteredOp H_s w (T_q q))‖ := norm_sum_le _ _
        _ ≤ ∑ q ∈ Finset.Icc (r_cut + 1) L, (1 + ∫ t : ℝ, ‖w t‖) * (2 * (J * f_T q)) :=
          Finset.sum_le_sum h_high_triv
        _ = J * ((1 + ∫ t : ℝ, ‖w t‖) * (2 * ∑ q ∈ Finset.Icc (r_cut + 1) L, f_T q)) := by
          rw [← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum]; ring
    have h_tri := norm_add_le
      (∑ q ∈ Finset.Icc 1 r_cut, Ψ (bochnerFilteredOp H_s w (T_q q)))
      (∑ q ∈ Finset.Icc (r_cut + 1) L, Ψ (bochnerFilteredOp H_s w (T_q q)))
    have h_fin : ‖Ψ B_T‖ ≤
        J * ((1 + ∫ t : ℝ, ‖w t‖) * barePerturbationTailProfile L r_cut f_T ε_LR) := by
      rw [hΨ_sum, h_union, Finset.sum_union h_disj]
      dsimp [barePerturbationTailProfile]; linarith
    exact le_trans h_fin (mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_left
        (barePerturbationTailProfile_le_bdlInhomogeneousBarePerturbationTailProfile
          L r_cut hf_T hε_nn) hw1_nn) hJ0)

/-! ## 1. Concrete `bandpassContinuationWeight` and `bandpassFilterWeight` `boxBall u (j / 2)` Tail Bounds for `D_u`, `B_V`, `B_Q` -/

/-- Universal `boxBall u (j / 2)` tail profile for `sitePerturbationOp` under weight `w`. -/
abbrev bdlSchwartzPerturbationBoxBallTailProfile (w : ℝ → ℂ) (f : ℕ → ℝ) (j : ℕ) : ℝ :=
  bdlSchwartzSumTailProfile w f 0 f j

theorem isSuperpolynomialDecay_bdlSchwartzPerturbationBoxBallTailProfile
    {w : ℝ → ℂ} {f : ℕ → ℝ} (hf : IsSuperpolynomialDecay f)
    (hw_tail : ∀ {c : ℝ}, 0 < c →
      IsSuperpolynomialDecay (fun R : ℕ => ∫ t in {t : ℝ | c * (R : ℝ) ≤ |t|}, ‖w t‖)) :
    IsSuperpolynomialDecay (bdlSchwartzPerturbationBoxBallTailProfile w f) :=
  isSuperpolynomialDecay_bdlSchwartzSumTailProfile hf hf hw_tail 0

/-- **Universal `boxBall u (j / 2)` Conditional Expectation Bound for `sitePerturbationOp V' u`
    (`norm_bochnerFilteredOp_sitePerturbationOp_boxBall_sub_condExp_schwartz_le`)**. -/
theorem norm_bochnerFilteredOp_sitePerturbationOp_boxBall_sub_condExp_schwartz_le
    {L : ℕ} [NeZero L]
    {c_star C β_c c_F η_mem c_mem J s : ℝ} {w : ℝ → ℂ} {f : ℕ → ℝ}
    (mem : Inhomogeneous3DMemoryRealization L qCodeBDL r0BDL mMaxBDL c_star C β_c c_F η_mem c_mem)
    (V V' : QuasiLocalPerturbation 3 L (UniformSite3D L (CodeSlotConfig qCodeBDL)))
    (hw : Integrable w)
    (hJ0 : 0 ≤ J) (hJ1 : J ≤ 1) (hs : s ∈ Set.Icc (-1 : ℝ) 1)
    (hf : IsSuperpolynomialDecay f)
    (hV : V.SatisfiesDecayBound J f) (hV' : V'.SatisfiesDecayBound J f)
    (u : Box3D L) (j : ℕ) (hj_cut : j / 4 ≤ L) :
    let Site := UniformSite3D L (CodeSlotConfig qCodeBDL)
    let H_s := mem.sys.H0 + (scaleQuasiLocalPerturbation s V).totalPerturbation
    let B_V := bochnerFilteredOp H_s w (sitePerturbationOp V' u)
    ‖B_V - condExp Site (boxBall u (j / 2)) B_V‖ ≤
      J * bdlSchwartzPerturbationBoxBallTailProfile w f j := by
  intro Site H_s B_V
  let term_q : ℕ → (ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site) :=
    fun q => ∑ A ∈ (boxCubes 3 L q).filter (fun A => anchorOfCube q A = u), V'.term q A
  have h_norm_q : ∀ q ∈ Finset.Icc 1 L, ‖term_q q‖ ≤ J * f q := by
    intro q hq
    have hcard : (((boxCubes 3 L q).filter (fun A => anchorOfCube q A = u)).card : ℝ) ≤ 1 := by
      exact_mod_cast card_filter_anchor_le_one q u (fun A hA => boxCube_anchorOfCube hA)
    calc ‖term_q q‖
      _ ≤ ∑ A ∈ (boxCubes 3 L q).filter (fun A => anchorOfCube q A = u), ‖V'.term q A‖ :=
        norm_sum_le _ _
      _ ≤ ∑ _A ∈ (boxCubes 3 L q).filter (fun A => anchorOfCube q A = u), (J * f q) :=
        Finset.sum_le_sum fun A hA => hV' q hq A (Finset.mem_filter.mp hA).1
      _ = (((boxCubes 3 L q).filter (fun A => anchorOfCube q A = u)).card : ℝ) * (J * f q) := by
        rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ 1 * (J * f q) := mul_le_mul_of_nonneg_right hcard (mul_nonneg hJ0 (hf.1 q))
      _ = J * f q := one_mul _
  have h_supp_q : ∀ q ∈ Finset.Icc 1 (j / 4),
      IsSupportedOn Site (boxBall u (0 + j / 4)) (term_q q) := by
    intro q hq
    rcases Finset.mem_Icc.mp hq with ⟨hq1, hq_cut⟩
    have hq_L : q ∈ Finset.Icc 1 L := Finset.mem_Icc.mpr ⟨hq1, le_trans hq_cut hj_cut⟩
    have h_sub : boxCube u q ⊆ boxBall u (0 + j / 4) :=
      Set.Subset.trans (boxCube_subset_boxBall u q) (boxBall_mono u (by omega : q ≤ 0 + j / 4))
    refine _root_.isSupportedOn_mono h_sub
      (isSupportedOn_finset_sum (boxCube u q) _ _ fun A hA => ?_)
    have hA_mem : A ∈ boxCubes 3 L q := (Finset.mem_filter.mp hA).1
    have hA_eq : A = boxCube u q :=
      Finset.mem_singleton.mp
        (filter_anchor_subset_singleton q u (fun B hB => boxCube_anchorOfCube hB) hA)
    rw [← hA_eq]
    exact V'.is_supported q hq_L A hA_mem
  exact norm_bochnerFilteredOp_sum_boxBall_sub_condExp_le
    mem V hw hJ0 hJ1 hs hf hf hV 0 u j hj_cut term_q h_norm_q h_supp_q

/-- **`bandpassContinuationWeight` `boxBall u (j / 2)` Tail Bound for `katoHastingsGeneratorOp`
    (`norm_katoHastingsGeneratorOp_W_BP_sitePerturbationOp_boxBall_sub_condExp_le`)**. -/
theorem norm_katoHastingsGeneratorOp_W_BP_sitePerturbationOp_boxBall_sub_condExp_le
    {L : ℕ} [NeZero L]
    {c_star C β_c c_F η_mem c_mem J τ : ℝ} {f : ℕ → ℝ}
    (mem : Inhomogeneous3DMemoryRealization L qCodeBDL r0BDL mMaxBDL c_star C β_c c_F η_mem c_mem)
    (V : QuasiLocalPerturbation 3 L (UniformSite3D L (CodeSlotConfig qCodeBDL)))
    (hJ0 : 0 ≤ J) (hJ1 : J ≤ 1) (hτ : τ ∈ Set.Icc (0 : ℝ) 1)
    (hf : IsSuperpolynomialDecay f) (hV : V.SatisfiesDecayBound J f)
    (u : Box3D L) (j : ℕ) (hj_cut : j / 4 ≤ L) :
    let Site := UniformSite3D L (CodeSlotConfig qCodeBDL)
    let D_u := katoHastingsGeneratorOp (mem.sys.H0 + τ • V.totalPerturbation) bandpassContinuationWeight (sitePerturbationOp V u)
    ‖D_u - condExp Site (boxBall u (j / 2)) D_u‖ ≤
      J * bdlSchwartzPerturbationBoxBallTailProfile bandpassContinuationWeight f j := by
  intro Site D_u
  have hH_eq : mem.sys.H0 + τ • V.totalPerturbation =
      mem.sys.H0 + (scaleQuasiLocalPerturbation τ V).totalPerturbation := by
    rw [scaleQuasiLocalPerturbation_V_tot, clm_real_smul]
  have hD_eq : D_u =
      bochnerFilteredOp (mem.sys.H0 + (scaleQuasiLocalPerturbation τ V).totalPerturbation) bandpassContinuationWeight
        (sitePerturbationOp V u) := by
    dsimp [D_u]; rw [hH_eq]; rfl
  rw [hD_eq]
  exact norm_bochnerFilteredOp_sitePerturbationOp_boxBall_sub_condExp_schwartz_le
    mem V V integrable_W_BP hJ0 hJ1 ⟨by linarith [hτ.1], hτ.2⟩ hf hV hV u j hj_cut

/-- **`bandpassFilterWeight` Bare-Frame `B_V` `boxBall u (j / 2)` Tail Bound
    (`norm_bare_bochnerFilteredOp_w_BP_sitePerturbationOp_boxBall_sub_condExp_le`)**. -/
theorem norm_bare_bochnerFilteredOp_w_BP_sitePerturbationOp_boxBall_sub_condExp_le
    {L : ℕ} [NeZero L]
    {c_star C β_c c_F η_mem c_mem J s : ℝ} {f : ℕ → ℝ}
    (mem : Inhomogeneous3DMemoryRealization L qCodeBDL r0BDL mMaxBDL c_star C β_c c_F η_mem c_mem)
    (V : QuasiLocalPerturbation 3 L (UniformSite3D L (CodeSlotConfig qCodeBDL)))
    (hJ0 : 0 ≤ J) (hJ1 : J ≤ 1) (hs : s ∈ Set.Icc (0 : ℝ) 1)
    (hf : IsSuperpolynomialDecay f) (hV : V.SatisfiesDecayBound J f)
    (u : Box3D L) (j : ℕ) (hj_cut : j / 4 ≤ L) :
    let Site := UniformSite3D L (CodeSlotConfig qCodeBDL)
    let V_s := scaleQuasiLocalPerturbation s V
    let H_s := mem.sys.H0 + V_s.totalPerturbation
    let B_V := bochnerFilteredOp H_s bandpassFilterWeight (sitePerturbationOp V_s u)
    ‖B_V - condExp Site (boxBall u (j / 2)) B_V‖ ≤
      J * bdlSchwartzPerturbationBoxBallTailProfile bandpassFilterWeight f j :=
  norm_bochnerFilteredOp_sitePerturbationOp_boxBall_sub_condExp_schwartz_le
    mem V (scaleQuasiLocalPerturbation s V) integrable_w_BP hJ0 hJ1
    ⟨by linarith [hs.1], hs.2⟩ hf hV
    (satisfiesDecayBound_scaleQuasiLocalPerturbation_of_mem_Icc V hs hJ0 hf.1 hV)
    u j hj_cut

/-- Universal `boxBall u (j / 2)` tail profile for `B_Q` under `bandpassFilterWeight`. -/
abbrev bdlSchwartzCheckBoxBallTailProfile (f : ℕ → ℝ) (j : ℕ) : ℝ :=
  bdlSchwartzSumTailProfile bandpassContinuationWeight f (2 * r0BDL) (bdlCheckCommutatorWeight f) j

theorem isSuperpolynomialDecay_bdlSchwartzCheckBoxBallTailProfile
    {f : ℕ → ℝ} (hf : IsSuperpolynomialDecay f) :
    IsSuperpolynomialDecay (bdlSchwartzCheckBoxBallTailProfile f) :=
  isSuperpolynomialDecay_bdlSchwartzSumTailProfile hf
    (isSuperpolynomialDecay_bdlCheckCommutatorWeight hf)
    (fun hc => isSuperpolynomialDecay_tail_integral_norm_W_BP hc)
    (2 * r0BDL)

/-- **`bandpassFilterWeight` Bare-Frame `B_Q` `boxBall u (j / 2)` Tail Bound
    (`norm_bare_bochnerFilteredOp_w_BP_siteCheckOp_boxBall_sub_condExp_le`)**. -/
theorem norm_bare_bochnerFilteredOp_w_BP_siteCheckOp_boxBall_sub_condExp_le
    {L : ℕ} [NeZero L]
    {c_star C β_c c_F η_mem c_mem J s : ℝ} {f : ℕ → ℝ}
    (mem : Inhomogeneous3DMemoryRealization L qCodeBDL r0BDL mMaxBDL c_star C β_c c_F η_mem c_mem)
    (V : QuasiLocalPerturbation 3 L (UniformSite3D L (CodeSlotConfig qCodeBDL)))
    (hJ0 : 0 ≤ J) (hJ1 : J ≤ 1) (hs : s ∈ Set.Icc (0 : ℝ) 1)
    (hf : IsSuperpolynomialDecay f) (hV : V.SatisfiesDecayBound J f)
    (u : Box3D L) (j : ℕ) (hj_cut : j / 4 ≤ L) :
    let Site := UniformSite3D L (CodeSlotConfig qCodeBDL)
    let V_s := scaleQuasiLocalPerturbation s V
    let H_s := mem.sys.H0 + V_s.totalPerturbation
    let B_Q := bochnerFilteredOp H_s bandpassFilterWeight (mem.sys.siteCheckOp u) - mem.sys.siteCheckOp u
    ‖B_Q - condExp Site (boxBall u (j / 2)) B_Q‖ ≤
      J * bdlSchwartzCheckBoxBallTailProfile f j := by
  intro Site V_s H_s B_Q
  let Q_u := mem.sys.siteCheckOp u
  have hHs_sa : IsSelfAdjoint H_s :=
    isSelfAdjoint_add_clm mem.sys.isSelfAdjoint_H0 V_s.isSelfAdjoint_totalPerturbation
  have h_comm_Q : Commute mem.sys.H0 Q_u := by
    dsimp [Q_u]; rw [siteCheckOp_eq_anchoredSiteCheckOp]
    exact (isSelfAdjoint_and_commute_H0_anchoredSiteCheckOp anchorOfRegion mem.sys u).2
  have hVs_dec : V_s.SatisfiesDecayBound J f :=
    satisfiesDecayBound_scaleQuasiLocalPerturbation_of_mem_Icc V hs hJ0 hf.1 hV
  let S_0 := boxBall u (2 * r0BDL)
  let C_q : ℕ → (ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site) :=
    fun q => ∑ A ∈ (boxCubes 3 L q).filter (fun A => ¬ Disjoint A S_0),
      opCommutator (V_s.term q A) Q_u
  have h_comm_sum : opCommutator V_s.totalPerturbation Q_u = ∑ q ∈ Finset.Icc 1 L, C_q q :=
    opCommutator_V_tot_eq_sum_filter_not_disjoint V_s
      (isSupportedOn_boxBall_siteCheckOp_inhomogeneous mem u le_rfl)
  have hBQ_eq : B_Q =
      (Complex.I : ℂ) • bochnerFilteredOp H_s bandpassContinuationWeight (∑ q ∈ Finset.Icc 1 L, C_q q) := by
    dsimp [B_Q, H_s]
    rw [bochnerFilteredOp_w_BP_sub_self_eq_I_smul_bochnerFilteredOp_W_BP hHs_sa h_comm_Q,
      h_comm_sum]
  have h_norm_eq : ‖B_Q - condExp Site (boxBall u (j / 2)) B_Q‖ =
      ‖bochnerFilteredOp H_s bandpassContinuationWeight (∑ q ∈ Finset.Icc 1 L, C_q q) -
        condExp Site (boxBall u (j / 2))
          (bochnerFilteredOp H_s bandpassContinuationWeight (∑ q ∈ Finset.Icc 1 L, C_q q))‖ := by
    have h_diff : B_Q - condExp Site (boxBall u (j / 2)) B_Q =
        (Complex.I : ℂ) • (bochnerFilteredOp H_s bandpassContinuationWeight (∑ q ∈ Finset.Icc 1 L, C_q q) -
          condExp Site (boxBall u (j / 2))
            (bochnerFilteredOp H_s bandpassContinuationWeight (∑ q ∈ Finset.Icc 1 L, C_q q))) := by
      rw [hBQ_eq, condExp_smul, smul_sub]
    rw [h_diff, norm_smul, Complex.norm_I, one_mul]
  rw [h_norm_eq]
  have h_norm_q : ∀ q ∈ Finset.Icc 1 L, ‖C_q q‖ ≤ J * bdlCheckCommutatorWeight f q := by
    intro q hq
    have hq0 : q ≠ 0 := by have := (Finset.mem_Icc.mp hq).1; omega
    have h_sub_filt : (boxCubes 3 L q).filter (fun A => ¬ Disjoint A S_0) ⊆
        (boxCubes 3 L q).filter (fun A =>
          ¬ Disjoint A (boxCube (shiftCorner u (2 * r0BDL)) (2 * (2 * r0BDL) + 1))) := by
      intro A hA
      rcases Finset.mem_filter.mp hA with ⟨hA_mem, hnd⟩
      exact Finset.mem_filter.mpr ⟨hA_mem, fun hdisj =>
        hnd (Finset.disjoint_of_subset_right (boxBall_subset_boxCube u (2 * r0BDL)) hdisj)⟩
    have hcard : (((boxCubes 3 L q).filter (fun A => ¬ Disjoint A S_0)).card : ℝ) ≤
        ((q + (4 * r0BDL + 1) : ℕ) : ℝ) ^ 3 := by
      have hc := le_trans (Finset.card_le_card h_sub_filt)
        (card_filter_not_disjoint_boxCube_le_pow (shiftCorner u (2 * r0BDL)) q (2 * (2 * r0BDL) + 1))
      rw [show 2 * (2 * r0BDL) + 1 = 4 * r0BDL + 1 by omega] at hc
      exact_mod_cast hc
    have hQ_le := norm_siteCheckOp_inhomogeneous_le mem u
    calc ‖C_q q‖
      _ ≤ ∑ A ∈ (boxCubes 3 L q).filter (fun A => ¬ Disjoint A S_0),
            ‖opCommutator (V_s.term q A) Q_u‖ := norm_sum_le _ _
      _ ≤ ∑ _A ∈ (boxCubes 3 L q).filter (fun A => ¬ Disjoint A S_0),
            (2 * (J * f q) * bdlInhomogeneousSiteWeightBound) := by
        refine Finset.sum_le_sum fun A hA => ?_
        have h1 := norm_opCommutator_le (V_s.term q A) Q_u
        have h2 := hVs_dec q hq A (Finset.mem_filter.mp hA).1
        exact le_trans h1 (mul_le_mul
          (mul_le_mul_of_nonneg_left h2 zero_le_two) hQ_le (norm_nonneg Q_u)
          (mul_nonneg zero_le_two (mul_nonneg hJ0 (hf.1 q))))
      _ = (((boxCubes 3 L q).filter (fun A => ¬ Disjoint A S_0)).card : ℝ) *
            (2 * (J * f q) * bdlInhomogeneousSiteWeightBound) := by
        rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ ((q + (4 * r0BDL + 1) : ℕ) : ℝ) ^ 3 *
            (2 * (J * f q) * bdlInhomogeneousSiteWeightBound) :=
        mul_le_mul_of_nonneg_right hcard
          (mul_nonneg (mul_nonneg zero_le_two (mul_nonneg hJ0 (hf.1 q)))
            bdlInhomogeneousSiteWeightBound_nonneg)
      _ = J * bdlCheckCommutatorWeight f q := by
        dsimp [bdlCheckCommutatorWeight]; rw [if_neg hq0]; ring
  have h_supp_q : ∀ q ∈ Finset.Icc 1 (j / 4),
      IsSupportedOn Site (boxBall u (2 * r0BDL + j / 4)) (C_q q) := by
    intro q hq
    rcases Finset.mem_Icc.mp hq with ⟨hq1, hq_cut⟩
    have hq_L : q ∈ Finset.Icc 1 L := Finset.mem_Icc.mpr ⟨hq1, le_trans hq_cut hj_cut⟩
    let r_X := 2 * r0BDL + j / 4
    have hQ_supp_X : IsSupportedOn Site (boxBall u r_X) Q_u :=
      isSupportedOn_boxBall_siteCheckOp_inhomogeneous mem u (by omega : 2 * r0BDL ≤ r_X)
    refine isSupportedOn_finset_sum (boxBall u r_X) _ _ fun A hA => ?_
    have hA_mem : A ∈ boxCubes 3 L q := (Finset.mem_filter.mp hA).1
    rcases Finset.not_disjoint_iff.mp (Finset.mem_filter.mp hA).2 with ⟨z, hzA, hz_ball⟩
    have hA_sub : A ⊆ boxBall u r_X := by
      intro x hxA
      have hA_eq : boxCube (anchorOfCube q A) q = A := boxCube_anchorOfCube hA_mem
      have hz_cube : z ∈ boxCube (anchorOfCube q A) q := hA_eq.symm ▸ hzA
      have hx_cube : x ∈ boxCube (anchorOfCube q A) q := hA_eq.symm ▸ hxA
      dsimp only [S_0, r_X] at hz_ball ⊢
      simp only [boxCube, boxBall, Finset.mem_filter, Finset.mem_univ, true_and] at hz_cube hx_cube hz_ball ⊢
      have hzx : boxDist z x ≤ q := Finset.sup_le fun i _ => by
        have hzi := hz_cube i; have hxi := hx_cube i; dsimp [coordDist]; omega
      have h_tri := boxDist_triangle u z x; omega
    have hV_supp_X : IsSupportedOn Site (boxBall u r_X) (V_s.term q A) :=
      _root_.isSupportedOn_mono hA_sub (V_s.is_supported q hq_L A hA_mem)
    exact _root_.isSupportedOn_sub (boxBall u r_X)
      (_root_.isSupportedOn_mul (boxBall u r_X) hV_supp_X hQ_supp_X)
      (_root_.isSupportedOn_mul (boxBall u r_X) hQ_supp_X hV_supp_X)
  exact norm_bochnerFilteredOp_sum_boxBall_sub_condExp_le mem V integrable_W_BP hJ0 hJ1
    ⟨by linarith [hs.1], hs.2⟩ hf (isSuperpolynomialDecay_bdlCheckCommutatorWeight hf) hV
    (2 * r0BDL) u j hj_cut C_q h_norm_q h_supp_q

end
