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

import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Lebesgue.Integral
import Proofs.KatoODE.ContinuationWeightKernel
import Proofs.KatoODE.TimeEvolutionPerturbationDuhamel

open scoped Classical InnerProduct ComplexConjugate BigOperators
open Filter Topology Asymptotics ContinuousLinearMap MeasureTheory
open KMSPinchedGibbs PerturbedThermalBarrier WeldedHierarchy WeldedHierarchy.BDLDecoder
open InhomogeneousMemoryChallenge

noncomputable section

set_option maxRecDepth 200000
set_option maxHeartbeats 800000

/-!
# Exact Kato Differential Commutator Identity for Perturbed Projectors

Proves the product-measure Fubini triangle identity (`posDuhamelTriangle`, `negDuhamelTriangle`) linking `bandpassFilterWeight` and `bandpassContinuationWeight`. Establishes Kato's exact differential equation `hasDerivAt_perturbedGroundSpectralProj_eq_katoGenerator_commutator` expressing the coupling derivative of `perturbedGroundSpectralProj` as $i [\mathcal{D}(s), P(s)]$ whenever the spectral gap is at least one-half.

## References

* Part I, Section 6.2 (`subsec:bochner-lr`), Equation (68) (`eq:wBP-WBP-ibp`)
* Part I, Section 6.3 (`subsec:qac-block-diag`), Equation (75) (`eq:qac-generator-def`), Proposition 6.4 (`prop:qac-block-diagonalization`)
* Kato (1950), Journal of the Physical Society of Japan 5, 435–439
* Hastings–Wen (2005), Physical Review B 72, 045141
-/

/-! ## 1. Continuation Weight `bandpassContinuationWeight` & Bochner Fubini Swap -/

/-- By evenness of `bandpassFilterWeight`, the integral over `Set.Iio τ` equals the integral over `Set.Ici (-τ)`. -/
lemma integral_w_BP_Iio_eq_Ici_neg (τ : ℝ) :
    (∫ t in Set.Iio τ, bandpassFilterWeight t) = ∫ t in Set.Ici (-τ), bandpassFilterWeight t := by
  rw [← integral_Iic_eq_integral_Iio, integral_Ici_eq_integral_Ioi, ← integral_comp_neg_Iic]
  refine setIntegral_congr_fun measurableSet_Iic fun t _ => ?_
  exact (w_BP_even t).symm

/-- Positive Duhamel triangle $\{(t, \tau) \in \mathbb{R}^2 \mid 0 < \tau \le t\}$. -/
def posDuhamelTriangle : Set (ℝ × ℝ) :=
  {p : ℝ × ℝ | 0 < p.2} ∩ {p : ℝ × ℝ | p.2 ≤ p.1}

/-- Negative Duhamel triangle $\{(t, \tau) \in \mathbb{R}^2 \mid t < \tau < 0\}$. -/
def negDuhamelTriangle : Set (ℝ × ℝ) :=
  {p : ℝ × ℝ | p.1 < p.2} ∩ {p : ℝ × ℝ | p.2 < 0}

lemma measurableSet_posDuhamelTriangle : MeasurableSet posDuhamelTriangle :=
  (measurableSet_lt measurable_const measurable_snd).inter
    (measurableSet_le measurable_snd measurable_fst)

lemma measurableSet_negDuhamelTriangle : MeasurableSet negDuhamelTriangle :=
  (measurableSet_lt measurable_fst measurable_snd).inter
    (measurableSet_lt measurable_snd measurable_const)

lemma posDuhamelTriangle_indicator_slice_left {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E]
    (G : ℝ → E) (t : ℝ) :
    (fun τ : ℝ => posDuhamelTriangle.indicator (fun p : ℝ × ℝ => bandpassFilterWeight p.1 • G p.2) (t, τ)) =
      (Set.Ioc (0 : ℝ) t).indicator (fun τ : ℝ => bandpassFilterWeight t • G τ) := by
  funext τ; rfl

lemma negDuhamelTriangle_indicator_slice_left {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E]
    (G : ℝ → E) (t : ℝ) :
    (fun τ : ℝ => negDuhamelTriangle.indicator (fun p : ℝ × ℝ => bandpassFilterWeight p.1 • G p.2) (t, τ)) =
      (Set.Ioo t (0 : ℝ)).indicator (fun τ : ℝ => bandpassFilterWeight t • G τ) := by
  funext τ; rfl

lemma posDuhamelTriangle_indicator_slice_right {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E]
    (G : ℝ → E) (τ : ℝ) :
    (fun t : ℝ => posDuhamelTriangle.indicator (fun p : ℝ × ℝ => bandpassFilterWeight p.1 • G p.2) (t, τ)) =
      if 0 < τ then (Set.Ici τ).indicator (fun t : ℝ => bandpassFilterWeight t • G τ) else 0 := by
  funext t
  by_cases hτ : 0 < τ
  · rw [if_pos hτ]
    by_cases ht : τ ≤ t
    · have h_mem : (t, τ) ∈ posDuhamelTriangle := ⟨hτ, ht⟩
      have h_ici : t ∈ Set.Ici τ := ht
      rw [Set.indicator_of_mem h_mem, Set.indicator_of_mem h_ici]
    · have h_nmem : (t, τ) ∉ posDuhamelTriangle := fun h => ht h.2
      have h_nici : t ∉ Set.Ici τ := ht
      rw [Set.indicator_of_notMem h_nmem, Set.indicator_of_notMem h_nici]
  · rw [if_neg hτ, Pi.zero_apply, Set.indicator_of_notMem (fun h => hτ h.1)]

lemma negDuhamelTriangle_indicator_slice_right {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E]
    (G : ℝ → E) (τ : ℝ) :
    (fun t : ℝ => negDuhamelTriangle.indicator (fun p : ℝ × ℝ => bandpassFilterWeight p.1 • G p.2) (t, τ)) =
      if τ < 0 then (Set.Iio τ).indicator (fun t : ℝ => bandpassFilterWeight t • G τ) else 0 := by
  funext t
  by_cases hτ : τ < 0
  · rw [if_pos hτ]
    by_cases ht : t < τ
    · have h_mem : (t, τ) ∈ negDuhamelTriangle := ⟨ht, hτ⟩
      have h_iio : t ∈ Set.Iio τ := ht
      rw [Set.indicator_of_mem h_mem, Set.indicator_of_mem h_iio]
    · have h_nmem : (t, τ) ∉ negDuhamelTriangle := fun h => ht h.1
      have h_niio : t ∉ Set.Iio τ := ht
      rw [Set.indicator_of_notMem h_nmem, Set.indicator_of_notMem h_niio]
  · rw [if_neg hτ, Pi.zero_apply, Set.indicator_of_notMem (fun h => hτ h.2)]

/-- Product integrability on `ℝ × ℝ` over `posDuhamelTriangle` for any continuous bounded `G`. -/
lemma integrable_posDuhamelTriangle_w_BP_smul {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    {G : ℝ → E} {M : ℝ} (hG_cont : Continuous G) (hM_nn : 0 ≤ M)
    (hG_bdd : ∀ τ : ℝ, ‖G τ‖ ≤ M) :
    Integrable
      (posDuhamelTriangle.indicator (fun p : ℝ × ℝ => bandpassFilterWeight p.1 • G p.2))
      (MeasureTheory.volume.prod MeasureTheory.volume) := by
  let H : ℝ × ℝ → E := fun p => bandpassFilterWeight p.1 • G p.2
  have hH_cont : Continuous H :=
    (wBPSchwartz.continuous.comp continuous_fst).smul (hG_cont.comp continuous_snd)
  have h_meas : AEStronglyMeasurable (posDuhamelTriangle.indicator H)
      (MeasureTheory.volume.prod MeasureTheory.volume) :=
    hH_cont.aestronglyMeasurable.indicator measurableSet_posDuhamelTriangle
  rw [MeasureTheory.integrable_prod_iff h_meas]
  refine ⟨Filter.Eventually.of_forall (fun t => ?_), ?_⟩
  · rw [posDuhamelTriangle_indicator_slice_left G t]
    exact (integrable_indicator_iff measurableSet_Ioc).mpr
      (hG_cont.const_smul (bandpassFilterWeight t)).integrableOn_Ioc
  · refine (integrable_norm_w_BP_mul_abs.mul_const M).mono'
      h_meas.norm.integral_prod_right' (Filter.Eventually.of_forall (fun t => ?_))
    have h_slice : (fun τ : ℝ => ‖posDuhamelTriangle.indicator H (t, τ)‖) =
        (Set.Ioc (0 : ℝ) t).indicator (fun τ : ℝ => ‖bandpassFilterWeight t • G τ‖) := by
      funext τ
      rw [congr_fun (posDuhamelTriangle_indicator_slice_left G t) τ,
        norm_indicator_eq_indicator_norm]
    rw [h_slice, MeasureTheory.integral_indicator measurableSet_Ioc]
    by_cases ht : 0 ≤ t
    · rw [← intervalIntegral.integral_of_le ht]
      have h_le : ∀ τ ∈ Set.uIoc (0 : ℝ) t, ‖‖bandpassFilterWeight t • G τ‖‖ ≤ ‖bandpassFilterWeight t‖ * M := by
        intro τ _
        rw [Real.norm_of_nonneg (norm_nonneg _), norm_smul]
        exact mul_le_mul_of_nonneg_left (hG_bdd τ) (norm_nonneg _)
      have h_int := intervalIntegral.norm_integral_le_of_norm_le_const h_le
      rw [sub_zero, abs_of_nonneg ht] at h_int
      calc ‖∫ τ in (0 : ℝ)..t, ‖bandpassFilterWeight t • G τ‖‖
        _ ≤ ‖bandpassFilterWeight t‖ * M * t := h_int
        _ = ‖bandpassFilterWeight t‖ * |t| * M := by rw [abs_of_nonneg ht]; ring
    · have h_empty : Set.Ioc (0 : ℝ) t = ∅ := Set.Ioc_eq_empty (by linarith)
      rw [h_empty, MeasureTheory.Measure.restrict_empty, MeasureTheory.integral_zero_measure,
        norm_zero]
      positivity

/-- Product integrability on `ℝ × ℝ` over `negDuhamelTriangle` for any continuous bounded `G`. -/
lemma integrable_negDuhamelTriangle_w_BP_smul {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    {G : ℝ → E} {M : ℝ} (hG_cont : Continuous G) (hM_nn : 0 ≤ M)
    (hG_bdd : ∀ τ : ℝ, ‖G τ‖ ≤ M) :
    Integrable
      (negDuhamelTriangle.indicator (fun p : ℝ × ℝ => bandpassFilterWeight p.1 • G p.2))
      (MeasureTheory.volume.prod MeasureTheory.volume) := by
  let H : ℝ × ℝ → E := fun p => bandpassFilterWeight p.1 • G p.2
  have hH_cont : Continuous H :=
    (wBPSchwartz.continuous.comp continuous_fst).smul (hG_cont.comp continuous_snd)
  have h_meas : AEStronglyMeasurable (negDuhamelTriangle.indicator H)
      (MeasureTheory.volume.prod MeasureTheory.volume) :=
    hH_cont.aestronglyMeasurable.indicator measurableSet_negDuhamelTriangle
  rw [MeasureTheory.integrable_prod_iff h_meas]
  refine ⟨Filter.Eventually.of_forall (fun t => ?_), ?_⟩
  · rw [negDuhamelTriangle_indicator_slice_left G t]
    exact (integrable_indicator_iff measurableSet_Ioo).mpr
      ((hG_cont.const_smul (bandpassFilterWeight t)).integrableOn_Icc.mono_set Set.Ioo_subset_Icc_self)
  · refine (integrable_norm_w_BP_mul_abs.mul_const M).mono'
      h_meas.norm.integral_prod_right' (Filter.Eventually.of_forall (fun t => ?_))
    have h_slice : (fun τ : ℝ => ‖negDuhamelTriangle.indicator H (t, τ)‖) =
        (Set.Ioo t (0 : ℝ)).indicator (fun τ : ℝ => ‖bandpassFilterWeight t • G τ‖) := by
      funext τ
      rw [congr_fun (negDuhamelTriangle_indicator_slice_left G t) τ,
        norm_indicator_eq_indicator_norm]
    rw [h_slice, MeasureTheory.integral_indicator measurableSet_Ioo,
      ← MeasureTheory.integral_Ioc_eq_integral_Ioo]
    by_cases ht : t ≤ 0
    · rw [← intervalIntegral.integral_of_le ht]
      have h_le : ∀ τ ∈ Set.uIoc t (0 : ℝ), ‖‖bandpassFilterWeight t • G τ‖‖ ≤ ‖bandpassFilterWeight t‖ * M := by
        intro τ _
        rw [Real.norm_of_nonneg (norm_nonneg _), norm_smul]
        exact mul_le_mul_of_nonneg_left (hG_bdd τ) (norm_nonneg _)
      have h_int := intervalIntegral.norm_integral_le_of_norm_le_const h_le
      rw [zero_sub, abs_neg] at h_int
      calc ‖∫ τ in t..(0 : ℝ), ‖bandpassFilterWeight t • G τ‖‖
        _ ≤ ‖bandpassFilterWeight t‖ * M * |t| := h_int
        _ = ‖bandpassFilterWeight t‖ * |t| * M := by ring
    · have h_empty : Set.Ioc t (0 : ℝ) = ∅ := Set.Ioc_eq_empty (by linarith)
      rw [h_empty, MeasureTheory.Measure.restrict_empty, MeasureTheory.integral_zero_measure,
        norm_zero]
      positivity

lemma integral_posDuhamelTriangle_slice_right {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    (G : ℝ → E) (τ : ℝ) :
    letI : NormedSpace ℝ E := NormedSpace.restrictScalars ℝ ℂ E
    (∫ t : ℝ, posDuhamelTriangle.indicator (fun p : ℝ × ℝ => bandpassFilterWeight p.1 • G p.2) (t, τ)) =
      (if 0 < τ then ∫ t in Set.Ici τ, bandpassFilterWeight t else 0) • G τ := by
  letI : NormedSpace ℝ E := NormedSpace.restrictScalars ℝ ℂ E
  rw [posDuhamelTriangle_indicator_slice_right G τ]
  by_cases hτ : 0 < τ
  · rw [if_pos hτ, if_pos hτ, MeasureTheory.integral_indicator measurableSet_Ici,
      integral_smul_const]
  · rw [if_neg hτ, if_neg hτ, Pi.zero_def, MeasureTheory.integral_zero, zero_smul]

lemma integral_negDuhamelTriangle_slice_right {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    (G : ℝ → E) (τ : ℝ) :
    letI : NormedSpace ℝ E := NormedSpace.restrictScalars ℝ ℂ E
    (∫ t : ℝ, negDuhamelTriangle.indicator (fun p : ℝ × ℝ => bandpassFilterWeight p.1 • G p.2) (t, τ)) =
      (if τ < 0 then ∫ t in Set.Ici (-τ), bandpassFilterWeight t else 0) • G τ := by
  letI : NormedSpace ℝ E := NormedSpace.restrictScalars ℝ ℂ E
  rw [negDuhamelTriangle_indicator_slice_right G τ]
  by_cases hτ : τ < 0
  · rw [if_pos hτ, if_pos hτ, MeasureTheory.integral_indicator measurableSet_Iio,
      integral_smul_const, integral_w_BP_Iio_eq_Ici_neg]
  · rw [if_neg hτ, if_neg hτ, Pi.zero_def, MeasureTheory.integral_zero, zero_smul]

lemma integral_pos_sub_neg_duhamelTriangle_slice_right {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    (G : ℝ → E) (τ : ℝ) :
    letI : NormedSpace ℝ E := NormedSpace.restrictScalars ℝ ℂ E
    (∫ t : ℝ, posDuhamelTriangle.indicator (fun p : ℝ × ℝ => bandpassFilterWeight p.1 • G p.2) (t, τ)) -
      (∫ t : ℝ, negDuhamelTriangle.indicator (fun p : ℝ × ℝ => bandpassFilterWeight p.1 • G p.2) (t, τ)) =
      bandpassContinuationWeight τ • G τ := by
  letI : NormedSpace ℝ E := NormedSpace.restrictScalars ℝ ℂ E
  rw [integral_posDuhamelTriangle_slice_right, integral_negDuhamelTriangle_slice_right]
  dsimp [bandpassContinuationWeight, wBPContinuationWeight]
  by_cases hpos : 0 < τ
  · have hneg : ¬ τ < 0 := not_lt.mpr hpos.le
    simp only [hpos, hneg, ↓reduceIte, zero_smul, sub_zero]
  · by_cases hneg : τ < 0
    · simp only [hpos, hneg, ↓reduceIte, zero_smul, zero_sub, neg_smul]
    · simp only [hpos, hneg, ↓reduceIte, zero_smul, sub_zero]

lemma integral_pos_sub_neg_duhamelTriangle_slice_left {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    (G : ℝ → E) (t : ℝ) :
    letI : NormedSpace ℝ E := NormedSpace.restrictScalars ℝ ℂ E
    (∫ τ : ℝ, posDuhamelTriangle.indicator (fun p : ℝ × ℝ => bandpassFilterWeight p.1 • G p.2) (t, τ)) -
      (∫ τ : ℝ, negDuhamelTriangle.indicator (fun p : ℝ × ℝ => bandpassFilterWeight p.1 • G p.2) (t, τ)) =
      bandpassFilterWeight t • ∫ τ in (0 : ℝ)..t, G τ := by
  letI : NormedSpace ℝ E := NormedSpace.restrictScalars ℝ ℂ E
  rw [posDuhamelTriangle_indicator_slice_left G t, negDuhamelTriangle_indicator_slice_left G t,
    MeasureTheory.integral_indicator measurableSet_Ioc,
    MeasureTheory.integral_indicator measurableSet_Ioo,
    ← MeasureTheory.integral_Ioc_eq_integral_Ioo,
    MeasureTheory.integral_smul, MeasureTheory.integral_smul, ← smul_sub]
  rfl

/-- **Bochner Fubini Identity for `bandpassFilterWeight` and `bandpassContinuationWeight` (`integrable_and_integral_w_BP_smul_intervalIntegral_eq_integral_W_BP_smul`)**:
    For any continuous bounded Banach-space-valued function $G : \mathbb{R} \to E$,
    $\tau \mapsto W_{\mathrm{BP}}(\tau) \bullet G(\tau)$ is Bochner integrable on $\mathbb{R}$ and
    $$\int_{t : \mathbb{R}} w_{\mathrm{BP}}(t) \bullet \left(\int_0^t G(\tau)\,d\tau\right)
      = \int_{\tau : \mathbb{R}} W_{\mathrm{BP}}(\tau) \bullet G(\tau).$$ -/
theorem integrable_and_integral_w_BP_smul_intervalIntegral_eq_integral_W_BP_smul {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    {G : ℝ → E} {M : ℝ} (hG_cont : Continuous G) (hM_nn : 0 ≤ M)
    (hG_bdd : ∀ τ : ℝ, ‖G τ‖ ≤ M) :
    letI : NormedSpace ℝ E := NormedSpace.restrictScalars ℝ ℂ E
    Integrable (fun τ : ℝ => bandpassContinuationWeight τ • G τ) MeasureTheory.volume ∧
    (∫ t : ℝ, bandpassFilterWeight t • (∫ τ in (0 : ℝ)..t, G τ)) =
      ∫ τ : ℝ, bandpassContinuationWeight τ • G τ := by
  letI : NormedSpace ℝ E := NormedSpace.restrictScalars ℝ ℂ E
  have h_pos := integrable_posDuhamelTriangle_w_BP_smul hG_cont hM_nn hG_bdd
  have h_neg := integrable_negDuhamelTriangle_w_BP_smul hG_cont hM_nn hG_bdd
  have h_right_eq :
      (fun τ : ℝ => bandpassContinuationWeight τ • G τ) =
        (fun τ : ℝ =>
          (∫ t : ℝ, posDuhamelTriangle.indicator (fun p : ℝ × ℝ => bandpassFilterWeight p.1 • G p.2) (t, τ)) -
            (∫ t : ℝ, negDuhamelTriangle.indicator (fun p : ℝ × ℝ => bandpassFilterWeight p.1 • G p.2) (t, τ))) := by
    funext τ
    exact (integral_pos_sub_neg_duhamelTriangle_slice_right G τ).symm
  have h_left_eq :
      (fun t : ℝ => bandpassFilterWeight t • (∫ τ in (0 : ℝ)..t, G τ)) =
        (fun t : ℝ =>
          (∫ τ : ℝ, posDuhamelTriangle.indicator (fun p : ℝ × ℝ => bandpassFilterWeight p.1 • G p.2) (t, τ)) -
            (∫ τ : ℝ, negDuhamelTriangle.indicator (fun p : ℝ × ℝ => bandpassFilterWeight p.1 • G p.2) (t, τ))) := by
    funext t
    exact (integral_pos_sub_neg_duhamelTriangle_slice_left G t).symm
  refine ⟨?_, ?_⟩
  · rw [h_right_eq]
    exact h_pos.integral_prod_right.sub h_neg.integral_prod_right
  · rw [h_left_eq, h_right_eq,
      MeasureTheory.integral_sub h_pos.integral_prod_left h_neg.integral_prod_left,
      MeasureTheory.integral_sub h_pos.integral_prod_right h_neg.integral_prod_right,
      MeasureTheory.integral_integral_swap
        (f := fun t τ => posDuhamelTriangle.indicator (fun p : ℝ × ℝ => bandpassFilterWeight p.1 • G p.2) (t, τ)) h_pos,
      MeasureTheory.integral_integral_swap
        (f := fun t τ => negDuhamelTriangle.indicator (fun p : ℝ × ℝ => bandpassFilterWeight p.1 • G p.2) (t, τ)) h_neg]

/-! ## 2. Annihilation of `bochnerFilteredOp H_s₀ w_BP P_deriv` -/

/-- If `Commute H_s₀ Q` and `Q * X * Q = 0`, then `Q * bochnerFilteredOp H_s₀ w_BL X * Q = 0`. -/
lemma proj_mul_bochnerFilteredOp_mul_proj_eq_zero_of_commute {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    {H_s₀ Q X : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site}
    {w_BL : ℝ → ℂ} (hHs₀ : IsSelfAdjoint H_s₀) (hw_int : Integrable w_BL)
    (h_comm : Commute H_s₀ Q) (h_diag_zero : Q * X * Q = 0) :
    Q * bochnerFilteredOp H_s₀ w_BL X * Q = 0 := by
  unfold bochnerFilteredOp
  rw [clm_sandwich_integral_smul Q Q w_BL (fun t => heisenbergFlow H_s₀ t X)
    (integrable_smul_heisenbergFlow_of_integrable hHs₀ hw_int X)]
  have h_pt : (fun t : ℝ => w_BL t • (Q * heisenbergFlow H_s₀ t X * Q)) = 0 := by
    funext t
    have hQ_flow : heisenbergFlow H_s₀ t Q = Q := heisenbergFlow_eq_self_of_commute h_comm t
    have h_conj : Q * heisenbergFlow H_s₀ t X * Q = heisenbergFlow H_s₀ t (Q * X * Q) := by
      rw [heisenbergFlow_mul, heisenbergFlow_mul, hQ_flow]
    rw [Pi.zero_apply, h_conj, h_diag_zero]
    have h_zero : heisenbergFlow H_s₀ t (0 : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site) = 0 := by
      unfold heisenbergFlow; rw [mul_zero, zero_mul]
    rw [h_zero, clm_smul_zero]
  rw [h_pt, Pi.zero_def, MeasureTheory.integral_zero]

/-- If `twoBlockOffDiagProj P_s₀ X = X` and `twoBlockOffDiagProj P_s₀ (bochnerFilteredOp H_s₀ w_BL X) = 0`,
    then `bochnerFilteredOp H_s₀ w_BL X = 0`. -/
theorem bochnerFilteredOp_eq_zero_of_twoBlockOffDiagProj_eq_self {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    {H_s₀ P_s₀ X : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site}
    {w_BL : ℝ → ℂ} (hHs₀ : IsSelfAdjoint H_s₀) (hw_int : Integrable w_BL)
    (hP_idem : P_s₀ * P_s₀ = P_s₀) (h_comm : Commute H_s₀ P_s₀)
    (hX_off : twoBlockOffDiagProj P_s₀ X = X)
    (h_filt_off : twoBlockOffDiagProj P_s₀ (bochnerFilteredOp H_s₀ w_BL X) = 0) :
    bochnerFilteredOp H_s₀ w_BL X = 0 := by
  rcases diag_blocks_twoBlockOffDiagProj_eq_zero hP_idem X with ⟨h1, h2⟩
  rw [hX_off] at h1 h2
  have h_comm_1P : Commute H_s₀ (1 - P_s₀) := (Commute.one_right H_s₀).sub_right h_comm
  have h_diag1 := proj_mul_bochnerFilteredOp_mul_proj_eq_zero_of_commute hHs₀ hw_int h_comm h1
  have h_diag2 := proj_mul_bochnerFilteredOp_mul_proj_eq_zero_of_commute hHs₀ hw_int h_comm_1P h2
  have h_diag_zero : twoBlockDiagProj P_s₀ (bochnerFilteredOp H_s₀ w_BL X) = 0 := by
    unfold twoBlockDiagProj
    rw [h_diag1, h_diag2, add_zero]
  rw [← twoBlockDiagProj_add_twoBlockOffDiagProj P_s₀ (bochnerFilteredOp H_s₀ w_BL X),
    h_diag_zero, h_filt_off, add_zero]

/-! ## 3. Kato's Differential Identity $\dot{P}(s_0) = i[\mathcal{D}(s_0), P(s_0)]$ -/

/-- Commutator with $P_{s_0}$ pulls inside the Bochner integral defining `katoHastingsGeneratorOp`. -/
lemma katoHastingsGeneratorOp_commutator_integral {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    {H_s₀ totalPerturbation P_s₀ : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site}
    {W : ℝ → ℂ} (hH : IsSelfAdjoint H_s₀) (hW_int : Integrable W MeasureTheory.volume) :
    let D_s₀ := katoHastingsGeneratorOp H_s₀ W totalPerturbation
    (Complex.I : ℂ) • (D_s₀ * P_s₀ - P_s₀ * D_s₀) =
      ∫ τ : ℝ, W τ • ((Complex.I : ℂ) •
        (heisenbergFlow H_s₀ τ totalPerturbation * P_s₀ - P_s₀ * heisenbergFlow H_s₀ τ totalPerturbation)) := by
  intro D_s₀
  let E := ManyBodyHilbertSpace Site
  let L_comm : (E →L[ℂ] E) →L[ℂ] (E →L[ℂ] E) :=
    (Complex.I : ℂ) •
      ((ContinuousLinearMap.mul ℂ (E →L[ℂ] E)).flip P_s₀ -
        ContinuousLinearMap.mul ℂ (E →L[ℂ] E) P_s₀)
  have h_int_flow : Integrable (fun τ : ℝ => W τ • heisenbergFlow H_s₀ τ totalPerturbation) :=
    integrable_smul_heisenbergFlow_of_integrable hH hW_int totalPerturbation
  have h1 : L_comm (∫ τ : ℝ, W τ • heisenbergFlow H_s₀ τ totalPerturbation) =
      ∫ τ : ℝ, L_comm (W τ • heisenbergFlow H_s₀ τ totalPerturbation) :=
    (L_comm.integral_comp_comm h_int_flow).symm
  have h2 : (fun τ : ℝ => L_comm (W τ • heisenbergFlow H_s₀ τ totalPerturbation)) =
      (fun τ : ℝ => W τ • ((Complex.I : ℂ) •
        (heisenbergFlow H_s₀ τ totalPerturbation * P_s₀ - P_s₀ * heisenbergFlow H_s₀ τ totalPerturbation))) := by
    funext τ
    exact L_comm.map_smul (W τ) (heisenbergFlow H_s₀ τ totalPerturbation)
  rw [← h2]
  exact h1

/-- **Kato's Differential Identity (`hasDerivAt_perturbedGroundSpectralProj_eq_katoGenerator_commutator`)**:
    Whenever `bhmPerturbedGap ≤ indexedSpectralGap sys V s₀` and
    `HasDerivAt (perturbedGroundSpectralProj sys V) P_deriv s₀`, the derivative $P_{\mathrm{deriv}}$
    equals the commutator $i [\mathcal{D}(s_0), P(s_0)]$ with the smooth bandpass QAC generator
    $\mathcal{D}(s_0) = \mathrm{katoHastingsGeneratorOp}\ H(s_0)\ W_{\mathrm{BP}}\ V_{\mathrm{tot}}$. -/
theorem hasDerivAt_perturbedGroundSpectralProj_eq_katoGenerator_commutator
    {D L : ℕ} [NeZero L]
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (sys : IndexedCommutingProjectorHamiltonian D L Site ι)
    (V : QuasiLocalPerturbation D L Site) (s₀ : ℝ)
    (h_gap : bhmPerturbedGap ≤ indexedSpectralGap sys V s₀)
    {P_deriv : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site}
    (hP_deriv : HasDerivAt (perturbedGroundSpectralProj sys V) P_deriv s₀) :
    let H_s₀ := sys.H0 + (scaleQuasiLocalPerturbation s₀ V).totalPerturbation
    let D_s₀ := katoHastingsGeneratorOp H_s₀ bandpassContinuationWeight V.totalPerturbation
    let P_s₀ := perturbedGroundSpectralProj sys V s₀
    P_deriv = (Complex.I : ℂ) • (D_s₀ * P_s₀ - P_s₀ * D_s₀) ∧
    HasDerivAt (perturbedGroundSpectralProj sys V)
      ((Complex.I : ℂ) • (D_s₀ * P_s₀ - P_s₀ * D_s₀)) s₀ := by
  intro H_s₀ D_s₀ P_s₀
  have hHs₀ : IsSelfAdjoint H_s₀ :=
    isSelfAdjoint_indexedH0_add_V_tot_bhm sys (scaleQuasiLocalPerturbation s₀ V)
  have hP_idem : ∀ s : ℝ,
      perturbedGroundSpectralProj sys V s * perturbedGroundSpectralProj sys V s =
        perturbedGroundSpectralProj sys V s :=
    fun s => (isStarProjection_perturbedGroundSpectralProj sys V s).isIdempotentElem.eq
  have h_comm : ∀ s : ℝ,
      Commute (sys.H0 + (s : ℂ) • V.totalPerturbation) (perturbedGroundSpectralProj sys V s) := by
    intro s
    rw [← scaleQuasiLocalPerturbation_V_tot]
    exact commute_perturbedGroundSpectralProj sys V s
  have h_H_s₀_eq : sys.H0 + (s₀ : ℂ) • V.totalPerturbation = H_s₀ := by
    dsimp [H_s₀]; rw [scaleQuasiLocalPerturbation_V_tot]
  rcases projector_deriv_eq_heisenbergFlow_add_duhamel_integral
    sys.isSelfAdjoint_H0 V.isSelfAdjoint_totalPerturbation hP_idem h_comm hP_deriv with ⟨h_off_self, h_duh_t⟩
  (try dsimp only at h_duh_t)
  rw [h_H_s₀_eq] at h_duh_t
  have h_filt_off : twoBlockOffDiagProj P_s₀ (bochnerFilteredOp H_s₀ bandpassFilterWeight P_deriv) = 0 :=
    twoBlockOffDiagProj_perturbedGroundSpectralProj_bochnerFilteredOp_eq_zero
      sys V s₀ integrable_w_BP (fun _ hω => integral_w_BP_mul_exp_eq_zero_of_abs_ge_half hω)
      h_gap P_deriv
  have h_filt_zero : bochnerFilteredOp H_s₀ bandpassFilterWeight P_deriv = 0 :=
    bochnerFilteredOp_eq_zero_of_twoBlockOffDiagProj_eq_self hHs₀ integrable_w_BP
      (hP_idem s₀) (commute_perturbedGroundSpectralProj sys V s₀) h_off_self h_filt_off
  let G : ℝ → (ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site) :=
    fun τ => (Complex.I : ℂ) •
      (heisenbergFlow H_s₀ τ V.totalPerturbation * P_s₀ - P_s₀ * heisenbergFlow H_s₀ τ V.totalPerturbation)
  have h_int_eq_sub :
      (fun t : ℝ => bandpassFilterWeight t • (∫ τ in (0 : ℝ)..t, G τ)) =
        (fun t : ℝ => bandpassFilterWeight t • P_deriv - bandpassFilterWeight t • heisenbergFlow H_s₀ t P_deriv) := by
    funext t
    have ht := h_duh_t t
    have h_sub : (∫ τ in (0 : ℝ)..t, G τ) = P_deriv - heisenbergFlow H_s₀ t P_deriv :=
      eq_sub_of_add_eq' ht.symm
    rw [h_sub, smul_sub]
  have h_lhs_eval :
      (∫ t : ℝ, bandpassFilterWeight t • (∫ τ in (0 : ℝ)..t, G τ)) = P_deriv := by
    rw [h_int_eq_sub, MeasureTheory.integral_sub (integrable_w_BP.smul_const P_deriv)
      (integrable_smul_heisenbergFlow_of_integrable hHs₀ integrable_w_BP P_deriv),
      integral_smul_const, integral_w_BP_eq_one, one_smul]
    change P_deriv - bochnerFilteredOp H_s₀ bandpassFilterWeight P_deriv = P_deriv
    rw [h_filt_zero, sub_zero]
  have hG_cont : Continuous G :=
    ((((continuous_heisenbergFlow H_s₀ V.totalPerturbation).mul continuous_const).sub
      (continuous_const.mul (continuous_heisenbergFlow H_s₀ V.totalPerturbation)))).const_smul (Complex.I : ℂ)
  have hG_bdd : ∀ τ : ℝ, ‖G τ‖ ≤ 2 * ‖V.totalPerturbation‖ * ‖P_s₀‖ := by
    intro τ
    dsimp [G]
    rw [norm_smul, Complex.norm_I, one_mul]
    calc ‖heisenbergFlow H_s₀ τ V.totalPerturbation * P_s₀ - P_s₀ * heisenbergFlow H_s₀ τ V.totalPerturbation‖
      _ ≤ 2 * ‖heisenbergFlow H_s₀ τ V.totalPerturbation‖ * ‖P_s₀‖ :=
        norm_opCommutator_le (heisenbergFlow H_s₀ τ V.totalPerturbation) P_s₀
      _ ≤ 2 * ‖V.totalPerturbation‖ * ‖P_s₀‖ :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left (norm_heisenbergFlow_le hHs₀ τ V.totalPerturbation) (by positivity))
          (norm_nonneg _)
  have h_fubini := (integrable_and_integral_w_BP_smul_intervalIntegral_eq_integral_W_BP_smul
    hG_cont (by positivity) hG_bdd).2
  have hP_eq : P_deriv = (Complex.I : ℂ) • (D_s₀ * P_s₀ - P_s₀ * D_s₀) := by
    rw [← h_lhs_eval, h_fubini,
      katoHastingsGeneratorOp_commutator_integral hHs₀ integrable_W_BP]
  exact ⟨hP_eq, hP_eq ▸ hP_deriv⟩

end
