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

import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Proofs.BandLimitedFilter.BochnerFilterSelfAdjointness
import Proofs.BandLimitedFilter.SmoothBandpassFilterKernel

/-!
# Smooth Odd Continuation Kernel and Fubini Integration by Parts

Constructs the smooth odd continuation weight `wBPContinuationWeight` (`bandpassContinuationWeight`) from tail integrals of `bandpassFilterWeight`, proving odd real symmetry (`bandpassContinuationWeight_zero`, `bandpassContinuationWeight_of_pos`, `bandpassContinuationWeight_of_neg`, `bandpassContinuationWeight_odd`, `bandpassContinuationWeight_of_pos_eq_wBPTailAntideriv`), polynomial moments, and superpolynomial tail decay. Establishes self-adjointness of the associated Kato–Hastings generator and the Fubini integration-by-parts identity.

## References

* Part I, Section 6.2 (`subsec:bochner-lr`), Equations (66)–(68) (`eq:wBP-WBP-def`, `eq:wBP-fourier-props`, `eq:wBP-WBP-ibp`)
* Hastings–Wen (2005), Physical Review B 72, 045141
* Bravyi–Hastings (2011), Communications in Mathematical Physics 307, 609–627
-/

noncomputable section

open scoped Classical InnerProduct ComplexConjugate BigOperators
open Filter Topology Asymptotics MeasureTheory Complex Real

/-!
## 1. Definition of the Continuation Weight Kernel $W_{\mathrm{BP}}$
-/

/-- The continuation weight kernel $W_{\mathrm{BP}} : \mathbb{R} \to \mathbb{C}$ associated to the
    smooth bandpass filter weight $w_{\mathrm{BP}}$, defined for $\tau > 0$ as the upper tail integral
    $\int_{[\tau, \infty)} w_{\mathrm{BP}}(t)\,dt$, extended oddly to $\tau < 0$ as
    $-\int_{[-\tau, \infty)} w_{\mathrm{BP}}(t)\,dt$, and set to $0$ at $\tau = 0$. -/
def wBPContinuationWeight (τ : ℝ) : ℂ :=
  if 0 < τ then
    ∫ t in Set.Ici τ, bandpassFilterWeight t
  else if τ < 0 then
    - (∫ t in Set.Ici (-τ), bandpassFilterWeight t)
  else
    0

/-- Standard notation alias `bandpassContinuationWeight` for the continuation weight kernel `wBPContinuationWeight`. -/
abbrev bandpassContinuationWeight : ℝ → ℂ := wBPContinuationWeight

@[simp]
lemma bandpassContinuationWeight_zero : bandpassContinuationWeight 0 = 0 := by
  simp [bandpassContinuationWeight, wBPContinuationWeight]

lemma bandpassContinuationWeight_of_pos {τ : ℝ} (hτ : 0 < τ) :
    bandpassContinuationWeight τ = ∫ t in Set.Ici τ, bandpassFilterWeight t := by
  simp [bandpassContinuationWeight, wBPContinuationWeight, hτ]

lemma bandpassContinuationWeight_of_neg {τ : ℝ} (hτ : τ < 0) :
    bandpassContinuationWeight τ = - (∫ t in Set.Ici (-τ), bandpassFilterWeight t) := by
  have h_not_pos : ¬ (0 < τ) := not_lt.mpr hτ.le
  simp [bandpassContinuationWeight, wBPContinuationWeight, h_not_pos, hτ]

/-!
## 2. Real-Valuedness and Odd Symmetry of $W_{\mathrm{BP}}$
-/

private lemma star_setIntegral_Ici_w_BP (a : ℝ) :
    star (∫ t in Set.Ici a, bandpassFilterWeight t) = ∫ t in Set.Ici a, bandpassFilterWeight t := by
  rw [Complex.star_def, ← integral_conj]
  refine integral_congr_ae (Filter.Eventually.of_forall (fun t => ?_))
  dsimp
  rw [← Complex.star_def, star_w_BP]

/-- $W_{\mathrm{BP}}(\tau)$ is real-valued for all $\tau \in \mathbb{R}$:
    $\mathrm{star}(W_{\mathrm{BP}}(\tau)) = W_{\mathrm{BP}}(\tau)$. -/
theorem star_W_BP (τ : ℝ) : star (bandpassContinuationWeight τ) = bandpassContinuationWeight τ := by
  rcases lt_trichotomy τ 0 with hneg | rfl | hpos
  · rw [bandpassContinuationWeight_of_neg hneg, star_neg, star_setIntegral_Ici_w_BP]
  · simp only [bandpassContinuationWeight_zero, star_zero]
  · rw [bandpassContinuationWeight_of_pos hpos, star_setIntegral_Ici_w_BP]

/-- $W_{\mathrm{BP}}$ is an odd function on $\mathbb{R}$: $W_{\mathrm{BP}}(-\tau) = - W_{\mathrm{BP}}(\tau)$. -/
theorem bandpassContinuationWeight_odd (τ : ℝ) : bandpassContinuationWeight (-τ) = - bandpassContinuationWeight τ := by
  rcases lt_trichotomy τ 0 with hneg | rfl | hpos
  · rw [bandpassContinuationWeight_of_pos (neg_pos.mpr hneg), bandpassContinuationWeight_of_neg hneg, neg_neg]
  · simp only [neg_zero, bandpassContinuationWeight_zero]
  · rw [bandpassContinuationWeight_of_neg (neg_lt_zero.mpr hpos), bandpassContinuationWeight_of_pos hpos, neg_neg]

/-!
## 3. Smooth Antiderivative Representation on $[0, \infty)$ and Measurability
-/

/-- Smooth extension of $\tau \mapsto \int_{[\tau, \infty)} w_{\mathrm{BP}}(t)\,dt$ to all $\tau \in \mathbb{R}$
    via $\int_{[0, \infty)} w_{\mathrm{BP}}(t)\,dt - \int_0^\tau w_{\mathrm{BP}}(t)\,dt$. -/
def wBPTailAntideriv (τ : ℝ) : ℂ :=
  (∫ t in Set.Ici (0 : ℝ), bandpassFilterWeight t) - ∫ t in (0 : ℝ)..τ, bandpassFilterWeight t

/-- For $\tau \ge 0$, `wBPTailAntideriv τ` coincides with $\int_{[\tau, \infty)} w_{\mathrm{BP}}(t)\,dt$. -/
lemma wBPTailAntideriv_eq_setIntegral_Ici {τ : ℝ} (hτ : 0 ≤ τ) :
    wBPTailAntideriv τ = ∫ t in Set.Ici τ, bandpassFilterWeight t := by
  dsimp [wBPTailAntideriv]
  rw [MeasureTheory.integral_Ici_eq_integral_Ioi, MeasureTheory.integral_Ici_eq_integral_Ioi,
    intervalIntegral.integral_of_le hτ, sub_eq_iff_eq_add']
  rw [← Set.Ioc_union_Ioi_eq_Ioi hτ]
  exact MeasureTheory.setIntegral_union Set.Ioc_disjoint_Ioi_same measurableSet_Ioi
    integrable_w_BP.integrableOn integrable_w_BP.integrableOn

lemma bandpassContinuationWeight_of_pos_eq_wBPTailAntideriv {τ : ℝ} (hτ : 0 < τ) :
    bandpassContinuationWeight τ = wBPTailAntideriv τ := by
  rw [bandpassContinuationWeight_of_pos hτ, wBPTailAntideriv_eq_setIntegral_Ici hτ.le]

/-- By the Fundamental Theorem of Calculus, `wBPTailAntideriv` has derivative $-w_{\mathrm{BP}}(\tau)$
    at every $\tau \in \mathbb{R}$. -/
lemma hasDerivAt_wBPTailAntideriv (τ : ℝ) :
    HasDerivAt wBPTailAntideriv (- bandpassFilterWeight τ) τ := by
  have h_ftc : HasDerivAt (fun x : ℝ => ∫ t in (0 : ℝ)..x, bandpassFilterWeight t) (bandpassFilterWeight τ) τ :=
    intervalIntegral.integral_hasDerivAt_right
      (wBPSchwartz.continuous.intervalIntegrable 0 τ)
      (wBPSchwartz.continuous.stronglyMeasurableAtFilter volume (𝓝 τ))
      wBPSchwartz.continuous.continuousAt
  unfold wBPTailAntideriv
  exact ((hasDerivAt_const τ _).sub h_ftc).congr_deriv (zero_sub _)

lemma continuous_wBPTailAntideriv : Continuous wBPTailAntideriv :=
  Differentiable.continuous (fun τ => (hasDerivAt_wBPTailAntideriv τ).differentiableAt)

lemma measurable_W_BP : Measurable bandpassContinuationWeight := by
  have h_eq : bandpassContinuationWeight = fun τ : ℝ =>
      if 0 < τ then wBPTailAntideriv τ
      else if τ < 0 then - wBPTailAntideriv (-τ)
      else 0 := by
    ext τ
    rcases lt_trichotomy τ 0 with hneg | rfl | hpos
    · have h_not_pos : ¬ (0 < τ) := not_lt.mpr hneg.le
      simp only [h_not_pos, ↓reduceIte, hneg, bandpassContinuationWeight_of_neg hneg,
        wBPTailAntideriv_eq_setIntegral_Ici (neg_pos.mpr hneg).le]
    · simp
    · simp only [hpos, ↓reduceIte, bandpassContinuationWeight_of_pos_eq_wBPTailAntideriv hpos]
  rw [h_eq]
  refine Measurable.ite (measurableSet_lt measurable_const measurable_id)
    continuous_wBPTailAntideriv.measurable ?_
  exact Measurable.ite (measurableSet_lt measurable_id measurable_const)
    (continuous_wBPTailAntideriv.comp continuous_neg).neg.measurable measurable_const

lemma aestronglyMeasurable_W_BP : AEStronglyMeasurable bandpassContinuationWeight volume :=
  measurable_W_BP.aestronglyMeasurable

/-!
## 4. Pointwise Tail Bound and Rapid Polynomial Decay of $W_{\mathrm{BP}}$
-/

private lemma norm_setIntegral_Ici_w_BP_le_tail {r : ℝ} (_hr : 0 ≤ r) :
    ‖∫ t in Set.Ici r, bandpassFilterWeight t‖ ≤ ∫ t in {t : ℝ | r ≤ |t|}, ‖bandpassFilterWeight t‖ := by
  refine (norm_integral_le_integral_norm _).trans ?_
  refine setIntegral_mono_set integrable_norm_w_BP.integrableOn
    (Filter.Eventually.of_forall (fun t => norm_nonneg (bandpassFilterWeight t)))
    (Filter.Eventually.of_forall (fun t (ht : r ≤ t) => le_trans ht (le_abs_self t)))

lemma norm_wBPTailAntideriv_le_tail {τ : ℝ} (hτ : 0 ≤ τ) :
    ‖wBPTailAntideriv τ‖ ≤ ∫ t in {t : ℝ | τ ≤ |t|}, ‖bandpassFilterWeight t‖ := by
  rw [wBPTailAntideriv_eq_setIntegral_Ici hτ]
  exact norm_setIntegral_Ici_w_BP_le_tail hτ

lemma pow_mul_norm_wBPTailAntideriv_le (k : ℕ) {τ : ℝ} (hτ : 0 ≤ τ) :
    τ ^ k * ‖wBPTailAntideriv τ‖ ≤ ∫ t : ℝ, ‖bandpassFilterWeight t‖ * |t| ^ k := by
  calc τ ^ k * ‖wBPTailAntideriv τ‖
    _ ≤ τ ^ k * (∫ t in {t : ℝ | τ ≤ |t|}, ‖bandpassFilterWeight t‖) :=
        mul_le_mul_of_nonneg_left (norm_wBPTailAntideriv_le_tail hτ) (pow_nonneg hτ k)
    _ = τ ^ k * (∫ t in {t : ℝ | τ ≤ |t|}, ‖bandpassFilterWeight t‖ * |t| ^ 0) := by
        simp only [pow_zero, mul_one]
    _ ≤ ∫ t : ℝ, ‖bandpassFilterWeight t‖ * |t| ^ (0 + k) :=
        pow_mul_tail_integral_norm_w_BP_mul_abs_pow_le 0 k hτ
    _ = ∫ t : ℝ, ‖bandpassFilterWeight t‖ * |t| ^ k := by rw [zero_add]

/-- Pointwise tail bound: $\|W_{\mathrm{BP}}(\tau)\| \le \int_{|t| \ge |\tau|} \|w_{\mathrm{BP}}(t)\|\,dt$. -/
theorem norm_W_BP_le_tail_w_BP (τ : ℝ) :
    ‖bandpassContinuationWeight τ‖ ≤ ∫ t in {t : ℝ | |τ| ≤ |t|}, ‖bandpassFilterWeight t‖ := by
  rcases lt_trichotomy τ 0 with hneg | rfl | hpos
  · rw [bandpassContinuationWeight_of_neg hneg, norm_neg, abs_of_neg hneg]
    exact norm_setIntegral_Ici_w_BP_le_tail (neg_pos.mpr hneg).le
  · rw [bandpassContinuationWeight_zero, norm_zero]
    exact setIntegral_nonneg (isClosed_le continuous_const continuous_abs |>.measurableSet)
      (fun t _ => norm_nonneg (bandpassFilterWeight t))
  · rw [bandpassContinuationWeight_of_pos hpos, abs_of_pos hpos]
    exact norm_setIntegral_Ici_w_BP_le_tail hpos.le

/-- Rapid polynomial decay of $W_{\mathrm{BP}}$: for every $k \in \mathbb{N}$ and $\tau \in \mathbb{R}$,
    $|\tau|^k \|W_{\mathrm{BP}}(\tau)\| \le \int_{\mathbb{R}} \|w_{\mathrm{BP}}(t)\| |t|^k\,dt$. -/
theorem abs_pow_mul_norm_W_BP_le (k : ℕ) (τ : ℝ) :
    |τ| ^ k * ‖bandpassContinuationWeight τ‖ ≤ ∫ t : ℝ, ‖bandpassFilterWeight t‖ * |t| ^ k := by
  calc |τ| ^ k * ‖bandpassContinuationWeight τ‖
    _ ≤ |τ| ^ k * (∫ t in {t : ℝ | |τ| ≤ |t|}, ‖bandpassFilterWeight t‖) :=
        mul_le_mul_of_nonneg_left (norm_W_BP_le_tail_w_BP τ) (pow_nonneg (abs_nonneg τ) k)
    _ = |τ| ^ k * (∫ t in {t : ℝ | |τ| ≤ |t|}, ‖bandpassFilterWeight t‖ * |t| ^ 0) := by
        simp only [pow_zero, mul_one]
    _ ≤ ∫ t : ℝ, ‖bandpassFilterWeight t‖ * |t| ^ (0 + k) :=
        pow_mul_tail_integral_norm_w_BP_mul_abs_pow_le 0 k (abs_nonneg τ)
    _ = ∫ t : ℝ, ‖bandpassFilterWeight t‖ * |t| ^ k := by rw [zero_add]

/-!
## 5. Integrability, Polynomial Moments, and Superpolynomial Tail Decay of $W_{\mathrm{BP}}$
-/

/-- Every polynomial moment $\tau \mapsto \|W_{\mathrm{BP}}(\tau)\| |\tau|^m$ is integrable on $\mathbb{R}$. -/
theorem integrable_norm_W_BP_mul_abs_pow (m : ℕ) :
    Integrable (fun τ : ℝ => ‖bandpassContinuationWeight τ‖ * |τ| ^ m) := by
  let M0 : ℝ := ∫ t : ℝ, ‖bandpassFilterWeight t‖ * |t| ^ m
  let M2 : ℝ := ∫ t : ℝ, ‖bandpassFilterWeight t‖ * |t| ^ (m + 2)
  have h_dom : Integrable (fun τ : ℝ => (M0 + M2) * (1 + τ ^ 2)⁻¹) :=
    integrable_inv_one_add_sq.const_mul (M0 + M2)
  refine h_dom.mono'
    (aestronglyMeasurable_W_BP.norm.mul (continuous_abs.pow m).aestronglyMeasurable)
    (Filter.Eventually.of_forall (fun τ => ?_))
  rw [Real.norm_of_nonneg (by positivity)]
  have h_pos : 0 < 1 + τ ^ 2 := by positivity
  have h_prod : (1 + τ ^ 2) * (‖bandpassContinuationWeight τ‖ * |τ| ^ m) ≤ M0 + M2 := by
    have h1 : |τ| ^ m * ‖bandpassContinuationWeight τ‖ ≤ M0 := abs_pow_mul_norm_W_BP_le m τ
    have h2 : |τ| ^ (m + 2) * ‖bandpassContinuationWeight τ‖ ≤ M2 := abs_pow_mul_norm_W_BP_le (m + 2) τ
    have h_id : (1 + τ ^ 2) * (‖bandpassContinuationWeight τ‖ * |τ| ^ m) =
        |τ| ^ m * ‖bandpassContinuationWeight τ‖ + |τ| ^ (m + 2) * ‖bandpassContinuationWeight τ‖ := by
      rw [ ← sq_abs τ, pow_add ]
      ring
    linarith
  calc ‖bandpassContinuationWeight τ‖ * |τ| ^ m
    _ = (1 + τ ^ 2)⁻¹ * ((1 + τ ^ 2) * (‖bandpassContinuationWeight τ‖ * |τ| ^ m)) := by
        rw [inv_mul_cancel_left₀ h_pos.ne']
    _ ≤ (1 + τ ^ 2)⁻¹ * (M0 + M2) :=
        mul_le_mul_of_nonneg_left h_prod (inv_nonneg.mpr h_pos.le)
    _ = (M0 + M2) * (1 + τ ^ 2)⁻¹ := mul_comm _ _

/-- $\|W_{\mathrm{BP}}(\cdot)\| : \mathbb{R} \to \mathbb{R}$ is integrable on $\mathbb{R}$. -/
theorem integrable_norm_W_BP : Integrable (fun τ : ℝ => ‖bandpassContinuationWeight τ‖) := by
  simpa only [pow_zero, mul_one] using integrable_norm_W_BP_mul_abs_pow 0

/-- $W_{\mathrm{BP}} : \mathbb{R} \to \mathbb{C}$ is Bochner integrable on $\mathbb{R}$. -/
theorem integrable_W_BP : Integrable bandpassContinuationWeight :=
  (integrable_norm_iff aestronglyMeasurable_W_BP).mp integrable_norm_W_BP

/-- First absolute moment $\tau \mapsto \|W_{\mathrm{BP}}(\tau)\| |\tau|$ is integrable on $\mathbb{R}$. -/
theorem integrable_norm_W_BP_mul_abs :
    Integrable (fun τ : ℝ => ‖bandpassContinuationWeight τ‖ * |τ|) := by
  simpa only [pow_one] using integrable_norm_W_BP_mul_abs_pow 1

/-- Markov tail inequality for the $m$-th polynomial moment of $W_{\mathrm{BP}}$. -/
lemma pow_mul_tail_integral_norm_W_BP_mul_abs_pow_le (m k : ℕ) {R : ℝ} (hR : 0 ≤ R) :
    R ^ k * (∫ τ in {τ : ℝ | R ≤ |τ|}, ‖bandpassContinuationWeight τ‖ * |τ| ^ m) ≤
      ∫ τ : ℝ, ‖bandpassContinuationWeight τ‖ * |τ| ^ (m + k) := by
  let S : Set ℝ := {τ : ℝ | R ≤ |τ|}
  have hS : MeasurableSet S := isClosed_le continuous_const continuous_abs |>.measurableSet
  rw [← integral_const_mul]
  have h_mono : ∫ τ in S, R ^ k * (‖bandpassContinuationWeight τ‖ * |τ| ^ m) ≤
      ∫ τ in S, ‖bandpassContinuationWeight τ‖ * |τ| ^ (m + k) := by
    refine setIntegral_mono_on
      ((integrable_norm_W_BP_mul_abs_pow m).const_mul (R ^ k)).integrableOn
      (integrable_norm_W_BP_mul_abs_pow (m + k)).integrableOn hS (fun τ hτ => ?_)
    have hpow : R ^ k ≤ |τ| ^ k := pow_le_pow_left₀ hR hτ k
    have hnonneg : 0 ≤ ‖bandpassContinuationWeight τ‖ * |τ| ^ m := by positivity
    calc R ^ k * (‖bandpassContinuationWeight τ‖ * |τ| ^ m)
      _ = (‖bandpassContinuationWeight τ‖ * |τ| ^ m) * R ^ k := mul_comm _ _
      _ ≤ (‖bandpassContinuationWeight τ‖ * |τ| ^ m) * |τ| ^ k := mul_le_mul_of_nonneg_left hpow hnonneg
      _ = ‖bandpassContinuationWeight τ‖ * |τ| ^ (m + k) := by rw [pow_add, mul_assoc]
  exact h_mono.trans (setIntegral_le_integral (integrable_norm_W_BP_mul_abs_pow (m + k))
    (Filter.Eventually.of_forall (fun τ => by positivity)))

/-- For any $m \in \mathbb{N}$ and $c > 0$, the tail integral
    $j \mapsto \int_{|\tau| \ge c j} \|W_{\mathrm{BP}}(\tau)\| |\tau|^m\,d\tau$
    belongs to `IsSuperpolynomialDecay`. -/
theorem isSuperpolynomialDecay_tail_integral_norm_W_BP_mul_abs_pow
    (m : ℕ) {c : ℝ} (hc : 0 < c) :
    IsSuperpolynomialDecay
      (fun j : ℕ => ∫ τ in {τ : ℝ | c * (j : ℝ) ≤ |τ|}, ‖bandpassContinuationWeight τ‖ * |τ| ^ m) := by
  refine ⟨fun j => setIntegral_nonneg
    (isClosed_le continuous_const continuous_abs |>.measurableSet)
    (fun τ _ => by positivity), fun n => ?_⟩
  let M : ℝ := ∫ τ : ℝ, ‖bandpassContinuationWeight τ‖ * |τ| ^ (m + (n + 1))
  let C : ℝ := M / c ^ (n + 1)
  have h_zero : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 0) := tendsto_const_nhds
  have h_upper : Tendsto (fun j : ℕ => C * (j : ℝ)⁻¹) atTop (𝓝 0) := by
    simpa only [mul_zero, Function.comp_def] using
      (tendsto_const_nhds (x := C)).mul (tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop)
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' h_zero h_upper
    (Filter.Eventually.of_forall (fun j => mul_nonneg (pow_nonneg (Nat.cast_nonneg j) n)
      (setIntegral_nonneg (isClosed_le continuous_const continuous_abs |>.measurableSet)
        (fun τ _ => by positivity)))) ?_
  filter_upwards [Filter.eventually_ge_atTop 1] with j hj
  have hj_pos : (0 : ℝ) < (j : ℝ) := Nat.cast_pos.mpr (Nat.succ_le_iff.mp hj)
  have hc_pow_pos : 0 < c ^ (n + 1) := pow_pos hc (n + 1)
  have h_markov := pow_mul_tail_integral_norm_W_BP_mul_abs_pow_le m (n + 1)
    (mul_nonneg hc.le (Nat.cast_nonneg j))
  set I_j : ℝ := ∫ τ in {τ : ℝ | c * (j : ℝ) ≤ |τ|}, ‖bandpassContinuationWeight τ‖ * |τ| ^ m
  have h_prod : c ^ (n + 1) * (j : ℝ) * ((j : ℝ) ^ n * I_j) ≤ M := by
    calc c ^ (n + 1) * (j : ℝ) * ((j : ℝ) ^ n * I_j)
      _ = (c * (j : ℝ)) ^ (n + 1) * I_j := by
          rw [mul_pow, pow_succ]
          ring
      _ ≤ M := h_markov
  calc (j : ℝ) ^ n * I_j
    _ = (c ^ (n + 1) * (j : ℝ))⁻¹ * (c ^ (n + 1) * (j : ℝ) * ((j : ℝ) ^ n * I_j)) := by
        rw [inv_mul_cancel_left₀ (mul_ne_zero hc_pow_pos.ne' hj_pos.ne')]
    _ ≤ (c ^ (n + 1) * (j : ℝ))⁻¹ * M :=
        mul_le_mul_of_nonneg_left h_prod
          (inv_nonneg.mpr (mul_nonneg hc_pow_pos.le hj_pos.le))
    _ = C * (j : ℝ)⁻¹ := by
        dsimp [C]
        rw [mul_inv, div_eq_mul_inv]
        ring

/-- For any $c > 0$, the continuation-weight tail integral
    $j \mapsto \int_{|\tau| \ge c j} \|W_{\mathrm{BP}}(\tau)\|\,d\tau$
    belongs to `IsSuperpolynomialDecay`. -/
theorem isSuperpolynomialDecay_tail_integral_norm_W_BP {c : ℝ} (hc : 0 < c) :
    IsSuperpolynomialDecay
      (fun j : ℕ => ∫ τ in {τ : ℝ | c * (j : ℝ) ≤ |τ|}, ‖bandpassContinuationWeight τ‖) := by
  simpa only [pow_zero, mul_one] using
    isSuperpolynomialDecay_tail_integral_norm_W_BP_mul_abs_pow 0 hc

/-- For any $c > 0$, the first-moment continuation-weight tail integral
    $j \mapsto \int_{|\tau| \ge c j} \|W_{\mathrm{BP}}(\tau)\| |\tau|\,d\tau$
    belongs to `IsSuperpolynomialDecay`. -/
theorem isSuperpolynomialDecay_tail_integral_norm_W_BP_mul_abs {c : ℝ} (hc : 0 < c) :
    IsSuperpolynomialDecay
      (fun j : ℕ => ∫ τ in {τ : ℝ | c * (j : ℝ) ≤ |τ|}, ‖bandpassContinuationWeight τ‖ * |τ|) := by
  simpa only [pow_one] using
    isSuperpolynomialDecay_tail_integral_norm_W_BP_mul_abs_pow 1 hc

/-!
## 6. Self-Adjointness of the Kato–Hastings Generator $\mathcal{D}_{W_{\mathrm{BP}}}^{H'}(V)$
-/

/-- Because $W_{\mathrm{BP}}$ is real-valued ($\mathrm{star}(W_{\mathrm{BP}}(\tau)) = W_{\mathrm{BP}}(\tau)$),
    the Kato–Hastings generator $\mathcal{D}_{W_{\mathrm{BP}}}^{H'}(V)$ is self-adjoint whenever
    $H'$ and $V$ are self-adjoint. -/
theorem isSelfAdjoint_katoHastingsGeneratorOp_W_BP {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    {H' V : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site}
    (hH' : IsSelfAdjoint H') (hV : IsSelfAdjoint V) :
    IsSelfAdjoint (katoHastingsGeneratorOp H' bandpassContinuationWeight V) :=
  isSelfAdjoint_bochnerFilteredOp hH' hV star_W_BP

/-!
## 7. Fubini / Integration-by-Parts Identity Relating $w_{\mathrm{BP}}$ and $W_{\mathrm{BP}}$
-/

private lemma integrable_w_BP_smul_intervalIntegral
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (G : ℝ → E) (hG_cont : Continuous G)
    (C_G : ℝ) (hG_bound : ∀ τ : ℝ, ‖G τ‖ ≤ C_G) :
    Integrable (fun t : ℝ => bandpassFilterWeight t • (∫ τ in (0 : ℝ)..t, G τ)) := by
  let C' : ℝ := max C_G 0
  have h_cont : Continuous (fun t : ℝ => bandpassFilterWeight t • (∫ τ in (0 : ℝ)..t, G τ)) :=
    wBPSchwartz.continuous.smul
      (intervalIntegral.continuous_primitive (fun a b => hG_cont.intervalIntegrable a b) 0)
  refine (integrable_norm_w_BP_mul_abs.const_mul C').mono' h_cont.aestronglyMeasurable
    (Filter.Eventually.of_forall (fun t => ?_))
  rw [norm_smul]
  have h_int_le : ‖∫ τ in (0 : ℝ)..t, G τ‖ ≤ C' * |t - 0| :=
    intervalIntegral.norm_integral_le_of_norm_le_const
      (fun τ _ => (hG_bound τ).trans (le_max_left C_G 0))
  rw [sub_zero] at h_int_le
  calc ‖bandpassFilterWeight t‖ * ‖∫ τ in (0 : ℝ)..t, G τ‖
    _ ≤ ‖bandpassFilterWeight t‖ * (C' * |t|) := mul_le_mul_of_nonneg_left h_int_le (norm_nonneg _)
    _ = C' * (‖bandpassFilterWeight t‖ * |t|) := by ring

private lemma integrable_W_BP_smul_of_bounded
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (G : ℝ → E) (hG_cont : Continuous G)
    (C_G : ℝ) (hG_bound : ∀ τ : ℝ, ‖G τ‖ ≤ C_G) :
    Integrable (fun τ : ℝ => bandpassContinuationWeight τ • G τ) := by
  let C' : ℝ := max C_G 0
  refine (integrable_norm_W_BP.const_mul C').mono'
    (aestronglyMeasurable_W_BP.smul hG_cont.aestronglyMeasurable)
    (Filter.Eventually.of_forall (fun τ => ?_))
  rw [norm_smul, mul_comm]
  exact mul_le_mul_of_nonneg_right ((hG_bound τ).trans (le_max_left C_G 0)) (norm_nonneg _)

private lemma integrableOn_Ioi_wBPTailAntideriv_smul_of_bounded
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (G : ℝ → E) (hG_cont : Continuous G)
    (C_G : ℝ) (hG_bound : ∀ τ : ℝ, ‖G τ‖ ≤ C_G) :
    IntegrableOn (fun τ : ℝ => wBPTailAntideriv τ • G τ) (Set.Ioi (0 : ℝ)) volume := by
  refine (integrable_W_BP_smul_of_bounded G hG_cont C_G hG_bound).integrableOn.congr_fun
    (fun τ hτ => ?_) measurableSet_Ioi
  change bandpassContinuationWeight τ • G τ = wBPTailAntideriv τ • G τ
  rw [bandpassContinuationWeight_of_pos_eq_wBPTailAntideriv hτ]

/-- Half-line integration-by-parts identity on $(0, \infty)$:
    $\int_{(0, \infty)} w_{\mathrm{BP}}(t) \int_0^t G(\tau)\,d\tau\,dt = \int_{(0, \infty)} W_{\mathrm{BP}}(\tau) G(\tau)\,d\tau$. -/
lemma setIntegral_Ioi_w_BP_smul_intervalIntegral_eq
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    (G : ℝ → E) (hG_cont : Continuous G)
    (C_G : ℝ) (hG_bound : ∀ τ : ℝ, ‖G τ‖ ≤ C_G) :
    (∫ t in Set.Ioi (0 : ℝ), bandpassFilterWeight t • (∫ τ in (0 : ℝ)..t, G τ)) =
      ∫ τ in Set.Ioi (0 : ℝ), bandpassContinuationWeight τ • G τ := by
  let Φ : ℝ → E := fun t => - (wBPTailAntideriv t • ∫ τ in (0 : ℝ)..t, G τ)
  let f' : ℝ → E := fun t => bandpassFilterWeight t • (∫ τ in (0 : ℝ)..t, G τ) - wBPTailAntideriv t • G t
  have hΦ0 : Φ 0 = 0 := by
    simp [Φ, intervalIntegral.integral_same]
  have h_deriv : ∀ t ∈ Set.Ici (0 : ℝ), HasDerivAt Φ (f' t) t := by
    intro t _
    have h1 := hasDerivAt_wBPTailAntideriv t
    have h2 : HasDerivAt (fun x : ℝ => ∫ τ in (0 : ℝ)..x, G τ) (G t) t :=
      intervalIntegral.integral_hasDerivAt_right
        (hG_cont.intervalIntegrable 0 t)
        (hG_cont.stronglyMeasurableAtFilter volume (𝓝 t))
        hG_cont.continuousAt
    have h_prod := (h1.smul h2).neg
    refine h_prod.congr_deriv ?_
    dsimp [f']
    rw [neg_smul]
    abel
  have h_tendsto : Tendsto Φ atTop (𝓝 (0 : E)) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    let C' : ℝ := max C_G 0
    let M2 : ℝ := ∫ s : ℝ, ‖bandpassFilterWeight s‖ * |s| ^ 2
    have h_upper : Tendsto (fun t : ℝ => (C' * M2) * t⁻¹) atTop (𝓝 0) := by
      simpa only [mul_zero] using (tendsto_const_nhds (x := C' * M2)).mul tendsto_inv_atTop_zero
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds h_upper
      (Filter.Eventually.of_forall (fun t => norm_nonneg (Φ t))) ?_
    filter_upwards [Filter.eventually_ge_atTop (1 : ℝ)] with t ht
    have ht_pos : 0 < t := lt_of_lt_of_le zero_lt_one ht
    have h_int_le : ‖∫ τ in (0 : ℝ)..t, G τ‖ ≤ C' * t := by
      have h : ‖∫ τ in (0 : ℝ)..t, G τ‖ ≤ C' * |t - 0| :=
        intervalIntegral.norm_integral_le_of_norm_le_const
          (fun τ _ => (hG_bound τ).trans (le_max_left C_G 0))
      simpa only [sub_zero, abs_of_pos ht_pos] using h
    have h_tail : t ^ 2 * ‖wBPTailAntideriv t‖ ≤ M2 :=
      pow_mul_norm_wBPTailAntideriv_le 2 ht_pos.le
    have h_prod : t * ‖Φ t‖ ≤ C' * M2 := by
      calc t * ‖Φ t‖
        _ = t * (‖wBPTailAntideriv t‖ * ‖∫ τ in (0 : ℝ)..t, G τ‖) := by
            simp only [Φ, norm_neg, norm_smul]
        _ ≤ t * (‖wBPTailAntideriv t‖ * (C' * t)) :=
            mul_le_mul_of_nonneg_left
              (mul_le_mul_of_nonneg_left h_int_le (norm_nonneg _)) ht_pos.le
        _ = C' * (t ^ 2 * ‖wBPTailAntideriv t‖) := by ring
        _ ≤ C' * M2 := mul_le_mul_of_nonneg_left h_tail (le_max_right C_G 0)
    calc ‖Φ t‖
      _ = t⁻¹ * (t * ‖Φ t‖) := by rw [inv_mul_cancel_left₀ ht_pos.ne']
      _ ≤ t⁻¹ * (C' * M2) := mul_le_mul_of_nonneg_left h_prod (inv_nonneg.mpr ht_pos.le)
      _ = (C' * M2) * t⁻¹ := mul_comm _ _
  have h_int1 : IntegrableOn (fun t : ℝ => bandpassFilterWeight t • (∫ τ in (0 : ℝ)..t, G τ))
      (Set.Ioi (0 : ℝ)) volume :=
    (integrable_w_BP_smul_intervalIntegral G hG_cont C_G hG_bound).integrableOn
  have h_int2 : IntegrableOn (fun τ : ℝ => wBPTailAntideriv τ • G τ)
      (Set.Ioi (0 : ℝ)) volume :=
    integrableOn_Ioi_wBPTailAntideriv_smul_of_bounded G hG_cont C_G hG_bound
  have h_ftc := integral_Ioi_of_hasDerivAt_of_tendsto' h_deriv (h_int1.sub h_int2) h_tendsto
  rw [hΦ0, sub_zero] at h_ftc
  have h_sub : (∫ t in Set.Ioi (0 : ℝ), f' t) =
      (∫ t in Set.Ioi (0 : ℝ), bandpassFilterWeight t • (∫ τ in (0 : ℝ)..t, G τ)) -
        ∫ τ in Set.Ioi (0 : ℝ), wBPTailAntideriv τ • G τ :=
    integral_sub h_int1 h_int2
  have h_eq : (∫ t in Set.Ioi (0 : ℝ), bandpassFilterWeight t • (∫ τ in (0 : ℝ)..t, G τ)) =
      ∫ τ in Set.Ioi (0 : ℝ), wBPTailAntideriv τ • G τ :=
    sub_eq_zero.mp (h_sub.symm.trans h_ftc)
  rw [h_eq]
  refine setIntegral_congr_fun measurableSet_Ioi (fun τ hτ => ?_)
  rw [bandpassContinuationWeight_of_pos_eq_wBPTailAntideriv hτ]

/-- **Fubini / Integration-by-Parts Identity Relating $w_{\mathrm{BP}}$ and $W_{\mathrm{BP}}$**:
    For any Banach space $E$, continuous map $G : \mathbb{R} \to E$, and uniform bound
    $\forall \tau,\ \|G(\tau)\| \le C_G$,
    $$\int_{\mathbb{R}} w_{\mathrm{BP}}(t) \cdot \left(\int_0^t G(\tau)\,d\tau\right) dt
      = \int_{\mathbb{R}} W_{\mathrm{BP}}(\tau) \cdot G(\tau)\,d\tau.$$ -/
theorem integral_w_BP_smul_intervalIntegral_eq_integral_W_BP_smul
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    (G : ℝ → E) (hG_cont : Continuous G)
    (C_G : ℝ) (hG_bound : ∀ τ : ℝ, ‖G τ‖ ≤ C_G) :
    (∫ t : ℝ, bandpassFilterWeight t • (∫ τ in (0 : ℝ)..t, G τ)) =
      ∫ τ : ℝ, bandpassContinuationWeight τ • G τ := by
  have h_int_lhs := integrable_w_BP_smul_intervalIntegral G hG_cont C_G hG_bound
  have h_int_rhs := integrable_W_BP_smul_of_bounded G hG_cont C_G hG_bound
  have h_pos := setIntegral_Ioi_w_BP_smul_intervalIntegral_eq G hG_cont C_G hG_bound
  have h_neg_G := setIntegral_Ioi_w_BP_smul_intervalIntegral_eq
    (fun τ : ℝ => - G (-τ))
    (hG_cont.comp continuous_neg).neg
    C_G (fun τ => by simpa only [norm_neg] using hG_bound (-τ))
  have h_ic : (∫ t in Set.Iic (0 : ℝ), bandpassFilterWeight t • (∫ τ in (0 : ℝ)..t, G τ)) =
      ∫ τ in Set.Iic (0 : ℝ), bandpassContinuationWeight τ • G τ := by
    have h1 := integral_comp_neg_Ioi (0 : ℝ)
      (fun t : ℝ => bandpassFilterWeight t • (∫ τ in (0 : ℝ)..t, G τ))
    have h2 := integral_comp_neg_Ioi (0 : ℝ)
      (fun τ : ℝ => bandpassContinuationWeight τ • G τ)
    simp only [neg_zero] at h1 h2
    rw [← h1, ← h2]
    have h_lhs_eq : (∫ t in Set.Ioi (0 : ℝ), bandpassFilterWeight (-t) • (∫ τ in (0 : ℝ)..(-t), G τ)) =
        ∫ t in Set.Ioi (0 : ℝ), bandpassFilterWeight t • (∫ τ in (0 : ℝ)..t, - G (-τ)) := by
      refine setIntegral_congr_fun measurableSet_Ioi (fun t _ => ?_)
      rw [w_BP_even t]
      congr 1
      rw [intervalIntegral.integral_neg, intervalIntegral.integral_comp_neg,
        neg_zero, intervalIntegral.integral_symm]
    have h_rhs_eq : (∫ τ in Set.Ioi (0 : ℝ), bandpassContinuationWeight τ • - G (-τ)) =
        ∫ τ in Set.Ioi (0 : ℝ), bandpassContinuationWeight (-τ) • G (-τ) := by
      refine setIntegral_congr_fun measurableSet_Ioi (fun τ _ => ?_)
      rw [bandpassContinuationWeight_odd τ, smul_neg, neg_smul]
    exact h_lhs_eq.trans (h_neg_G.trans h_rhs_eq)
  rw [← MeasureTheory.setIntegral_univ (f := fun t : ℝ => bandpassFilterWeight t • (∫ τ in (0 : ℝ)..t, G τ)),
    ← MeasureTheory.setIntegral_univ (f := fun τ : ℝ => bandpassContinuationWeight τ • G τ),
    ← Set.Iic_union_Ioi (a := (0 : ℝ)),
    MeasureTheory.setIntegral_union (Set.Iic_disjoint_Ioi le_rfl) measurableSet_Ioi
      h_int_lhs.integrableOn h_int_lhs.integrableOn,
    MeasureTheory.setIntegral_union (Set.Iic_disjoint_Ioi le_rfl) measurableSet_Ioi
      h_int_rhs.integrableOn h_int_rhs.integrableOn,
    h_ic, h_pos]

end
