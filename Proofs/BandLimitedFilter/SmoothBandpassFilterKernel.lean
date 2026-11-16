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

import Defs.FlowAndFilter
import Defs.SuperpolyDecay
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
import Proofs.LiebRobinson.SuperpolyDecayClosure

/-!
# Schwartz-Class Smooth Bandpass Filter Weight Construction

Constructs the Schwartz-space time-domain bandpass filter `wBP` (`bandpassFilterWeight`) as the Fourier transform of a smooth compactly supported frequency bump `bumpFreq` (`wBPFreq`). Establishes `IsSmoothBandpassFilterWeight` and `smooth_bandpass_filter_weight_exists`, proving unit integral, even real symmetry, exact Fourier vanishing for frequencies of magnitude at least one-half, and superpolynomial tail decay.

## References

* Part I, Section 6.2 (`subsec:bochner-lr`), Equations (65)–(67) (`eq:bump-freq-def`, `eq:wBP-WBP-def`, `eq:wBP-fourier-props`)
* Bravyi–Hastings (2011), Communications in Mathematical Physics 307, 609–627
-/

noncomputable section

open scoped Classical InnerProduct ComplexConjugate BigOperators FourierTransform
open Filter Topology Asymptotics MeasureTheory Complex Real SchwartzMap

/-!
## 1. Frequency-Space Smooth Bump Function and Schwartz Lift
-/

/-- Smooth radial bump function on frequency space $\mathbb{R}$ centered at $0$ with inner radius
    $r_{\mathrm{in}} = 1 / (8\pi)$ (where the bump equals $1$) and outer support radius
    $r_{\mathrm{out}} = 1 / (4\pi)$ (outside which the bump vanishes identically). -/
def bumpFreq : ContDiffBump (0 : ℝ) where
  rIn := 1 / (8 * Real.pi)
  rOut := 1 / (4 * Real.pi)
  rIn_pos := by positivity
  rIn_lt_rOut := by
    have hpi : 0 < Real.pi := Real.pi_pos
    exact one_div_lt_one_div_of_lt (by positivity) (by linarith)

/-- Complex-valued frequency profile $\widehat{w}_{\mathrm{BP}}(\xi) := (\mathrm{bumpFreq}(\xi) : \mathbb{C})$. -/
def wBPFreq (ξ : ℝ) : ℂ := ((bumpFreq ξ : ℝ) : ℂ)

@[simp]
lemma wBPFreq_apply (ξ : ℝ) : wBPFreq ξ = ((bumpFreq ξ : ℝ) : ℂ) := rfl

/-- $\widehat{w}_{\mathrm{BP}}$ is an even function of frequency $\xi$. -/
lemma wBPFreq_neg (ξ : ℝ) : wBPFreq (-ξ) = wBPFreq ξ := by
  simp only [wBPFreq, bumpFreq.neg]

/-- $\widehat{w}_{\mathrm{BP}}(0) = 1$. -/
@[simp]
lemma wBPFreq_zero : wBPFreq 0 = 1 := by
  simp only [wBPFreq]
  have h1 : bumpFreq 0 = 1 :=
    bumpFreq.one_of_mem_closedBall (Metric.mem_closedBall_self bumpFreq.rIn_pos.le)
  rw [h1, Complex.ofReal_one]

/-- $\widehat{w}_{\mathrm{BP}}(\xi) = 0$ whenever $|\xi| \ge 1 / (4\pi)$. -/
lemma wBPFreq_eq_zero_of_le_abs {ξ : ℝ} (hξ : 1 / (4 * Real.pi) ≤ |ξ|) :
    wBPFreq ξ = 0 := by
  simp only [wBPFreq]
  have hdist : bumpFreq.rOut ≤ dist ξ 0 := by
    simpa [bumpFreq, Real.dist_eq] using hξ
  rw [bumpFreq.zero_of_le_dist hdist, Complex.ofReal_zero]

/-- $\widehat{w}_{\mathrm{BP}}$ is $C^\infty$ smooth on $\mathbb{R}$. -/
lemma contDiff_wBPFreq : ContDiff ℝ (⊤ : ℕ∞) wBPFreq :=
  Complex.ofRealCLM.contDiff.comp bumpFreq.contDiff

/-- $\widehat{w}_{\mathrm{BP}}$ has compact support on $\mathbb{R}$. -/
lemma hasCompactSupport_wBPFreq : HasCompactSupport wBPFreq :=
  bumpFreq.hasCompactSupport.comp_left Complex.ofReal_zero

/-- The frequency profile $\widehat{w}_{\mathrm{BP}}$ lifted to the Schwartz space $\mathcal{S}(\mathbb{R}, \mathbb{C})$. -/
def wBPFreqSchwartz : 𝓢(ℝ, ℂ) :=
  hasCompactSupport_wBPFreq.toSchwartzMap contDiff_wBPFreq

@[simp]
lemma wBPFreqSchwartz_apply (ξ : ℝ) : wBPFreqSchwartz ξ = wBPFreq ξ :=
  HasCompactSupport.toSchwartzMap_toFun hasCompactSupport_wBPFreq contDiff_wBPFreq ξ

@[simp]
lemma coe_wBPFreqSchwartz : (wBPFreqSchwartz : ℝ → ℂ) = wBPFreq := by
  ext ξ
  exact wBPFreqSchwartz_apply ξ

/-!
## 2. Time-Domain Smooth Bandpass Filter Kernel $w_{\mathrm{BP}}$
-/

/-- The smooth bandpass filter kernel in Schwartz space $\mathcal{S}(\mathbb{R}, \mathbb{C})$,
    defined as the Schwartz Fourier transform $\mathcal{F}(\widehat{w}_{\mathrm{BP}})$. -/
def wBPSchwartz : 𝓢(ℝ, ℂ) := 𝓕 wBPFreqSchwartz

/-- The smooth bandpass filter weight $w_{\mathrm{BP}} : \mathbb{R} \to \mathbb{C}$. -/
def wBP (t : ℝ) : ℂ := wBPSchwartz t

/-- Standard notation alias `bandpassFilterWeight` for the smooth bandpass filter weight `wBP`. -/
abbrev bandpassFilterWeight : ℝ → ℂ := wBP

@[simp]
lemma wBPSchwartz_apply (t : ℝ) : wBPSchwartz t = bandpassFilterWeight t := rfl

@[simp]
lemma coe_wBPSchwartz : (wBPSchwartz : ℝ → ℂ) = bandpassFilterWeight := rfl

/-- Explicit Fourier representation $w_{\mathrm{BP}} = \mathcal{F}(\widehat{w}_{\mathrm{BP}})$. -/
lemma w_BP_eq_fourier : bandpassFilterWeight = 𝓕 wBPFreq := by
  change (wBPSchwartz : ℝ → ℂ) = 𝓕 wBPFreq
  rw [wBPSchwartz, SchwartzMap.fourier_coe, coe_wBPFreqSchwartz]

/-- Pointwise integral formula for $w_{\mathrm{BP}}(t)$. -/
lemma w_BP_apply (t : ℝ) :
    bandpassFilterWeight t = ∫ ξ : ℝ, Complex.exp (↑(-2 * Real.pi * ξ * t) * Complex.I) * wBPFreq ξ := by
  have h := congr_fun w_BP_eq_fourier t
  rw [h, Real.fourier_real_eq_integral_exp_smul]
  simp only [smul_eq_mul]

/-!
## 3. Integrability and Polynomial Moments of $w_{\mathrm{BP}}$
-/

/-- $w_{\mathrm{BP}} : \mathbb{R} \to \mathbb{C}$ is Bochner integrable on $\mathbb{R}$. -/
theorem integrable_w_BP : Integrable bandpassFilterWeight :=
  wBPSchwartz.integrable

/-- $\|w_{\mathrm{BP}}(\cdot)\| : \mathbb{R} \to \mathbb{R}$ is integrable on $\mathbb{R}$. -/
theorem integrable_norm_w_BP : Integrable (fun t : ℝ => ‖bandpassFilterWeight t‖) :=
  integrable_w_BP.norm

/-- Every polynomial moment $t \mapsto \|w_{\mathrm{BP}}(t)\| |t|^n$ is integrable on $\mathbb{R}$. -/
theorem integrable_norm_w_BP_mul_abs_pow (n : ℕ) :
    Integrable (fun t : ℝ => ‖bandpassFilterWeight t‖ * |t| ^ n) := by
  have h := wBPSchwartz.integrable_pow_mul (volume : Measure ℝ) n
  refine h.congr (Filter.Eventually.of_forall (fun t => ?_))
  simp only [wBPSchwartz_apply, Real.norm_eq_abs, mul_comm]

/-- First absolute moment $t \mapsto \|w_{\mathrm{BP}}(t)\| |t|$ is integrable on $\mathbb{R}$. -/
theorem integrable_norm_w_BP_mul_abs :
    Integrable (fun t : ℝ => ‖bandpassFilterWeight t‖ * |t|) := by
  simpa only [pow_one] using integrable_norm_w_BP_mul_abs_pow 1

/-!
## 4. Evenness and Real-Valued Symmetry ($w_{\mathrm{BP}}(t)^* = w_{\mathrm{BP}}(t)$)
-/

/-- $w_{\mathrm{BP}}$ is an even function of time: $w_{\mathrm{BP}}(-t) = w_{\mathrm{BP}}(t)$. -/
theorem w_BP_even (t : ℝ) : bandpassFilterWeight (-t) = bandpassFilterWeight t := by
  have h1 : bandpassFilterWeight (-t) = 𝓕⁻ wBPFreq t := by
    rw [w_BP_eq_fourier, Real.fourierInv_eq_fourier_neg]
  have h2 : 𝓕⁻ wBPFreq = 𝓕 wBPFreq := by
    rw [Real.fourierInv_eq_fourier_comp_neg]
    congr 1
    ext ξ
    exact wBPFreq_neg ξ
  rw [h1, h2, ← w_BP_eq_fourier]

/-- $w_{\mathrm{BP}}(t)$ is real-valued for all $t \in \mathbb{R}$: $\mathrm{star}(w_{\mathrm{BP}}(t)) = w_{\mathrm{BP}}(t)$. -/
theorem star_w_BP (t : ℝ) : star (bandpassFilterWeight t) = bandpassFilterWeight t := by
  calc star (bandpassFilterWeight t)
    _ = (starRingEnd ℂ) (∫ ξ : ℝ, Complex.exp (↑(-2 * Real.pi * ξ * t) * Complex.I) * wBPFreq ξ) := by
        rw [w_BP_apply, Complex.star_def]
    _ = ∫ ξ : ℝ, (starRingEnd ℂ) (Complex.exp (↑(-2 * Real.pi * ξ * t) * Complex.I) * wBPFreq ξ) := by
        rw [← integral_conj]
    _ = ∫ ξ : ℝ, Complex.exp (↑(-2 * Real.pi * ξ * (-t)) * Complex.I) * wBPFreq ξ := by
        refine integral_congr_ae (Filter.Eventually.of_forall (fun ξ => ?_))
        simp only [wBPFreq, map_mul, ← Complex.exp_conj, Complex.conj_ofReal, Complex.conj_I]
        congr 2
        push_cast
        ring
    _ = bandpassFilterWeight (-t) := (w_BP_apply (-t)).symm
    _ = bandpassFilterWeight t := w_BP_even t

/-!
## 5. Exact Fourier Inversion, Unit Normalization, and Vanishing for $|\omega| \ge 1/2$
-/

/-- By Fourier inversion on $\mathcal{S}(\mathbb{R}, \mathbb{C})$, the Fourier transform
    $\int_{\mathbb{R}} w_{\mathrm{BP}}(t) e^{i\omega t}\,dt$ recovers $\widehat{w}_{\mathrm{BP}}(\omega / (2\pi))$. -/
theorem integral_w_BP_mul_exp_eq (ω : ℝ) :
    (∫ t : ℝ, bandpassFilterWeight t * Complex.exp (Complex.I * (ω : ℂ) * (t : ℂ))) =
      wBPFreq (ω / (2 * Real.pi)) := by
  let ξ : ℝ := ω / (2 * Real.pi)
  have h_inv_schwartz : (𝓕⁻ (𝓕 wBPFreqSchwartz) : 𝓢(ℝ, ℂ)) ξ = wBPFreqSchwartz ξ := by
    rw [FourierTransform.fourierInv_fourier_eq]
  have h_inv : 𝓕⁻ bandpassFilterWeight ξ = wBPFreq ξ := by
    simpa only [SchwartzMap.fourierInv_coe, SchwartzMap.fourier_coe, coe_wBPFreqSchwartz,
      w_BP_eq_fourier, wBPFreqSchwartz_apply] using h_inv_schwartz
  rw [← h_inv, Real.fourierInv_eq_fourier_neg, Real.fourier_real_eq_integral_exp_smul]
  refine integral_congr_ae (Filter.Eventually.of_forall (fun t => ?_))
  simp only [smul_eq_mul, mul_comm (Complex.exp _)]
  congr 2
  have hpi : (2 * Real.pi : ℝ) ≠ 0 := by positivity
  have h_arg : (-2 * Real.pi * t * -ξ : ℝ) = ω * t := by
    dsimp [ξ]
    calc -2 * Real.pi * t * -(ω / (2 * Real.pi))
      _ = (ω / (2 * Real.pi) * (2 * Real.pi)) * t := by ring
      _ = ω * t := by rw [div_mul_cancel₀ ω hpi]
  rw [h_arg]
  push_cast
  ring

/-- Unit normalization of the smooth bandpass filter weight: $\int_{\mathbb{R}} w_{\mathrm{BP}}(t)\,dt = 1$. -/
theorem integral_w_BP_eq_one : (∫ t : ℝ, bandpassFilterWeight t) = 1 := by
  have h0 := integral_w_BP_mul_exp_eq 0
  simpa only [Complex.ofReal_zero, mul_zero, zero_mul, Complex.exp_zero, mul_one,
    zero_div, wBPFreq_zero] using h0

/-- **Exact Bandpass Frequency Vanishing**: for all $|\omega| \ge 1/2$,
    $$\int_{\mathbb{R}} w_{\mathrm{BP}}(t) e^{i\omega t}\,dt = 0.$$ -/
theorem integral_w_BP_mul_exp_eq_zero_of_abs_ge_half {ω : ℝ} (hω : (1 / 2 : ℝ) ≤ |ω|) :
    (∫ t : ℝ, bandpassFilterWeight t * Complex.exp (Complex.I * (ω : ℂ) * (t : ℂ))) = 0 := by
  rw [integral_w_BP_mul_exp_eq]
  apply wBPFreq_eq_zero_of_le_abs
  have hpi : 0 < 2 * Real.pi := by positivity
  rw [abs_div, abs_of_pos hpi]
  calc 1 / (4 * Real.pi)
    _ = (1 / 2) / (2 * Real.pi) := by ring
    _ ≤ |ω| / (2 * Real.pi) := div_le_div_of_nonneg_right hω hpi.le

/-!
## 6. Superpolynomial Time-Domain Tail Decay of $w_{\mathrm{BP}}$
-/

/-- Markov tail inequality for the $m$-th polynomial moment of $w_{\mathrm{BP}}$: for any $R > 0$
    and $k \in \mathbb{N}$,
    $$R^k \int_{|t| \ge R} \|w_{\mathrm{BP}}(t)\| |t|^m\,dt \le \int_{\mathbb{R}} \|w_{\mathrm{BP}}(t)\| |t|^{m + k}\,dt.$$ -/
lemma pow_mul_tail_integral_norm_w_BP_mul_abs_pow_le (m k : ℕ) {R : ℝ} (hR : 0 ≤ R) :
    R ^ k * (∫ t in {t : ℝ | R ≤ |t|}, ‖bandpassFilterWeight t‖ * |t| ^ m) ≤
      ∫ t : ℝ, ‖bandpassFilterWeight t‖ * |t| ^ (m + k) := by
  let S : Set ℝ := {t : ℝ | R ≤ |t|}
  have hS : MeasurableSet S := isClosed_le continuous_const continuous_abs |>.measurableSet
  rw [← integral_const_mul]
  have h_mono : ∫ t in S, R ^ k * (‖bandpassFilterWeight t‖ * |t| ^ m) ≤
      ∫ t in S, ‖bandpassFilterWeight t‖ * |t| ^ (m + k) := by
    refine setIntegral_mono_on
      ((integrable_norm_w_BP_mul_abs_pow m).const_mul (R ^ k)).integrableOn
      (integrable_norm_w_BP_mul_abs_pow (m + k)).integrableOn hS (fun t ht => ?_)
    have hpow : R ^ k ≤ |t| ^ k := pow_le_pow_left₀ hR ht k
    have hnonneg : 0 ≤ ‖bandpassFilterWeight t‖ * |t| ^ m := by positivity
    calc R ^ k * (‖bandpassFilterWeight t‖ * |t| ^ m)
      _ = (‖bandpassFilterWeight t‖ * |t| ^ m) * R ^ k := mul_comm _ _
      _ ≤ (‖bandpassFilterWeight t‖ * |t| ^ m) * |t| ^ k := mul_le_mul_of_nonneg_left hpow hnonneg
      _ = ‖bandpassFilterWeight t‖ * |t| ^ (m + k) := by rw [pow_add, mul_assoc]
  exact h_mono.trans (setIntegral_le_integral (integrable_norm_w_BP_mul_abs_pow (m + k))
    (Filter.Eventually.of_forall (fun t => by positivity)))

/-- For any $m \in \mathbb{N}$ and $c > 0$, the time-domain tail integral
    $$j \mapsto \int_{|t| \ge c j} \|w_{\mathrm{BP}}(t)\| |t|^m\,dt$$
    belongs to the superpolynomial decay class `IsSuperpolynomialDecay`. -/
theorem isSuperpolynomialDecay_tail_integral_norm_w_BP_mul_abs_pow
    (m : ℕ) {c : ℝ} (hc : 0 < c) :
    IsSuperpolynomialDecay
      (fun j : ℕ => ∫ t in {t : ℝ | c * (j : ℝ) ≤ |t|}, ‖bandpassFilterWeight t‖ * |t| ^ m) := by
  refine ⟨fun j => setIntegral_nonneg
    (isClosed_le continuous_const continuous_abs |>.measurableSet)
    (fun t _ => by positivity), fun n => ?_⟩
  let M : ℝ := ∫ t : ℝ, ‖bandpassFilterWeight t‖ * |t| ^ (m + (n + 1))
  let C : ℝ := M / c ^ (n + 1)
  have h_zero : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 0) := tendsto_const_nhds
  have h_upper : Tendsto (fun j : ℕ => C * (j : ℝ)⁻¹) atTop (𝓝 0) := by
    simpa only [mul_zero, Function.comp_def] using
      (tendsto_const_nhds (x := C)).mul (tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop)
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' h_zero h_upper
    (Filter.Eventually.of_forall (fun j => mul_nonneg (pow_nonneg (Nat.cast_nonneg j) n)
      (setIntegral_nonneg (isClosed_le continuous_const continuous_abs |>.measurableSet)
        (fun t _ => by positivity)))) ?_
  filter_upwards [Filter.eventually_ge_atTop 1] with j hj
  have hj_pos : (0 : ℝ) < (j : ℝ) := Nat.cast_pos.mpr ( Nat.succ_le_iff.mp hj )
  have hc_pow_pos : 0 < c ^ (n + 1) := pow_pos hc (n + 1)
  have h_markov := pow_mul_tail_integral_norm_w_BP_mul_abs_pow_le m (n + 1)
    (mul_nonneg hc.le (Nat.cast_nonneg j))
  set I_j : ℝ := ∫ t in {t : ℝ | c * (j : ℝ) ≤ |t|}, ‖bandpassFilterWeight t‖ * |t| ^ m
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

/-- For any $c > 0$, the time-domain tail integral
    $$j \mapsto \int_{|t| \ge c j} \|w_{\mathrm{BP}}(t)\|\,dt$$
    belongs to `IsSuperpolynomialDecay`. -/
theorem isSuperpolynomialDecay_tail_integral_norm_w_BP {c : ℝ} (hc : 0 < c) :
    IsSuperpolynomialDecay
      (fun j : ℕ => ∫ t in {t : ℝ | c * (j : ℝ) ≤ |t|}, ‖bandpassFilterWeight t‖) := by
  simpa only [pow_zero, mul_one] using
    isSuperpolynomialDecay_tail_integral_norm_w_BP_mul_abs_pow 0 hc

/-- For any $c > 0$, the first-moment time-domain tail integral
    $$j \mapsto \int_{|t| \ge c j} \|w_{\mathrm{BP}}(t)\| |t|\,dt$$
    belongs to `IsSuperpolynomialDecay`. -/
theorem isSuperpolynomialDecay_tail_integral_norm_w_BP_mul_abs {c : ℝ} (hc : 0 < c) :
    IsSuperpolynomialDecay
      (fun j : ℕ => ∫ t in {t : ℝ | c * (j : ℝ) ≤ |t|}, ‖bandpassFilterWeight t‖ * |t|) := by
  simpa only [pow_one] using
    isSuperpolynomialDecay_tail_integral_norm_w_BP_mul_abs_pow 1 hc

/-!
## 7. Packaged Smooth Bandpass Filter Specification and Existence Theorem
-/

/-- Specification predicate for a smooth bandpass filter weight $w : \mathbb{R} \to \mathbb{C}$
    having unit normalization, real-valued even symmetry, all polynomial moments integrable,
    exact Fourier vanishing on $|\omega| \ge 1/2$, and superpolynomially decaying time-domain
    tail integrals. -/
structure IsSmoothBandpassFilterWeight (w : ℝ → ℂ) : Prop where
  integrable : Integrable w
  integral_eq_one : (∫ t : ℝ, w t) = 1
  star_eq_self : ∀ t : ℝ, star (w t) = w t
  even : ∀ t : ℝ, w (-t) = w t
  integrable_norm_mul_abs : Integrable (fun t : ℝ => ‖w t‖ * |t|)
  integrable_norm_mul_abs_pow : ∀ n : ℕ, Integrable (fun t : ℝ => ‖w t‖ * |t| ^ n)
  fourier_eq_zero_of_abs_ge_half :
    ∀ ω : ℝ, (1 / 2 : ℝ) ≤ |ω| →
      (∫ t : ℝ, w t * Complex.exp (Complex.I * (ω : ℂ) * (t : ℂ))) = 0
  superpoly_tail_decay :
    ∀ {c : ℝ}, 0 < c →
      IsSuperpolynomialDecay (fun j : ℕ => ∫ t in {t : ℝ | c * (j : ℝ) ≤ |t|}, ‖w t‖)
  superpoly_tail_mul_abs_decay :
    ∀ {c : ℝ}, 0 < c →
      IsSuperpolynomialDecay (fun j : ℕ => ∫ t in {t : ℝ | c * (j : ℝ) ≤ |t|}, ‖w t‖ * |t|)

/-- `bandpassFilterWeight` satisfies the complete smooth bandpass filter weight specification. -/
theorem isSmoothBandpassFilterWeight_w_BP : IsSmoothBandpassFilterWeight bandpassFilterWeight where
  integrable := integrable_w_BP
  integral_eq_one := integral_w_BP_eq_one
  star_eq_self := star_w_BP
  even := w_BP_even
  integrable_norm_mul_abs := integrable_norm_w_BP_mul_abs
  integrable_norm_mul_abs_pow := integrable_norm_w_BP_mul_abs_pow
  fourier_eq_zero_of_abs_ge_half := fun _ hω => integral_w_BP_mul_exp_eq_zero_of_abs_ge_half hω
  superpoly_tail_decay := fun hc => isSuperpolynomialDecay_tail_integral_norm_w_BP hc
  superpoly_tail_mul_abs_decay := fun hc =>
    isSuperpolynomialDecay_tail_integral_norm_w_BP_mul_abs hc

/-- Constructive existence of a smooth bandpass filter weight satisfying
    `IsSmoothBandpassFilterWeight`. -/
theorem smooth_bandpass_filter_weight_exists :
    ∃ w : ℝ → ℂ, IsSmoothBandpassFilterWeight w :=
  ⟨bandpassFilterWeight, isSmoothBandpassFilterWeight_w_BP⟩

end
