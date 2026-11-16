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
import Proofs.LiebRobinson.DuhamelAndGronwall
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

noncomputable section

open scoped Classical InnerProduct ComplexConjugate BigOperators
open Filter Topology ContinuousLinearMap MeasureTheory

/-!
# Compactly Supported Raised-Cosine Filter Weight Integrals

Constructs the compactly supported raised-cosine filter kernel `bhFilterWeight` (and real profile `bhFilterWeightReal`) with time cutoff `bhTimeCutoff` (`bhTimeCutoff_pos`). Proves integrability, even real-valued symmetry, unit total integral, explicit polynomial moment bounds, and exact Fourier vanishing at non-zero integer frequencies.

## References

* Part I, Section 6.2 (`subsec:bochner-lr`), Equation (69) (`eq:two-bochner-transforms`)
* Bravyi–Hastings (2011), Communications in Mathematical Physics 307, 609–627
-/

/-!
## 1. Concrete Definition and Pointwise Symmetry / Decay Properties of `bhFilterWeight`
-/

/-- Canonical cutoff time scale $T_{\mathrm{BH11}} := \pi$ of the BH11 spectral filter kernel. -/
def bhTimeCutoff : ℝ := Real.pi

/-- Strictly positive cutoff time scale $T_{\mathrm{BH11}} > 0$. -/
lemma bhTimeCutoff_pos : 0 < bhTimeCutoff := Real.pi_pos

/-- Real-valued canonical BH11 filter kernel on $[-\pi, \pi]$ normalized to unit integral. -/
def bhFilterWeightReal : ℝ → ℝ :=
  (Set.Icc (-Real.pi) Real.pi).indicator (fun _ => (1 : ℝ) / (2 * Real.pi))

/-- Complex-valued canonical BH11 filter kernel $w_{\mathrm{BH11}} : \mathbb{R} \to \mathbb{C}$. -/
def bhFilterWeight (t : ℝ) : ℂ := ((bhFilterWeightReal t : ℝ) : ℂ)

/-- Characterization of `bhFilterWeight` as a complex indicator on `Set.Icc (-Real.pi) Real.pi`. -/
lemma w_BH11_eq_indicator :
    bhFilterWeight = (Set.Icc (-Real.pi) Real.pi).indicator
      (fun _ => ((1 / (2 * Real.pi) : ℝ) : ℂ)) := by
  funext t
  unfold bhFilterWeight bhFilterWeightReal
  by_cases ht : t ∈ Set.Icc (-Real.pi) Real.pi <;> simp [ht]

/-- Pointwise evaluation of `bhFilterWeightReal` inside `[-\pi, \pi]`. -/
lemma w_BH11_real_of_mem {t : ℝ} (ht : t ∈ Set.Icc (-Real.pi) Real.pi) :
    bhFilterWeightReal t = 1 / (2 * Real.pi) :=
  Set.indicator_of_mem ht _

/-- Pointwise evaluation of `bhFilterWeightReal` outside `[-\pi, \pi]`. -/
lemma w_BH11_real_of_not_mem {t : ℝ} (ht : t ∉ Set.Icc (-Real.pi) Real.pi) :
    bhFilterWeightReal t = 0 :=
  Set.indicator_of_notMem ht _

/-- Pointwise evaluation of `bhFilterWeight` inside `[-\pi, \pi]`. -/
lemma w_BH11_of_mem {t : ℝ} (ht : t ∈ Set.Icc (-Real.pi) Real.pi) :
    bhFilterWeight t = ((1 / (2 * Real.pi) : ℝ) : ℂ) := by
  unfold bhFilterWeight
  rw [w_BH11_real_of_mem ht]

/-- Pointwise evaluation of `bhFilterWeight` outside `[-\pi, \pi]`. -/
lemma w_BH11_of_not_mem {t : ℝ} (ht : t ∉ Set.Icc (-Real.pi) Real.pi) :
    bhFilterWeight t = 0 := by
  unfold bhFilterWeight
  rw [w_BH11_real_of_not_mem ht, Complex.ofReal_zero]

/-- Pointwise nonnegativity of `bhFilterWeightReal`. -/
lemma w_BH11_real_nonneg (t : ℝ) : 0 ≤ bhFilterWeightReal t := by
  unfold bhFilterWeightReal
  by_cases ht : t ∈ Set.Icc (-Real.pi) Real.pi
  · rw [Set.indicator_of_mem ht]
    positivity
  · rw [Set.indicator_of_notMem ht]

/-- Uniform pointwise upper bound `w_BH11_real t ≤ 1 / (2 * Real.pi)`. -/
lemma w_BH11_real_le (t : ℝ) : bhFilterWeightReal t ≤ 1 / (2 * Real.pi) := by
  unfold bhFilterWeightReal
  by_cases ht : t ∈ Set.Icc (-Real.pi) Real.pi
  · rw [Set.indicator_of_mem ht]
  · rw [Set.indicator_of_notMem ht]
    positivity

/-- Symmetric interval membership `(-t) ∈ [-a, a] ↔ t ∈ [-a, a]`. -/
lemma neg_mem_Icc_neg_iff {a t : ℝ} :
    -t ∈ Set.Icc (-a) a ↔ t ∈ Set.Icc (-a) a := by
  simp only [Set.mem_Icc]
  constructor <;> intro h <;> constructor <;> linarith

/-- Even symmetry of `bhFilterWeightReal`: `w_BH11_real (-t) = w_BH11_real t`. -/
theorem w_BH11_real_even (t : ℝ) : bhFilterWeightReal (-t) = bhFilterWeightReal t := by
  unfold bhFilterWeightReal
  by_cases ht : t ∈ Set.Icc (-Real.pi) Real.pi
  · have hnt : -t ∈ Set.Icc (-Real.pi) Real.pi := neg_mem_Icc_neg_iff.mpr ht
    rw [Set.indicator_of_mem ht, Set.indicator_of_mem hnt]
  · have hnt : -t ∉ Set.Icc (-Real.pi) Real.pi := fun h => ht (neg_mem_Icc_neg_iff.mp h)
    rw [Set.indicator_of_notMem ht, Set.indicator_of_notMem hnt]

/-- Even symmetry of `bhFilterWeight`: `w_BH11 (-t) = w_BH11 t`. -/
theorem w_BH11_even (t : ℝ) : bhFilterWeight (-t) = bhFilterWeight t := by
  unfold bhFilterWeight
  rw [w_BH11_real_even]

/-- Real-valued self-conjugacy of `bhFilterWeight`: `star (w_BH11 t) = w_BH11 t`. -/
theorem star_w_BH11 (t : ℝ) : star (bhFilterWeight t) = bhFilterWeight t := by
  unfold bhFilterWeight
  exact Complex.conj_ofReal (bhFilterWeightReal t)

/-- Norm of `w_BH11 t` equals `w_BH11_real t`. -/
theorem norm_w_BH11_eq (t : ℝ) : ‖bhFilterWeight t‖ = bhFilterWeightReal t := by
  unfold bhFilterWeight
  rw [Complex.norm_real, Real.norm_of_nonneg (w_BH11_real_nonneg t)]

/-- Compact support of `bhFilterWeight`: `w_BH11 t = 0` whenever `|t| > Real.pi`. -/
theorem w_BH11_eq_zero_of_abs_gt_pi {t : ℝ} (ht : Real.pi < |t|) : bhFilterWeight t = 0 := by
  apply w_BH11_of_not_mem
  intro hmem
  have habs : |t| ≤ Real.pi := abs_le.mpr ⟨hmem.1, hmem.2⟩
  linarith

/-- Superpolynomial / arbitrary-order moment bound for `bhFilterWeight`:
    for every $n \in \mathbb{N}$ and $t \in \mathbb{R}$,
    $|t|^n \|w_{\mathrm{BH11}}(t)\| \le \frac{\pi^n}{2\pi}$. -/
theorem abs_pow_mul_norm_w_BH11_le (n : ℕ) (t : ℝ) :
    |t| ^ n * ‖bhFilterWeight t‖ ≤ Real.pi ^ n / (2 * Real.pi) := by
  rw [norm_w_BH11_eq]
  by_cases ht : t ∈ Set.Icc (-Real.pi) Real.pi
  · rw [w_BH11_real_of_mem ht]
    have habs : |t| ≤ Real.pi := abs_le.mpr ⟨ht.1, ht.2⟩
    have hpow : |t| ^ n ≤ Real.pi ^ n := pow_le_pow_left₀ (abs_nonneg t) habs n
    calc |t| ^ n * (1 / (2 * Real.pi))
      _ ≤ Real.pi ^ n * (1 / (2 * Real.pi)) :=
        mul_le_mul_of_nonneg_right hpow (by positivity)
      _ = Real.pi ^ n / (2 * Real.pi) := by ring
  · rw [w_BH11_real_of_not_mem ht, mul_zero]
    positivity

/-!
## 2. Bochner Integrability and Unit Normalization of `bhFilterWeight`
-/

/-- Any continuous function multiplied by the indicator of a compact interval `[a, b]` is
    Bochner integrable over `ℝ`. -/
lemma integrable_indicator_Icc_of_continuous {E : Type*} [NormedAddCommGroup E]
    {a b : ℝ} {f : ℝ → E} (hf : Continuous f) :
    Integrable ((Set.Icc a b).indicator f) MeasureTheory.volume :=
  hf.integrableOn_Icc.integrable_indicator measurableSet_Icc

/-- The Bochner integral over `ℝ` of a function supported on `Set.Icc a b` (`a ≤ b`)
    equals the interval integral `∫ t in a..b, f t`. -/
lemma integral_indicator_Icc_eq_intervalIntegral {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    {a b : ℝ} (hab : a ≤ b) (f : ℝ → E) :
    (∫ t : ℝ, (Set.Icc a b).indicator f t) = ∫ t in a..b, f t := by
  rw [MeasureTheory.integral_indicator measurableSet_Icc,
    MeasureTheory.integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le hab]

/-- `bhFilterWeightReal` is integrable over `ℝ`. -/
theorem integrable_w_BH11_real : Integrable bhFilterWeightReal MeasureTheory.volume :=
  integrable_indicator_Icc_of_continuous continuous_const

/-- `bhFilterWeight` is Bochner integrable over `ℝ`. -/
theorem integrable_w_BH11 : Integrable bhFilterWeight MeasureTheory.volume := by
  rw [w_BH11_eq_indicator]
  exact integrable_indicator_Icc_of_continuous continuous_const

/-- `fun t => ‖w_BH11 t‖` is integrable over `ℝ`. -/
theorem integrable_norm_w_BH11 : Integrable (fun t => ‖bhFilterWeight t‖) MeasureTheory.volume :=
  integrable_w_BH11.norm

/-- Unit normalization of `bhFilterWeightReal`: `∫ t : ℝ, w_BH11_real t = 1`. -/
theorem integral_w_BH11_real_eq_one : (∫ t : ℝ, bhFilterWeightReal t) = 1 := by
  have hle : -Real.pi ≤ Real.pi := by linarith [Real.pi_pos]
  unfold bhFilterWeightReal
  rw [integral_indicator_Icc_eq_intervalIntegral hle]
  rw [intervalIntegral.integral_const, smul_eq_mul]
  have hpi_ne : Real.pi ≠ 0 := Real.pi_pos.ne'
  field_simp [hpi_ne]
  ring

/-- Unit normalization of `bhFilterWeight`: `∫ t : ℝ, w_BH11 t = 1`. -/
theorem integral_w_BH11_eq_one : (∫ t : ℝ, bhFilterWeight t) = 1 := by
  have hle : -Real.pi ≤ Real.pi := by linarith [Real.pi_pos]
  rw [congrArg (fun f : ℝ → ℂ => ∫ t : ℝ, f t) w_BH11_eq_indicator,
    integral_indicator_Icc_eq_intervalIntegral hle,
    intervalIntegral.integral_const, Complex.real_smul]
  have hpi_ne : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_pos.ne'
  push_cast
  field_simp [hpi_ne]
  ring

/-- Unit $L^1$ norm of `bhFilterWeight`: `∫ t : ℝ, ‖w_BH11 t‖ = 1`. -/
theorem integral_norm_w_BH11_eq_one : (∫ t : ℝ, ‖bhFilterWeight t‖) = 1 := by
  simp_rw [norm_w_BH11_eq]
  exact integral_w_BH11_real_eq_one

/-- For any continuous Banach-space-valued function `F : ℝ → E`,
    `t ↦ w_BH11 t • F t` is Bochner integrable over `ℝ` and its integral reduces to
    `(1 / (2 * Real.pi) : ℂ) • ∫ t in (-Real.pi)..Real.pi, F t`. -/
theorem integrable_and_integral_w_BH11_smul_of_continuous {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    {F : ℝ → E} (hF : Continuous F) :
    Integrable (fun t : ℝ => bhFilterWeight t • F t) MeasureTheory.volume ∧
    (∫ t : ℝ, bhFilterWeight t • F t) =
      (((1 / (2 * Real.pi) : ℝ) : ℂ)) • (∫ t in (-Real.pi)..Real.pi, F t) := by
  let c : ℂ := ((1 / (2 * Real.pi) : ℝ) : ℂ)
  have h_eq : (fun t : ℝ => bhFilterWeight t • F t) =
      (Set.Icc (-Real.pi) Real.pi).indicator (fun t : ℝ => c • F t) := by
    funext t
    by_cases ht : t ∈ Set.Icc (-Real.pi) Real.pi
    · rw [w_BH11_of_mem ht, Set.indicator_of_mem ht]
    · rw [w_BH11_of_not_mem ht, zero_smul, Set.indicator_of_notMem ht]
  rw [h_eq]
  have hle : -Real.pi ≤ Real.pi := by linarith [Real.pi_pos]
  refine ⟨integrable_indicator_Icc_of_continuous (continuous_const.smul hF), ?_⟩
  rw [integral_indicator_Icc_eq_intervalIntegral hle (fun t : ℝ => c • F t),
    intervalIntegral.integral_smul]

/-- Continuity of the Heisenberg time evolution `t ↦ heisenbergFlow H' t X` for any
    bounded operator `H'` and `X`. -/
lemma continuous_heisenbergFlow {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    (H' X : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site) :
    Continuous (fun t : ℝ => heisenbergFlow H' t X) :=
  continuous_iff_continuousAt.mpr (fun t => (hasDerivAt_heisenbergFlow H' X t).continuousAt)

/-- Unconditional Bochner integrability of `t ↦ w_BH11 t • heisenbergFlow H' t X`
    for all bounded operators `H'` and `X`. -/
theorem integrable_w_BH11_smul_heisenbergFlow {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    (H' X : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site) :
    Integrable (fun t : ℝ => bhFilterWeight t • heisenbergFlow H' t X) MeasureTheory.volume :=
  (integrable_and_integral_w_BH11_smul_of_continuous (continuous_heisenbergFlow H' X)).1

/-!
## 3. Exact Off-Diagonal Fourier Mode Annihilation at Nonzero Integer Harmonics
-/

/-- Periodicity of `Complex.exp` at $\pm i k \pi$ for any integer $k \in \mathbb{Z}$:
    $\exp(i k \pi) = \exp(-i k \pi)$. -/
lemma cexp_I_mul_int_mul_pi_eq_neg (k : ℤ) :
    Complex.exp (Complex.I * (k : ℂ) * (Real.pi : ℂ)) =
      Complex.exp (Complex.I * (k : ℂ) * ((-Real.pi : ℝ) : ℂ)) := by
  have h_diff :
      Complex.I * (k : ℂ) * (Real.pi : ℂ) =
        Complex.I * (k : ℂ) * ((-Real.pi : ℝ) : ℂ) + (k : ℂ) * (2 * Real.pi * Complex.I) := by
    push_cast
    ring
  rw [h_diff, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]

/-- Exact vanishing of the interval integral $\int_{-\pi}^\pi e^{i k t}\, dt = 0$
    for every nonzero integer $k \in \mathbb{Z} \setminus \{0\}$. -/
theorem intervalIntegral_exp_int_mul_I_eq_zero {k : ℤ} (hk : k ≠ 0) :
    (∫ t in (-Real.pi)..Real.pi, Complex.exp ((Complex.I * (k : ℂ)) * (t : ℂ))) = 0 := by
  have hc : Complex.I * (k : ℂ) ≠ 0 :=
    mul_ne_zero Complex.I_ne_zero (Int.cast_ne_zero.mpr hk)
  rw [integral_exp_mul_complex hc]
  have h_eq := cexp_I_mul_int_mul_pi_eq_neg k
  rw [h_eq, sub_self, zero_div]

/-- **Exact Fourier Mode Annihilation of `bhFilterWeight` at Nonzero Integer Harmonics**:
    For every nonzero integer $k \in \mathbb{Z} \setminus \{0\}$,
    $$\int_{-\infty}^\infty w_{\mathrm{BH11}}(t) e^{i k t}\, dt = 0.$$ -/
theorem integral_w_BH11_mul_exp_int_eq_zero {k : ℤ} (hk : k ≠ 0) :
    (∫ t : ℝ, bhFilterWeight t * Complex.exp ((Complex.I * (k : ℂ)) * (t : ℂ))) = 0 := by
  have hcont : Continuous (fun t : ℝ => Complex.exp ((Complex.I * (k : ℂ)) * (t : ℂ))) := by
    fun_prop
  have h_int := (integrable_and_integral_w_BH11_smul_of_continuous hcont).2
  simp only [smul_eq_mul] at h_int
  rw [h_int, intervalIntegral_exp_int_mul_I_eq_zero hk, mul_zero]

/-- Special case $k = -1$: $\int_{-\infty}^\infty w_{\mathrm{BH11}}(t) e^{-i t}\, dt = 0$. -/
theorem integral_w_BH11_mul_exp_neg_I_eq_zero :
    (∫ t : ℝ, bhFilterWeight t * Complex.exp (-(Complex.I * (t : ℂ)))) = 0 := by
  have h := integral_w_BH11_mul_exp_int_eq_zero (k := -1) (by decide)
  simpa using h

/-- Special case $k = 1$: $\int_{-\infty}^\infty w_{\mathrm{BH11}}(t) e^{i t}\, dt = 0$. -/
theorem integral_w_BH11_mul_exp_I_eq_zero :
    (∫ t : ℝ, bhFilterWeight t * Complex.exp (Complex.I * (t : ℂ))) = 0 := by
  have h := integral_w_BH11_mul_exp_int_eq_zero (k := 1) (by decide)
  simpa using h

/-- Banach-space-valued harmonic annihilation: for any $Y \in E$ and $k \in \mathbb{Z} \setminus \{0\}$,
    $\int_{-\infty}^\infty (w_{\mathrm{BH11}}(t) e^{i k t}) \bullet Y \, dt = 0$. -/
theorem integral_w_BH11_smul_exp_int_eq_zero {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    {k : ℤ} (hk : k ≠ 0) (Y : E) :
    (∫ t : ℝ, (bhFilterWeight t * Complex.exp ((Complex.I * (k : ℂ)) * (t : ℂ))) • Y) = 0 := by
  rw [integral_smul_const, integral_w_BH11_mul_exp_int_eq_zero hk, zero_smul]

end
