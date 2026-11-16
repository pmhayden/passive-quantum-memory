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

import Defs.SuperpolyDecay
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Algebraic and Tail-Summation Closure of Superpolynomial Decay Profiles

Proves that the superpolynomial decay class `IsSuperpolynomialDecay` is closed under non-negative scalar multiplication (`isSuperpolynomialDecay_const_mul`), addition (`isSuperpolynomialDecay_add`), pointwise maximum (`isSuperpolynomialDecay_max`), polynomial multiplication (`isSuperpolynomialDecay_mul_pow`), summability (`summable_of_isSuperpolynomialDecay`), affine division rescaling (`isSuperpolynomialDecay_floor_div`), and Bravyi–Hastings lattice-volume tail summation `fTilde` (`isSuperpolynomialDecay_fTilde`).

## References

* Part I, Section 6.1 (`subsec:dsuper-banach`), Equation (62) (`eq:dsuper-def`), Lemma 6.2 (`lem:dsuper-closure`)
* Part II, Section 2 (`subsec:setup`), Definition 2.3 (`def:perturbation-class`), Lemma 2.4 (`lem:D-super-closure`)
* Bravyi–Hastings (2011), Communications in Mathematical Physics 307, 609–627
-/

noncomputable section

open scoped Classical BigOperators
open Filter Topology Asymptotics

/-!
## 1. Basic Algebraic Closure of `IsSuperpolynomialDecay`
-/

/-- The zero function belongs to `IsSuperpolynomialDecay`. -/
lemma isSuperpolynomialDecay_zero :
    IsSuperpolynomialDecay (fun _ : ℕ => (0 : ℝ)) := by
  refine ⟨fun _ => le_rfl, fun n => ?_⟩
  simpa only [mul_zero] using (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 0))

/-- `IsSuperpolynomialDecay` is closed under multiplication by a non-negative real constant $c \ge 0$. -/
lemma isSuperpolynomialDecay_const_mul {f : ℕ → ℝ} (hf : IsSuperpolynomialDecay f)
    {c : ℝ} (hc : 0 ≤ c) :
    IsSuperpolynomialDecay (fun r => c * f r) := by
  refine ⟨fun r => mul_nonneg hc (hf.1 r), fun n => ?_⟩
  have h_eq : (fun r : ℕ => (r : ℝ) ^ n * (c * f r)) =
      (fun r : ℕ => c * ((r : ℝ) ^ n * f r)) := by
    ext r; ring
  rw [h_eq]
  simpa [mul_zero] using (hf.2 n).const_mul c

/-- `IsSuperpolynomialDecay` is closed under pointwise addition. -/
lemma isSuperpolynomialDecay_add {f₁ f₂ : ℕ → ℝ}
    (hf₁ : IsSuperpolynomialDecay f₁) (hf₂ : IsSuperpolynomialDecay f₂) :
    IsSuperpolynomialDecay (fun r => f₁ r + f₂ r) := by
  refine ⟨fun r => add_nonneg (hf₁.1 r) (hf₂.1 r), fun n => ?_⟩
  have h_eq : (fun r : ℕ => (r : ℝ) ^ n * (f₁ r + f₂ r)) =
      (fun r : ℕ => (r : ℝ) ^ n * f₁ r + (r : ℝ) ^ n * f₂ r) := by
    ext r; ring
  rw [h_eq]
  simpa [add_zero] using (hf₁.2 n).add (hf₂.2 n)

/-- `IsSuperpolynomialDecay` is closed under pointwise maximum $\max(f_1(r), f_2(r))$. -/
lemma isSuperpolynomialDecay_max {f₁ f₂ : ℕ → ℝ}
    (hf₁ : IsSuperpolynomialDecay f₁) (hf₂ : IsSuperpolynomialDecay f₂) :
    IsSuperpolynomialDecay (fun r => max (f₁ r) (f₂ r)) := by
  refine ⟨fun r => le_trans (hf₁.1 r) (le_max_left _ _), fun n => ?_⟩
  have h_zero : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 0) := tendsto_const_nhds
  have h_sum : Tendsto (fun r : ℕ => (r : ℝ) ^ n * f₁ r + (r : ℝ) ^ n * f₂ r) atTop (𝓝 0) := by
    simpa using (hf₁.2 n).add (hf₂.2 n)
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' h_zero h_sum
    (Eventually.of_forall (fun r =>
      mul_nonneg (pow_nonneg (Nat.cast_nonneg r) n) (le_trans (hf₁.1 r) (le_max_left _ _)))) ?_
  refine Eventually.of_forall (fun r => ?_)
  have h_le : max (f₁ r) (f₂ r) ≤ f₁ r + f₂ r :=
    max_le (le_add_of_nonneg_right (hf₂.1 r)) (le_add_of_nonneg_left (hf₁.1 r))
  calc (r : ℝ) ^ n * max (f₁ r) (f₂ r)
    _ ≤ (r : ℝ) ^ n * (f₁ r + f₂ r) :=
      mul_le_mul_of_nonneg_left h_le (pow_nonneg (Nat.cast_nonneg r) n)
    _ = (r : ℝ) ^ n * f₁ r + (r : ℝ) ^ n * f₂ r := mul_add _ _ _

/-- `IsSuperpolynomialDecay` is closed under multiplication by any polynomial power $(r : \mathbb{R})^p$. -/
lemma isSuperpolynomialDecay_mul_pow {f : ℕ → ℝ} (hf : IsSuperpolynomialDecay f) (p : ℕ) :
    IsSuperpolynomialDecay (fun r => (r : ℝ) ^ p * f r) := by
  refine ⟨fun r => mul_nonneg (pow_nonneg (Nat.cast_nonneg r) p) (hf.1 r), fun n => ?_⟩
  have h_eq : (fun r : ℕ => (r : ℝ) ^ n * ((r : ℝ) ^ p * f r)) =
      (fun r : ℕ => (r : ℝ) ^ (n + p) * f r) := by
    ext r
    rw [pow_add, mul_assoc]
  rw [h_eq]
  exact hf.2 (n + p)

/-- Every polynomial moment $r \mapsto (r : \mathbb{R})^p f(r)$ of an `IsSuperpolynomialDecay`
    function is summable over $\mathbb{N}$. -/
lemma summable_pow_mul_of_isSuperpolynomialDecay {f : ℕ → ℝ}
    (hf : IsSuperpolynomialDecay f) (p : ℕ) :
    Summable (fun r : ℕ => (r : ℝ) ^ p * f r) := by
  have h_tendsto : Tendsto (fun r : ℕ => (r : ℝ) ^ (p + 2) * f r) atTop (𝓝 0) :=
    hf.2 (p + 2)
  have h_ev : ∀ᶠ r : ℕ in atTop, (r : ℝ) ^ (p + 2) * f r < 1 :=
    h_tendsto.eventually (Iio_mem_nhds zero_lt_one)
  have h_pseries : Summable (fun r : ℕ => ((r : ℝ) ^ 2)⁻¹) := by
    simp [Real.summable_nat_pow_inv]
  refine Summable.of_norm_bounded_eventually_nat h_pseries ?_
  filter_upwards [h_ev, eventually_ge_atTop 1] with r hr_lt hr_ge
  have hr_pos : (0 : ℝ) < (r : ℝ) := Nat.cast_pos.mpr (by omega)
  have hr_sq_pos : (0 : ℝ) < (r : ℝ) ^ 2 := pow_pos hr_pos 2
  have h_nonneg : 0 ≤ (r : ℝ) ^ p * f r :=
    mul_nonneg (pow_nonneg (Nat.cast_nonneg r) p) (hf.1 r)
  have h_eq : (r : ℝ) ^ p * f r = ((r : ℝ) ^ 2)⁻¹ * ((r : ℝ) ^ (p + 2) * f r) := by
    have hr_sq_ne : (r : ℝ) ^ 2 ≠ 0 := ne_of_gt hr_sq_pos
    have h_alg : (r : ℝ) ^ (p + 2) * f r = (r : ℝ) ^ 2 * ((r : ℝ) ^ p * f r) := by
      rw [pow_add]
      ring
    rw [h_alg, inv_mul_cancel_left₀ hr_sq_ne]
  rw [Real.norm_of_nonneg h_nonneg, h_eq]
  calc ((r : ℝ) ^ 2)⁻¹ * ((r : ℝ) ^ (p + 2) * f r)
    _ ≤ ((r : ℝ) ^ 2)⁻¹ * 1 :=
      mul_le_mul_of_nonneg_left (le_of_lt hr_lt) (inv_nonneg.mpr (le_of_lt hr_sq_pos))
    _ = ((r : ℝ) ^ 2)⁻¹ := mul_one _

/-- Every `IsSuperpolynomialDecay` function is summable over $\mathbb{N}$. -/
lemma summable_of_isSuperpolynomialDecay {f : ℕ → ℝ} (hf : IsSuperpolynomialDecay f) :
    Summable f := by
  simpa using summable_pow_mul_of_isSuperpolynomialDecay hf 0

/-!
## 2. Affine Floor Rescaling, Bravyi–Hastings Tail `fTilde`, and Master Bochner Envelope
-/

/-- Real floor division $r \mapsto \lfloor (r : \mathbb{R}) / c \rfloor$ for $c > 0$ tends to `atTop`. -/
lemma tendsto_floor_div_const_atTop {c : ℝ} (hc : 0 < c) :
    Tendsto (fun r : ℕ => ⌊(r : ℝ) / c⌋₊) atTop atTop := by
  rw [Filter.tendsto_atTop]
  intro b
  rw [Filter.eventually_atTop]
  refine ⟨⌈(b : ℝ) * c⌉₊, fun r hr => ?_⟩
  apply Nat.le_floor
  rw [le_div_iff₀ hc]
  exact le_trans (Nat.le_ceil ((b : ℝ) * c)) (Nat.cast_le.mpr hr)

/-- Integer division by $C > 0$ tends to `atTop` as $r \to \infty$. -/
lemma tendsto_div_const_atTop {C : ℕ} (hC : 0 < C) :
    Tendsto (fun r : ℕ => r / C) atTop atTop := by
  rw [Filter.tendsto_atTop]
  intro b
  rw [Filter.eventually_atTop]
  refine ⟨b * C, fun r hr => ?_⟩
  exact (Nat.le_div_iff_mul_le hC).mpr hr

/-- If $w \in \mathcal{D}_{\mathrm{super}}$ is non-increasing and $v_{\mathrm{LR}} > 0$, then the
    affinely rescaled profile $r \mapsto w(\lfloor r / (2 v_{\mathrm{LR}}) \rfloor)$ belongs to
    $\mathcal{D}_{\mathrm{super}}$. -/
lemma isSuperpolynomialDecay_floor_div {w : ℕ → ℝ}
    (hw : IsSuperpolynomialDecay w) (_hw_anti : Antitone w)
    {v_LR : ℝ} (hv : 0 < v_LR) :
    IsSuperpolynomialDecay (fun r : ℕ => w ⌊(r : ℝ) / (2 * v_LR)⌋₊) := by
  set c : ℝ := 2 * v_LR
  have hc : 0 < c := by dsimp [c]; linarith
  refine ⟨fun r => hw.1 ⌊(r : ℝ) / c⌋₊, fun n => ?_⟩
  have h_zero : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 0) := tendsto_const_nhds
  have h_comp : Tendsto (fun r : ℕ => ((⌊(r : ℝ) / c⌋₊ : ℕ) : ℝ) ^ n * w ⌊(r : ℝ) / c⌋₊)
      atTop (𝓝 0) :=
    (hw.2 n).comp (tendsto_floor_div_const_atTop hc)
  have h_upper : Tendsto
      (fun r : ℕ => (2 * c) ^ n * (((⌊(r : ℝ) / c⌋₊ : ℕ) : ℝ) ^ n * w ⌊(r : ℝ) / c⌋₊))
      atTop (𝓝 0) := by
    simpa [mul_zero] using h_comp.const_mul ((2 * c) ^ n)
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' h_zero h_upper
    (Eventually.of_forall (fun r =>
      mul_nonneg (pow_nonneg (Nat.cast_nonneg r) n) (hw.1 ⌊(r : ℝ) / c⌋₊)))
    ?_
  rw [Filter.eventually_atTop]
  refine ⟨⌈c⌉₊, fun r hr => ?_⟩
  have hc_le_r : c ≤ (r : ℝ) := le_trans (Nat.le_ceil c) (Nat.cast_le.mpr hr)
  have h_one_le_div : ((1 : ℕ) : ℝ) ≤ (r : ℝ) / c := by
    rw [Nat.cast_one]
    exact (one_le_div hc).mpr hc_le_r
  have hq_ge_one : 1 ≤ ⌊(r : ℝ) / c⌋₊ := Nat.le_floor h_one_le_div
  have hq_real_ge_one : (1 : ℝ) ≤ (⌊(r : ℝ) / c⌋₊ : ℝ) := Nat.one_le_cast.mpr hq_ge_one
  have h_div_lt : (r : ℝ) / c ≤ (⌊(r : ℝ) / c⌋₊ : ℝ) + 1 :=
    le_of_lt (Nat.lt_floor_add_one ((r : ℝ) / c))
  have hr_le : (r : ℝ) ≤ (2 * c) * (⌊(r : ℝ) / c⌋₊ : ℝ) := by
    have h_mul : (r : ℝ) ≤ ((⌊(r : ℝ) / c⌋₊ : ℝ) + 1) * c := (div_le_iff₀ hc).mp h_div_lt
    nlinarith
  have h_pow : (r : ℝ) ^ n ≤ ((2 * c) * (⌊(r : ℝ) / c⌋₊ : ℝ)) ^ n :=
    pow_le_pow_left₀ (Nat.cast_nonneg r) hr_le n
  calc (r : ℝ) ^ n * w ⌊(r : ℝ) / c⌋₊
    _ ≤ ((2 * c) * (⌊(r : ℝ) / c⌋₊ : ℝ)) ^ n * w ⌊(r : ℝ) / c⌋₊ :=
      mul_le_mul_of_nonneg_right h_pow (hw.1 ⌊(r : ℝ) / c⌋₊)
    _ = (2 * c) ^ n * (((⌊(r : ℝ) / c⌋₊ : ℕ) : ℝ) ^ n * w ⌊(r : ℝ) / c⌋₊) := by
      rw [mul_pow, mul_assoc]

/-- If $f_{\mathrm{LR}} \in \mathcal{D}_{\mathrm{super}}$ is non-increasing, then $r \mapsto f_{\mathrm{LR}}(r / 2)$
    belongs to $\mathcal{D}_{\mathrm{super}}$. -/
lemma isSuperpolynomialDecay_div_two {f_LR : ℕ → ℝ}
    (hf : IsSuperpolynomialDecay f_LR) (_hf_anti : Antitone f_LR) :
    IsSuperpolynomialDecay (fun r : ℕ => f_LR (r / 2)) := by
  refine ⟨fun r => hf.1 (r / 2), fun n => ?_⟩
  have h2_pos : 0 < (2 : ℕ) := by decide
  have h_zero : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 0) := tendsto_const_nhds
  have h_comp : Tendsto (fun r : ℕ => ((r / 2 : ℕ) : ℝ) ^ n * f_LR (r / 2)) atTop (𝓝 0) :=
    (hf.2 n).comp (tendsto_div_const_atTop h2_pos)
  have h_upper : Tendsto
      (fun r : ℕ => ((4 : ℕ) : ℝ) ^ n * (((r / 2 : ℕ) : ℝ) ^ n * f_LR (r / 2)))
      atTop (𝓝 0) := by
    simpa [mul_zero] using h_comp.const_mul (((4 : ℕ) : ℝ) ^ n)
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' h_zero h_upper
    (Eventually.of_forall (fun r => mul_nonneg (pow_nonneg (Nat.cast_nonneg r) n) (hf.1 (r / 2))))
    ?_
  rw [Filter.eventually_atTop]
  refine ⟨2, fun r hr => ?_⟩
  have hr_le_nat : r ≤ 4 * (r / 2) := by omega
  have hr_le_real : (r : ℝ) ≤ ((4 : ℕ) : ℝ) * ((r / 2 : ℕ) : ℝ) := by
    exact_mod_cast hr_le_nat
  have h_pow : (r : ℝ) ^ n ≤ (((4 : ℕ) : ℝ) * ((r / 2 : ℕ) : ℝ)) ^ n :=
    pow_le_pow_left₀ (Nat.cast_nonneg r) hr_le_real n
  calc (r : ℝ) ^ n * f_LR (r / 2)
    _ ≤ (((4 : ℕ) : ℝ) * ((r / 2 : ℕ) : ℝ)) ^ n * f_LR (r / 2) :=
      mul_le_mul_of_nonneg_right h_pow (hf.1 (r / 2))
    _ = ((4 : ℕ) : ℝ) ^ n * (((r / 2 : ℕ) : ℝ) ^ n * f_LR (r / 2)) := by
      rw [mul_pow, mul_assoc]

/-- Pointwise non-negativity of `fTilde C f r` for non-negative $f$. -/
lemma fTilde_nonneg (C : ℝ) {f : ℕ → ℝ} (hf : ∀ r, 0 ≤ f r) (r : ℕ) :
    0 ≤ fTilde C f r := by
  dsimp [fTilde]
  apply mul_nonneg (Nat.cast_nonneg r)
  apply tsum_nonneg
  intro q
  split_ifs
  · exact hf q
  · exact le_rfl

/-- **Bravyi–Hastings Tail Profile Closure (`isSuperpolynomialDecay_fTilde`)**:
    If $C > 0$ and $f \in \mathcal{D}_{\mathrm{super}}$, then the Bravyi–Hastings tail profile
    $\tilde{f}(r) = r \sum_{q > (r - 3)/(2C) - 3} f(q)$ belongs to $\mathcal{D}_{\mathrm{super}}$,
    and consequently $\max(f(r), \tilde{f}(r)) \in \mathcal{D}_{\mathrm{super}}$. -/
theorem isSuperpolynomialDecay_fTilde {C : ℝ} (hC : 0 < C)
    {f : ℕ → ℝ} (hf : IsSuperpolynomialDecay f) :
    IsSuperpolynomialDecay (fTilde C f) := by
  refine ⟨fTilde_nonneg C hf.1, fun n => ?_⟩
  have h_sum : Summable (fun q : ℕ => (q : ℝ) ^ (n + 2) * f q) :=
    summable_pow_mul_of_isSuperpolynomialDecay hf (n + 2)
  let S : ℝ := ∑' q : ℕ, (q : ℝ) ^ (n + 2) * f q
  let K : ℝ := 8 * C + 3
  have hK_pos : 0 < K := by dsimp [K]; linarith
  let M_const : ℝ := K ^ (n + 2) * S
  have h_zero : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 0) := tendsto_const_nhds
  have h_upper : Tendsto (fun r : ℕ => M_const * (r : ℝ)⁻¹) atTop (𝓝 0) := by
    simpa using (tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop).const_mul M_const
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' h_zero h_upper
    (Eventually.of_forall (fun r =>
      mul_nonneg (pow_nonneg (Nat.cast_nonneg r) n) (fTilde_nonneg C hf.1 r))) ?_
  filter_upwards [eventually_ge_atTop (Nat.ceil (8 * C + 4) + 1)] with r hr
  have hr_pos : (0 : ℝ) < (r : ℝ) := Nat.cast_pos.mpr (by omega)
  have hr_ge : 8 * C + 4 ≤ (r : ℝ) := by
    have h1 : (Nat.ceil (8 * C + 4) : ℝ) ≤ (r : ℝ) := by
      exact_mod_cast (by omega : Nat.ceil (8 * C + 4) ≤ r)
    linarith [Nat.le_ceil (8 * C + 4)]
  let g_r : ℕ → ℝ := fun q => if (q : ℝ) > ((r : ℝ) - 3) / (2 * C) - 3 then f q else 0
  have hg_nonneg : ∀ q : ℕ, 0 ≤ g_r q := by
    intro q
    dsimp [g_r]
    split_ifs
    · exact hf.1 q
    · exact le_rfl
  have h_term_bound : ∀ q : ℕ,
      (r : ℝ) ^ (n + 2) * g_r q ≤ K ^ (n + 2) * ((q : ℝ) ^ (n + 2) * f q) := by
    intro q
    dsimp [g_r]
    split_ifs with hq
    · have h2C_pos : (0 : ℝ) < 2 * C := by linarith
      have hq_gt_one : 1 < (q : ℝ) := by
        have h_div : 4 < ((r : ℝ) - 3) / (2 * C) := by
          rw [lt_div_iff₀ h2C_pos]
          linarith
        linarith
      have h_r_sub : (r : ℝ) - 3 < 2 * C * ((q : ℝ) + 3) := by
        have h1 : ((r : ℝ) - 3) / (2 * C) < (q : ℝ) + 3 := by linarith
        have h2 := (div_lt_iff₀ h2C_pos).mp h1
        linarith
      have h_r_le : (r : ℝ) ≤ K * (q : ℝ) := by
        dsimp [K]
        nlinarith
      calc (r : ℝ) ^ (n + 2) * f q
        _ ≤ (K * (q : ℝ)) ^ (n + 2) * f q := by
          apply mul_le_mul_of_nonneg_right _ (hf.1 q)
          exact pow_le_pow_left₀ (Nat.cast_nonneg r) h_r_le (n + 2)
        _ = K ^ (n + 2) * ((q : ℝ) ^ (n + 2) * f q) := by
          rw [mul_pow, mul_assoc]
    · rw [mul_zero]
      exact mul_nonneg (pow_nonneg (le_of_lt hK_pos) (n + 2))
        (mul_nonneg (pow_nonneg (Nat.cast_nonneg q) (n + 2)) (hf.1 q))
  have hf_sum : Summable f := summable_of_isSuperpolynomialDecay hf
  have hg_sum : Summable g_r :=
    Summable.of_nonneg_of_le hg_nonneg
      (fun q => by dsimp [g_r]; split_ifs <;> [exact le_rfl; exact hf.1 q]) hf_sum
  have h_tsum_le : (r : ℝ) ^ (n + 2) * (∑' q : ℕ, g_r q) ≤ M_const := by
    rw [← tsum_mul_left]
    calc ∑' q : ℕ, (r : ℝ) ^ (n + 2) * g_r q
      _ ≤ ∑' q : ℕ, K ^ (n + 2) * ((q : ℝ) ^ (n + 2) * f q) :=
        Summable.tsum_le_tsum h_term_bound (hg_sum.mul_left _) (h_sum.mul_left _)
      _ = K ^ (n + 2) * S := tsum_mul_left
      _ = M_const := rfl
  have hr_ne : (r : ℝ) ≠ 0 := ne_of_gt hr_pos
  have h_id : (r : ℝ) ^ n * fTilde C f r =
      (r : ℝ)⁻¹ * ((r : ℝ) ^ (n + 2) * (∑' q : ℕ, g_r q)) := by
    dsimp [fTilde, g_r]
    have h_alg : (r : ℝ) ^ n * ((r : ℝ) * ∑' q : ℕ, g_r q) =
        ((r : ℝ)⁻¹ * (r : ℝ)) * ((r : ℝ) ^ n * (r : ℝ) * ∑' q : ℕ, g_r q) := by
      rw [inv_mul_cancel₀ hr_ne, one_mul, mul_assoc]
    rw [h_alg]
    ring
  rw [h_id, mul_comm M_const (r : ℝ)⁻¹]
  exact mul_le_mul_of_nonneg_left h_tsum_le (inv_nonneg.mpr (le_of_lt hr_pos))
