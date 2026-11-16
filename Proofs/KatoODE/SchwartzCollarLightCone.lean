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

import Proofs.HastingsKomaLightCone.BareFrameBQLightConeAndTwoBlockNorm
import Proofs.KatoODE.ContinuationWeightKernel
import Proofs.KatoODE.LocalizedShortRangeDuhamel

open scoped Classical InnerProduct ComplexConjugate BigOperators Nat
open Filter Topology Asymptotics ContinuousLinearMap MeasureTheory
open KMSPinchedGibbs PerturbedThermalBarrier WeldedHierarchy WeldedHierarchy.BDLDecoder
open InhomogeneousMemoryChallenge

noncomputable section

set_option maxRecDepth 200000
set_option maxHeartbeats 800000

/-!
# Square-Root Collar Optimization and Schwartz Bochner Integration by Parts

Combines short-range collar Lieb–Robinson bounds with square-root truncation radius optimization (`bdlSchwartzRadiusProfile`, `bdlSchwartzCollarEnvelope`) to prove `norm_bochnerFilteredOp_interpolated_sub_condExp_schwartz_le`. Establishes the operator integration-by-parts identity relating `bandpassFilterWeight` and `bandpassContinuationWeight` under `bochnerFilteredOp`.

## References

* Part I, Section 6.2 (`subsec:bochner-lr`), Equation (68) (`eq:wBP-WBP-ibp`), Proposition 6.3 (`prop:bochner-time-convolution`)
-/

attribute [local irreducible] collarConstRCABDL bdlLambda qCodeBDL r0BDL mMaxBDL LatticeHamiltonian.s1

/-! ## 1. Superpolynomial Decay under Square-Root and Linear-Lower Compositions -/

/-- If `g : ℕ → ℝ` has superpolynomial decay, then `fun d : ℕ => g (Nat.sqrt d)` also has
    superpolynomial decay. -/
lemma isSuperpolynomialDecay_comp_sqrt {g : ℕ → ℝ} (hg : IsSuperpolynomialDecay g) :
    IsSuperpolynomialDecay (fun d : ℕ => g (Nat.sqrt d)) := by
  refine ⟨fun d => hg.1 (Nat.sqrt d), fun n => ?_⟩
  have h_tend : Tendsto Nat.sqrt atTop atTop :=
    Filter.tendsto_atTop_atTop.mpr (fun b => ⟨b * b, fun d hd => Nat.le_sqrt.mpr hd⟩)
  have h_comp : Tendsto
      (fun d : ℕ => ((Nat.sqrt d : ℕ) : ℝ) ^ (2 * n) * g (Nat.sqrt d)) atTop (𝓝 0) :=
    (hg.2 (2 * n)).comp h_tend
  have h_upper : Tendsto
      (fun d : ℕ => (4 : ℝ) ^ n * (((Nat.sqrt d : ℕ) : ℝ) ^ (2 * n) * g (Nat.sqrt d)))
      atTop (𝓝 0) := by
    simpa [mul_zero] using h_comp.const_mul ((4 : ℝ) ^ n)
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds h_upper
    (Eventually.of_forall fun d =>
      mul_nonneg (pow_nonneg (Nat.cast_nonneg d) n) (hg.1 (Nat.sqrt d))) ?_
  filter_upwards [Filter.eventually_ge_atTop 1] with d hd
  have h_sqrt_pos : 1 ≤ Nat.sqrt d := Nat.le_sqrt.mpr (by omega : 1 * 1 ≤ d)
  have h_lt := Nat.lt_succ_sqrt d
  have hd_le_nat : d ≤ 4 * (Nat.sqrt d * Nat.sqrt d) := by nlinarith
  have hd_le_real : (d : ℝ) ≤ 4 * ((Nat.sqrt d : ℕ) : ℝ) ^ 2 := by
    have h1 : (d : ℝ) ≤ ((4 * (Nat.sqrt d * Nat.sqrt d) : ℕ) : ℝ) := by exact_mod_cast hd_le_nat
    calc (d : ℝ)
      _ ≤ ((4 * (Nat.sqrt d * Nat.sqrt d) : ℕ) : ℝ) := h1
      _ = 4 * ((Nat.sqrt d : ℕ) : ℝ) ^ 2 := by push_cast; ring
  have h_pow : (d : ℝ) ^ n ≤ (4 * ((Nat.sqrt d : ℕ) : ℝ) ^ 2) ^ n :=
    pow_le_pow_left₀ (Nat.cast_nonneg d) hd_le_real n
  calc (d : ℝ) ^ n * g (Nat.sqrt d)
    _ ≤ (4 * ((Nat.sqrt d : ℕ) : ℝ) ^ 2) ^ n * g (Nat.sqrt d) :=
      mul_le_mul_of_nonneg_right h_pow (hg.1 (Nat.sqrt d))
    _ = (4 : ℝ) ^ n * (((Nat.sqrt d : ℕ) : ℝ) ^ (2 * n) * g (Nat.sqrt d)) := by
      rw [mul_pow, ← pow_mul, mul_assoc]

/-- If `g : ℕ → ℝ` has superpolynomial decay and `d : ℕ → ℕ` grows at least linearly
    (`∃ c ≥ 1, ∀ᶠ r in atTop, r ≤ c * d r`), then `fun r => g (d r)` has superpolynomial decay. -/
lemma isSuperpolynomialDecay_comp_linear_lower {g : ℕ → ℝ} (hg : IsSuperpolynomialDecay g)
    {d : ℕ → ℕ} (hd : ∃ c : ℕ, 1 ≤ c ∧ ∀ᶠ r in atTop, r ≤ c * d r) :
    IsSuperpolynomialDecay (fun r : ℕ => g (d r)) := by
  rcases hd with ⟨c, hc1, h_ev⟩
  refine ⟨fun r => hg.1 (d r), fun n => ?_⟩
  have h_tend : Tendsto d atTop atTop := by
    rw [Filter.tendsto_atTop_atTop]
    intro b
    rcases Filter.eventually_atTop.mp h_ev with ⟨N, hN⟩
    refine ⟨max N (c * b), fun r hr => ?_⟩
    have hrN : N ≤ r := le_of_max_le_left hr
    have hrcb : c * b ≤ r := le_of_max_le_right hr
    have h_le : c * b ≤ c * d r := le_trans hrcb (hN r hrN)
    exact Nat.le_of_mul_le_mul_left h_le (by omega)
  have h_comp : Tendsto (fun r : ℕ => ((d r : ℕ) : ℝ) ^ n * g (d r)) atTop (𝓝 0) :=
    (hg.2 n).comp h_tend
  have h_upper : Tendsto
      (fun r : ℕ => ((c : ℕ) : ℝ) ^ n * (((d r : ℕ) : ℝ) ^ n * g (d r))) atTop (𝓝 0) := by
    simpa [mul_zero] using h_comp.const_mul (((c : ℕ) : ℝ) ^ n)
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds h_upper
    (Eventually.of_forall fun r =>
      mul_nonneg (pow_nonneg (Nat.cast_nonneg r) n) (hg.1 (d r))) ?_
  filter_upwards [h_ev] with r hr
  have hr_real : (r : ℝ) ≤ (c : ℝ) * (d r : ℝ) := by exact_mod_cast hr
  have h_pow : (r : ℝ) ^ n ≤ ((c : ℝ) * (d r : ℝ)) ^ n :=
    pow_le_pow_left₀ (Nat.cast_nonneg r) hr_real n
  calc (r : ℝ) ^ n * g (d r)
    _ ≤ ((c : ℝ) * (d r : ℝ)) ^ n * g (d r) :=
      mul_le_mul_of_nonneg_right h_pow (hg.1 (d r))
    _ = ((c : ℕ) : ℝ) ^ n * (((d r : ℕ) : ℝ) ^ n * g (d r)) := by
      rw [mul_pow, mul_assoc]

/-- Elementary factorial bound: for all `R, m : ℕ`,
    $\exp(-R / 2) \le (e \cdot m!) / (1 + R / 2)^m$. -/
lemma exp_neg_div_two_le_mul_factorial_div_pow (R m : ℕ) :
    Real.exp (- (R : ℝ) / 2) ≤ (Real.exp 1 * (m.factorial : ℝ)) / (1 + (R : ℝ) / 2) ^ m := by
  let x : ℝ := 1 + (R : ℝ) / 2
  have hx_pos : 0 < x := by dsimp [x]; positivity
  have h_fac_pos : (0 : ℝ) < (m.factorial : ℝ) := Nat.cast_pos.mpr (Nat.factorial_pos m)
  have h_pow_exp : x ^ m ≤ Real.exp x * (m.factorial : ℝ) :=
    (div_le_iff₀ h_fac_pos).mp (Real.pow_div_factorial_le_exp x hx_pos.le m)
  rw [le_div_iff₀ (pow_pos hx_pos m)]
  calc Real.exp (- (R : ℝ) / 2) * x ^ m
    _ ≤ Real.exp (- (R : ℝ) / 2) * (Real.exp x * (m.factorial : ℝ)) :=
      mul_le_mul_of_nonneg_left h_pow_exp (Real.exp_nonneg _)
    _ = (Real.exp (- (R : ℝ) / 2) * Real.exp x) * (m.factorial : ℝ) := by ring
    _ = Real.exp 1 * (m.factorial : ℝ) := by
      rw [← Real.exp_add]
      congr 2
      dsimp [x]; ring

/-! ## 2. General Collar Bochner Light-Cone Bound (`norm_bochnerFilteredOp_sub_condExp_le_of_collar`) -/

/-- **General Collar Bochner Light-Cone Bound (`norm_bochnerFilteredOp_sub_condExp_le_of_collar`)**:
    Splits the Bochner time integral at $|t| \le T$ vs. $|t| \ge T$, applying
    `norm_heisenbergEvolve_sub_condExp_le_of_collar` on $[-T, T]$ and the trivial $2 \|O_X\|$ bound
    on the tail $\{t : T \le |t|\}$. -/
theorem norm_bochnerFilteredOp_sub_condExp_le_of_collar {D L : ℕ} [NeZero D] [NeZero L]
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    [∀ x, Nonempty (Site x)]
    (H : LatticeHamiltonian D L Site) {w : ℝ → ℂ} (hw : Integrable w)
    {X B : Finset (BoxD D L)} (hX : X.Nonempty) (hXB : X ⊆ B)
    {O_X : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site}
    (hO : IsSupportedOn Site X O_X)
    {d R : ℕ} (hR1 : 1 ≤ R) (hRd : R ≤ d)
    (h_collar : ∀ x ∈ X, ∀ y : BoxD D L, y ∉ B → d ≤ boxDist x y)
    (m : ℕ) {T : ℝ} (hT : 0 ≤ T) :
    ‖bochnerFilteredOp H.totalHamiltonian w O_X - condExp Site B (bochnerFilteredOp H.totalHamiltonian w O_X)‖ ≤
      ‖O_X‖ * ((∫ t : ℝ, ‖w t‖) * (4 * (B.card : ℝ) * T *
        ((X.card : ℝ) * Real.exp 1 * H.s1 0 * Real.exp (- (d : ℝ) / (R : ℝ)) *
          Real.exp (2 * Real.exp 1 * H.s1 0 * T) +
          H.s1 (m : ℝ) / (1 + (R : ℝ)) ^ m)) +
        2 * ∫ t in {t : ℝ | T ≤ |t|}, ‖w t‖) := by
  let C_short : ℝ := 4 * (B.card : ℝ) * T *
    ((X.card : ℝ) * Real.exp 1 * H.s1 0 * Real.exp (- (d : ℝ) / (R : ℝ)) *
      Real.exp (2 * Real.exp 1 * H.s1 0 * T) +
      H.s1 (m : ℝ) / (1 + (R : ℝ)) ^ m)
  have hs0_nn : 0 ≤ H.s1 0 := H.s1_nonneg 0
  have hsm_nn : 0 ≤ H.s1 (m : ℝ) := H.s1_nonneg (m : ℝ)
  have hC_short_nn : 0 ≤ C_short := by dsimp [C_short]; positivity
  let S_tail : Set ℝ := {t : ℝ | T ≤ |t|}
  have hS_meas : MeasurableSet S_tail := measurableSet_le measurable_const continuous_abs.measurable
  let b : ℝ → ℝ := fun t =>
    (‖O_X‖ * C_short) + (2 * ‖O_X‖) * S_tail.indicator (fun _ : ℝ => (1 : ℝ)) t
  have h_int_flow : Integrable (fun t : ℝ => w t • heisenbergFlow H.totalHamiltonian t O_X) :=
    integrable_smul_heisenbergFlow_of_integrable H.isSelfAdjoint_totalHamiltonian hw O_X
  have h_b_eq : (fun t : ℝ => ‖w t‖ * b t) =
      (fun t : ℝ => (‖O_X‖ * C_short) * ‖w t‖ +
        (2 * ‖O_X‖) * S_tail.indicator (fun τ : ℝ => ‖w τ‖) t) := by
    ext t
    dsimp [b]
    by_cases ht : t ∈ S_tail
    · rw [Set.indicator_of_mem ht, Set.indicator_of_mem ht]; ring
    · rw [Set.indicator_of_notMem ht, Set.indicator_of_notMem ht]; ring
  have h_int_b : Integrable (fun t : ℝ => ‖w t‖ * b t) := by
    rw [h_b_eq]
    exact (hw.norm.const_mul (‖O_X‖ * C_short)).add
      ((hw.norm.indicator hS_meas).const_mul (2 * ‖O_X‖))
  have h_pt : ∀ t : ℝ,
      ‖heisenbergFlow H.totalHamiltonian t O_X - condExp Site B (heisenbergFlow H.totalHamiltonian t O_X)‖ ≤ b t := by
    intro t
    dsimp [b]
    by_cases ht : |t| ≤ T
    · have h_lr := norm_heisenbergEvolve_sub_condExp_le_of_collar H hX hXB hO
        hR1 hRd h_collar m hT (abs_le.mp ht)
      have h_ind_nn : 0 ≤ (2 * ‖O_X‖) * S_tail.indicator (fun _ : ℝ => (1 : ℝ)) t :=
        mul_nonneg (by positivity) (Set.indicator_nonneg (fun _ _ => zero_le_one) t)
      change ‖heisenbergFlow H.totalHamiltonian t O_X - condExp Site B (heisenbergFlow H.totalHamiltonian t O_X)‖ ≤
        4 * ‖O_X‖ * (B.card : ℝ) * T * _ at h_lr
      dsimp [C_short]
      linarith
    · have ht_mem : t ∈ S_tail := le_of_not_ge ht
      rw [Set.indicator_of_mem ht_mem, mul_one]
      have h_ce := norm_sub_condExp_le_two_mul_norm B (heisenbergFlow H.totalHamiltonian t O_X)
      have h_hf := norm_heisenbergFlow_le_self H.isSelfAdjoint_totalHamiltonian t O_X
      have h_nn : 0 ≤ ‖O_X‖ * C_short := mul_nonneg (norm_nonneg O_X) hC_short_nn
      linarith
  have h_int_le : (∫ t : ℝ, ‖w t‖ * b t) ≤
      ‖O_X‖ * ((∫ t : ℝ, ‖w t‖) * C_short + 2 * ∫ t in S_tail, ‖w t‖) := by
    rw [h_b_eq, integral_add (hw.norm.const_mul (‖O_X‖ * C_short))
      ((hw.norm.indicator hS_meas).const_mul (2 * ‖O_X‖)),
      integral_const_mul, integral_const_mul, MeasureTheory.integral_indicator hS_meas]
    ring_nf; exact le_rfl
  exact norm_bochnerFilteredOp_sub_condExp_le H.totalHamiltonian w O_X B b _ h_int_flow h_int_b h_pt h_int_le

/-! ## 3. Calibrated Collar Envelope (`bdlSchwartzCollarEnvelope`) for `interpolatedLatticeHamiltonian` -/

/-- Calibrated time-cutoff velocity scale $c_T := 1 / (4 e (S_0 + 1)) > 0$. -/
def bdlSchwartzTimeScale (f : ℕ → ℝ) : ℝ :=
  1 / (4 * Real.exp 1 * (bdlInhomogeneousInterpolatedS1Bound f 0 + 1))

lemma bdlSchwartzTimeScale_pos {f : ℕ → ℝ} (hf : IsSuperpolynomialDecay f) :
    0 < bdlSchwartzTimeScale f := by
  unfold bdlSchwartzTimeScale
  have := bdlInhomogeneousInterpolatedS1Bound_nonneg hf 0
  positivity

/-- Calibrated moment constant $C_{\mathrm{LC}}(m) := e^2 S_0 m! + S_m$ at order $m \in \mathbb{N}$. -/
def bdlSchwartzLightConeConst (f : ℕ → ℝ) (m : ℕ) : ℝ :=
  Real.exp 2 * bdlInhomogeneousInterpolatedS1Bound f 0 * (m.factorial : ℝ) +
    bdlInhomogeneousInterpolatedS1Bound f (m : ℝ)

lemma bdlSchwartzLightConeConst_nonneg {f : ℕ → ℝ} (hf : IsSuperpolynomialDecay f) (m : ℕ) :
    0 ≤ bdlSchwartzLightConeConst f m := by
  unfold bdlSchwartzLightConeConst
  have h0 := bdlInhomogeneousInterpolatedS1Bound_nonneg hf 0
  have hm := bdlInhomogeneousInterpolatedS1Bound_nonneg hf (m : ℝ)
  positivity

/-- Single-variable radius profile at truncation radius $R \in \mathbb{N}$. -/
def bdlSchwartzRadiusProfile (w : ℝ → ℂ) (f : ℕ → ℝ) (R : ℕ) : ℝ :=
  (∫ t : ℝ, ‖w t‖) * (4 * bdlSchwartzTimeScale f * (R : ℝ) *
    hastingsKomaSuperpolyEnvelope (bdlSchwartzLightConeConst f) (fun k => k) R) +
  2 * ∫ t in {t : ℝ | bdlSchwartzTimeScale f * (R : ℝ) ≤ |t|}, ‖w t‖

lemma bdlSchwartzRadiusProfile_nonneg (w : ℝ → ℂ) {f : ℕ → ℝ} (hf : IsSuperpolynomialDecay f)
    (R : ℕ) : 0 ≤ bdlSchwartzRadiusProfile w f R := by
  unfold bdlSchwartzRadiusProfile
  have hw_nn : 0 ≤ ∫ t : ℝ, ‖w t‖ := integral_nonneg fun _ => norm_nonneg _
  have hw_tail_nn : 0 ≤ ∫ t in {t : ℝ | bdlSchwartzTimeScale f * (R : ℝ) ≤ |t|}, ‖w t‖ :=
    setIntegral_nonneg (measurableSet_le measurable_const continuous_abs.measurable)
      (fun _ _ => norm_nonneg _)
  have hc_pos := (bdlSchwartzTimeScale_pos hf).le
  have h_hk := hastingsKomaSuperpolyEnvelope_nonneg (bdlSchwartzLightConeConst_nonneg hf)
    (fun k => k) R
  positivity

theorem isSuperpolynomialDecay_bdlSchwartzRadiusProfile {w : ℝ → ℂ} {f : ℕ → ℝ}
    (hf : IsSuperpolynomialDecay f)
    (hw_tail : ∀ {c : ℝ}, 0 < c →
      IsSuperpolynomialDecay (fun R : ℕ => ∫ t in {t : ℝ | c * (R : ℝ) ≤ |t|}, ‖w t‖)) :
    IsSuperpolynomialDecay (bdlSchwartzRadiusProfile w f) := by
  have h_hk : IsSuperpolynomialDecay
      (hastingsKomaSuperpolyEnvelope (bdlSchwartzLightConeConst f) (fun k => k)) :=
    isSuperpolynomialDecay_hastingsKomaSuperpolyEnvelope
      (bdlSchwartzLightConeConst_nonneg hf)
      ⟨1, le_rfl, Eventually.of_forall fun r => by omega⟩
  have h_pow1 : IsSuperpolynomialDecay
      (fun R : ℕ => (R : ℝ) *
        hastingsKomaSuperpolyEnvelope (bdlSchwartzLightConeConst f) (fun k => k) R) := by
    simpa [pow_one] using isSuperpolynomialDecay_mul_pow h_hk 1
  have hw_nn : 0 ≤ ∫ t : ℝ, ‖w t‖ := integral_nonneg fun _ => norm_nonneg _
  have hc_pos := bdlSchwartzTimeScale_pos hf
  have h_term1 : IsSuperpolynomialDecay
      (fun R : ℕ => (∫ t : ℝ, ‖w t‖) * (4 * bdlSchwartzTimeScale f * (R : ℝ) *
        hastingsKomaSuperpolyEnvelope (bdlSchwartzLightConeConst f) (fun k => k) R)) := by
    have h1 := isSuperpolynomialDecay_const_mul h_pow1
      (show 0 ≤ (∫ t : ℝ, ‖w t‖) * (4 * bdlSchwartzTimeScale f) by positivity)
    convert h1 using 1; ext R; ring
  have h_term2 : IsSuperpolynomialDecay
      (fun R : ℕ => 2 * ∫ t in {t : ℝ | bdlSchwartzTimeScale f * (R : ℝ) ≤ |t|}, ‖w t‖) :=
    isSuperpolynomialDecay_const_mul (hw_tail hc_pos) zero_le_two
  exact isSuperpolynomialDecay_add h_term1 h_term2

/-- Collar envelope at distance profile `d : ℕ → ℕ`, setting $R = \lfloor\sqrt{d(r)}\rfloor$. -/
def bdlSchwartzCollarEnvelope (w : ℝ → ℂ) (f : ℕ → ℝ) (d : ℕ → ℕ) (r : ℕ) : ℝ :=
  bdlSchwartzRadiusProfile w f (Nat.sqrt (d r))

lemma bdlSchwartzCollarEnvelope_nonneg (w : ℝ → ℂ) {f : ℕ → ℝ} (hf : IsSuperpolynomialDecay f)
    (d : ℕ → ℕ) (r : ℕ) : 0 ≤ bdlSchwartzCollarEnvelope w f d r :=
  bdlSchwartzRadiusProfile_nonneg w hf (Nat.sqrt (d r))

theorem isSuperpolynomialDecay_bdlSchwartzCollarEnvelope {w : ℝ → ℂ} {f : ℕ → ℝ}
    (hf : IsSuperpolynomialDecay f)
    (hw_tail : ∀ {c : ℝ}, 0 < c →
      IsSuperpolynomialDecay (fun R : ℕ => ∫ t in {t : ℝ | c * (R : ℝ) ≤ |t|}, ‖w t‖))
    {d : ℕ → ℕ} (hd : ∃ c : ℕ, 1 ≤ c ∧ ∀ᶠ r in atTop, r ≤ c * d r) :
    IsSuperpolynomialDecay (bdlSchwartzCollarEnvelope w f d) :=
  isSuperpolynomialDecay_comp_linear_lower
    (isSuperpolynomialDecay_comp_sqrt (isSuperpolynomialDecay_bdlSchwartzRadiusProfile hf hw_tail))
    hd

/-- **Single-Operator Collar Bochner Light-Cone Bound for `interpolatedLatticeHamiltonian`
    (`norm_bochnerFilteredOp_interpolated_sub_condExp_schwartz_le`)**. -/
theorem norm_bochnerFilteredOp_interpolated_sub_condExp_schwartz_le
    {L : ℕ} [NeZero L]
    {c_star C β_c c_F η_mem c_mem J s : ℝ} {w : ℝ → ℂ} {f : ℕ → ℝ}
    (mem : Inhomogeneous3DMemoryRealization L qCodeBDL r0BDL mMaxBDL c_star C β_c c_F η_mem c_mem)
    (V : QuasiLocalPerturbation 3 L (UniformSite3D L (CodeSlotConfig qCodeBDL)))
    (hw : Integrable w)
    (hJ0 : 0 ≤ J) (hJ1 : J ≤ 1) (hs : s ∈ Set.Icc (-1 : ℝ) 1)
    (hf : IsSuperpolynomialDecay f) (hV : V.SatisfiesDecayBound J f)
    {X B : Finset (Box3D L)} (hX : X.Nonempty) (hXB : X ⊆ B)
    (d : ℕ → ℕ) (r : ℕ) (hd_pos : 0 < d r)
    (h_collar : ∀ x ∈ X, ∀ y : Box3D L, y ∉ B → d r ≤ boxDist x y)
    (O_X : ManyBodyHilbertSpace (UniformSite3D L (CodeSlotConfig qCodeBDL)) →L[ℂ]
      ManyBodyHilbertSpace (UniformSite3D L (CodeSlotConfig qCodeBDL)))
    (hO_X : IsSupportedOn (UniformSite3D L (CodeSlotConfig qCodeBDL)) X O_X) :
    let H_s := mem.sys.H0 + (scaleQuasiLocalPerturbation s V).totalPerturbation
    ‖bochnerFilteredOp H_s w O_X -
      condExp (UniformSite3D L (CodeSlotConfig qCodeBDL)) B
        (bochnerFilteredOp H_s w O_X)‖ ≤
      ((X.card : ℝ) * (B.card : ℝ) * bdlSchwartzCollarEnvelope w f d r) * ‖O_X‖ := by
  intro H_s
  haveI : NeZero 3 := ⟨by decide⟩
  let H_lat := interpolatedLatticeHamiltonian mem.sys V s
  have hHs_eq : H_s = H_lat.totalHamiltonian := by
    dsimp [H_s, H_lat]
    rw [interpolatedLatticeHamiltonian_H_tot, interpolatedHamiltonianOp,
      scaleQuasiLocalPerturbation_V_tot]
  rw [hHs_eq]
  let R : ℕ := Nat.sqrt (d r)
  have hR1 : 1 ≤ R := Nat.le_sqrt.mpr (by omega : 1 * 1 ≤ d r)
  have hRd : R ≤ d r := Nat.sqrt_le_self (d r)
  have hR_pos : (0 : ℝ) < (R : ℝ) := by exact_mod_cast (by omega : 0 < R)
  have hX_card1 : (1 : ℝ) ≤ (X.card : ℝ) := by
    exact_mod_cast Finset.card_pos.mpr hX
  have hB_card1 : (1 : ℝ) ≤ (B.card : ℝ) := by
    exact_mod_cast Finset.card_pos.mpr (hX.mono hXB)
  have hXB_card1 : (1 : ℝ) ≤ (X.card : ℝ) * (B.card : ℝ) :=
    one_le_mul_of_one_le_of_one_le hX_card1 hB_card1
  let c_T : ℝ := bdlSchwartzTimeScale f
  let T : ℝ := c_T * (R : ℝ)
  have hc_pos : 0 < c_T := bdlSchwartzTimeScale_pos hf
  have hT_nn : 0 ≤ T := by dsimp [T]; positivity
  let I_tail : ℝ := ∫ t in {t : ℝ | T ≤ |t|}, ‖w t‖
  have hI_tail_nn : 0 ≤ I_tail :=
    setIntegral_nonneg (measurableSet_le measurable_const continuous_abs.measurable)
      (fun _ _ => norm_nonneg _)
  have hw_nn : 0 ≤ ∫ t : ℝ, ‖w t‖ := integral_nonneg fun _ => norm_nonneg _
  let Y : ℝ := ‖bochnerFilteredOp H_lat.totalHamiltonian w O_X -
    condExp (UniformSite3D L (CodeSlotConfig qCodeBDL)) B (bochnerFilteredOp H_lat.totalHamiltonian w O_X)‖
  let K_mult : ℝ := ‖O_X‖ * (X.card : ℝ) * (B.card : ℝ) * (∫ t : ℝ, ‖w t‖) * (4 * c_T * (R : ℝ))
  have hK_nn : 0 ≤ K_mult := by dsimp [K_mult]; positivity
  have h_forall_m : ∀ m : ℕ,
      Y - ‖O_X‖ * (2 * I_tail) ≤
        K_mult * (bdlSchwartzLightConeConst f m / (1 + (R : ℝ) / 2) ^ m) := by
    intro m
    have h_col := norm_bochnerFilteredOp_sub_condExp_le_of_collar H_lat hw hX hXB hO_X
      hR1 hRd h_collar m hT_nn
    have hs0_le : H_lat.s1 0 ≤ bdlInhomogeneousInterpolatedS1Bound f 0 :=
      (interpolatedLatticeHamiltonian_s1_inhomogeneous_le mem V hJ0 hJ1 (abs_le.mpr hs)
        hf hV le_rfl).2
    have hsm_le : H_lat.s1 (m : ℝ) ≤ bdlInhomogeneousInterpolatedS1Bound f (m : ℝ) :=
      (interpolatedLatticeHamiltonian_s1_inhomogeneous_le mem V hJ0 hJ1 (abs_le.mpr hs)
        hf hV (Nat.cast_nonneg m)).2
    have hs0_nn : 0 ≤ H_lat.s1 0 := H_lat.s1_nonneg 0
    have hsm_nn : 0 ≤ H_lat.s1 (m : ℝ) := H_lat.s1_nonneg (m : ℝ)
    have hS0_nn : 0 ≤ bdlInhomogeneousInterpolatedS1Bound f 0 :=
      bdlInhomogeneousInterpolatedS1Bound_nonneg hf 0
    have hR_div : (R : ℝ) ≤ (d r : ℝ) / (R : ℝ) := by
      rw [le_div_iff₀ hR_pos]
      exact_mod_cast Nat.sqrt_le (d r)
    have h_vel : 2 * Real.exp 1 * H_lat.s1 0 * T ≤ (R : ℝ) / 2 := by
      dsimp [T, c_T, bdlSchwartzTimeScale]
      have h_denom_pos : 0 < 4 * Real.exp 1 * (bdlInhomogeneousInterpolatedS1Bound f 0 + 1) := by
        positivity
      rw [show 2 * Real.exp 1 * H_lat.s1 0 *
            (1 / (4 * Real.exp 1 * (bdlInhomogeneousInterpolatedS1Bound f 0 + 1)) * (R : ℝ)) =
          (2 * Real.exp 1 * H_lat.s1 0 * (R : ℝ)) /
            (4 * Real.exp 1 * (bdlInhomogeneousInterpolatedS1Bound f 0 + 1)) by ring]
      rw [div_le_div_iff₀ h_denom_pos zero_lt_two]
      have h_le : H_lat.s1 0 ≤ bdlInhomogeneousInterpolatedS1Bound f 0 + 1 := by linarith
      calc (2 * Real.exp 1 * H_lat.s1 0 * (R : ℝ)) * 2
        _ = (4 * Real.exp 1 * (R : ℝ)) * H_lat.s1 0 := by ring
        _ ≤ (4 * Real.exp 1 * (R : ℝ)) * (bdlInhomogeneousInterpolatedS1Bound f 0 + 1) :=
          mul_le_mul_of_nonneg_left h_le (by positivity)
        _ = (R : ℝ) * (4 * Real.exp 1 * (bdlInhomogeneousInterpolatedS1Bound f 0 + 1)) := by ring
    have h_exp_prod :
        Real.exp (- (d r : ℝ) / (R : ℝ)) * Real.exp (2 * Real.exp 1 * H_lat.s1 0 * T) ≤
          (Real.exp 1 * (m.factorial : ℝ)) / (1 + (R : ℝ) / 2) ^ m := by
      rw [← Real.exp_add]
      exact le_trans (Real.exp_le_exp.mpr (by rw [neg_div, neg_div]; linarith))
        (exp_neg_div_two_le_mul_factorial_div_pow R m)
    have h_denom_pos : (0 : ℝ) < (1 + (R : ℝ) / 2) ^ m := by positivity
    have h_pow_mono : (1 + (R : ℝ) / 2) ^ m ≤ (1 + (R : ℝ)) ^ m :=
      pow_le_pow_left₀ (by positivity) (by linarith) m
    have h_term1 :
        (X.card : ℝ) * Real.exp 1 * H_lat.s1 0 * Real.exp (- (d r : ℝ) / (R : ℝ)) *
            Real.exp (2 * Real.exp 1 * H_lat.s1 0 * T) ≤
          (X.card : ℝ) *
            ((Real.exp 2 * bdlInhomogeneousInterpolatedS1Bound f 0 * (m.factorial : ℝ)) /
              (1 + (R : ℝ) / 2) ^ m) := by
      have h1 : Real.exp 1 * H_lat.s1 0 ≤ Real.exp 1 * bdlInhomogeneousInterpolatedS1Bound f 0 :=
        mul_le_mul_of_nonneg_left hs0_le (Real.exp_nonneg 1)
      have h2 := mul_le_mul h1 h_exp_prod (by positivity) (by positivity)
      have h_e2 : Real.exp 1 * Real.exp 1 = Real.exp 2 := by
        rw [← Real.exp_add]; norm_num
      calc (X.card : ℝ) * Real.exp 1 * H_lat.s1 0 * Real.exp (- (d r : ℝ) / (R : ℝ)) *
              Real.exp (2 * Real.exp 1 * H_lat.s1 0 * T)
        _ = (X.card : ℝ) * ((Real.exp 1 * H_lat.s1 0) *
              (Real.exp (- (d r : ℝ) / (R : ℝ)) * Real.exp (2 * Real.exp 1 * H_lat.s1 0 * T))) := by
          ring
        _ ≤ (X.card : ℝ) * ((Real.exp 1 * bdlInhomogeneousInterpolatedS1Bound f 0) *
              ((Real.exp 1 * (m.factorial : ℝ)) / (1 + (R : ℝ) / 2) ^ m)) :=
          mul_le_mul_of_nonneg_left h2 (by positivity)
        _ = (X.card : ℝ) *
              (((Real.exp 1 * Real.exp 1) * bdlInhomogeneousInterpolatedS1Bound f 0 *
                (m.factorial : ℝ)) / (1 + (R : ℝ) / 2) ^ m) := by ring
        _ = (X.card : ℝ) *
              ((Real.exp 2 * bdlInhomogeneousInterpolatedS1Bound f 0 * (m.factorial : ℝ)) /
                (1 + (R : ℝ) / 2) ^ m) := by rw [h_e2]
    have h_term2 :
        H_lat.s1 (m : ℝ) / (1 + (R : ℝ)) ^ m ≤
          (X.card : ℝ) * (bdlInhomogeneousInterpolatedS1Bound f (m : ℝ) / (1 + (R : ℝ) / 2) ^ m) := by
      have h_div1 : H_lat.s1 (m : ℝ) / (1 + (R : ℝ)) ^ m ≤
          H_lat.s1 (m : ℝ) / (1 + (R : ℝ) / 2) ^ m :=
        div_le_div_of_nonneg_left hsm_nn h_denom_pos h_pow_mono
      have h_div2 : H_lat.s1 (m : ℝ) / (1 + (R : ℝ) / 2) ^ m ≤
          bdlInhomogeneousInterpolatedS1Bound f (m : ℝ) / (1 + (R : ℝ) / 2) ^ m :=
        div_le_div_of_nonneg_right hsm_le h_denom_pos.le
      exact le_trans (le_trans h_div1 h_div2)
        (le_mul_of_one_le_left
          (div_nonneg (bdlInhomogeneousInterpolatedS1Bound_nonneg hf (m : ℝ)) h_denom_pos.le)
          hX_card1)
    have h_inner :
        (X.card : ℝ) * Real.exp 1 * H_lat.s1 0 * Real.exp (- (d r : ℝ) / (R : ℝ)) *
            Real.exp (2 * Real.exp 1 * H_lat.s1 0 * T) +
          H_lat.s1 (m : ℝ) / (1 + (R : ℝ)) ^ m ≤
        (X.card : ℝ) * (bdlSchwartzLightConeConst f m / (1 + (R : ℝ) / 2) ^ m) := by
      calc _
        _ ≤ (X.card : ℝ) *
              ((Real.exp 2 * bdlInhomogeneousInterpolatedS1Bound f 0 * (m.factorial : ℝ)) /
                (1 + (R : ℝ) / 2) ^ m) +
            (X.card : ℝ) *
              (bdlInhomogeneousInterpolatedS1Bound f (m : ℝ) / (1 + (R : ℝ) / 2) ^ m) :=
          add_le_add h_term1 h_term2
        _ = (X.card : ℝ) * (bdlSchwartzLightConeConst f m / (1 + (R : ℝ) / 2) ^ m) := by
          unfold bdlSchwartzLightConeConst; ring
    have h_mult_inner := mul_le_mul_of_nonneg_left h_inner
      (show 0 ≤ ‖O_X‖ * (∫ t : ℝ, ‖w t‖) * (4 * (B.card : ℝ) * T) by positivity)
    change Y ≤ ‖O_X‖ * ((∫ t : ℝ, ‖w t‖) * (4 * (B.card : ℝ) * T * _) + 2 * I_tail) at h_col
    dsimp [K_mult, T] at h_mult_inner ⊢
    linarith
  have h_env := le_mul_hastingsKomaSuperpolyEnvelope_of_forall
    (C := bdlSchwartzLightConeConst f) (d := fun k => k) (r := R) h_forall_m
  have h_tail_scale : ‖O_X‖ * (2 * I_tail) ≤
      ((X.card : ℝ) * (B.card : ℝ)) * (‖O_X‖ * (2 * I_tail)) :=
    le_mul_of_one_le_left (by positivity) hXB_card1
  change Y ≤ _
  unfold bdlSchwartzCollarEnvelope bdlSchwartzRadiusProfile
  dsimp [K_mult, I_tail, T, c_T, R] at h_env h_tail_scale ⊢
  linarith

/-- **Integration-by-Parts Identity for `bochnerFilteredOp H_s w_BP Q_u - Q_u`**:
    When `[H0, Q_u] = 0`,
    $\mathcal{F}_{w_{\mathrm{BP}}}^{H_0 + V_{\mathrm{tot}}}(Q_u) - Q_u =
      i \cdot \mathcal{F}_{W_{\mathrm{BP}}}^{H_0 + V_{\mathrm{tot}}}([V_{\mathrm{tot}}, Q_u])$. -/
theorem bochnerFilteredOp_w_BP_sub_self_eq_I_smul_bochnerFilteredOp_W_BP
    {D L : ℕ} {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    {H0 totalPerturbation Q_u : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site}
    (hH_sa : IsSelfAdjoint (H0 + totalPerturbation)) (h_comm : Commute H0 Q_u) :
    bochnerFilteredOp (H0 + totalPerturbation) bandpassFilterWeight Q_u - Q_u =
      (Complex.I : ℂ) • bochnerFilteredOp (H0 + totalPerturbation) bandpassContinuationWeight (opCommutator totalPerturbation Q_u) := by
  let H_s := H0 + totalPerturbation
  let G : ℝ → (ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site) :=
    fun τ => (Complex.I : ℂ) • heisenbergFlow H_s τ (opCommutator totalPerturbation Q_u)
  have hG_cont : Continuous G :=
    (continuous_heisenbergFlow H_s (opCommutator totalPerturbation Q_u)).const_smul (Complex.I : ℂ)
  have hG_bound : ∀ τ : ℝ, ‖G τ‖ ≤ ‖opCommutator totalPerturbation Q_u‖ := by
    intro τ
    dsimp [G]
    rw [norm_smul, Complex.norm_I, one_mul]
    exact norm_heisenbergFlow_le_self hH_sa τ (opCommutator totalPerturbation Q_u)
  have hQ_one : (∫ t : ℝ, bandpassFilterWeight t • Q_u) = Q_u := by
    rw [integral_smul_const, integral_w_BP_eq_one, one_smul]
  have h_int1 : Integrable (fun t : ℝ => bandpassFilterWeight t • heisenbergFlow H_s t Q_u) :=
    integrable_smul_heisenbergFlow_of_integrable hH_sa integrable_w_BP Q_u
  have h_int2 : Integrable (fun t : ℝ => bandpassFilterWeight t • Q_u) := integrable_w_BP.smul_const Q_u
  have h_sub_eq : bochnerFilteredOp H_s bandpassFilterWeight Q_u - Q_u =
      ∫ t : ℝ, bandpassFilterWeight t • (∫ τ in (0 : ℝ)..t, G τ) := by
    calc bochnerFilteredOp H_s bandpassFilterWeight Q_u - Q_u
      _ = (∫ t : ℝ, bandpassFilterWeight t • heisenbergFlow H_s t Q_u) - ∫ t : ℝ, bandpassFilterWeight t • Q_u := by
        unfold bochnerFilteredOp; rw [hQ_one]
      _ = ∫ t : ℝ, (bandpassFilterWeight t • heisenbergFlow H_s t Q_u - bandpassFilterWeight t • Q_u) :=
        (integral_sub h_int1 h_int2).symm
      _ = ∫ t : ℝ, bandpassFilterWeight t • (∫ τ in (0 : ℝ)..t, G τ) := by
        congr 1; funext t
        have h_ftc := intervalIntegral.integral_eq_sub_of_hasDerivAt
          (f := fun τ => heisenbergFlow H_s τ Q_u) (f' := G)
          (fun τ _ => hasDerivAt_heisenbergFlow_of_commute_left (totalPerturbation := totalPerturbation) h_comm τ)
          (hG_cont.intervalIntegrable 0 t)
        have h0 : heisenbergFlow H_s 0 Q_u = Q_u := by
          unfold heisenbergFlow; rw [neg_zero, timeEvolutionOp_zero, one_mul, mul_one]
        rw [h_ftc]; (try dsimp only); rw [h0, smul_sub]
  rw [h_sub_eq,
    integral_w_BP_smul_intervalIntegral_eq_integral_W_BP_smul G hG_cont
      ‖opCommutator totalPerturbation Q_u‖ hG_bound]
  unfold bochnerFilteredOp
  rw [← integral_smul (Complex.I : ℂ)]
  congr 1; funext τ; dsimp [G]
  exact smul_comm (bandpassContinuationWeight τ) (Complex.I : ℂ) _

end
