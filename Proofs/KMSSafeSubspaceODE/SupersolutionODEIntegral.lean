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

import Proofs.KMSSafeSubspaceODE.KMSSkewSymmetryAndDirichlet

open scoped Classical InnerProduct ComplexConjugate BigOperators
open Filter Topology Asymptotics ContinuousLinearMap

noncomputable section

/-!
# Nonlinear Square-Root Grönwall ODE Integration and KMS Generator Derivative Inequality

Analyzes the regularized comparison supersolution `kmsCompFunc` (`hasDerivAt_kmsCompFunc`, `kmsCompFunc_sqrt_and_deriv_ge`) and proves the nonlinear square-root Grönwall differential inequality bound (`kms_gronwall_ode_integral_bound`) together with the KMS Heisenberg–Lindblad generator derivative inequality (`kms_lindblad_generator_deriv_ineq`).

## References

* Part I, Section 5.5 (`subsec:unperturbed-kms-lifetime`), Theorem 5.8 (`thm:unperturbed-kms-lifetime`)
* Part II, Section 6.2 (`subsec:kms-gronwall`), Theorem 6.2 (`thm:kms-gronwall-bare`)
* Part II, Section 6.3 (`subsec:main-theorems`), Theorem 6.5 (`thm:main-D`)
-/

/-- If a differentiable function $h : \mathbb{R} \to \mathbb{R}$ on $[0, s_1]$ achieves its maximum on
    $[0, s_1]$ at $s_0 \in (0, s_1]$, then its derivative $h'$ at $s_0$ satisfies $0 \le h'$. -/
lemma not_neg_deriv_at_right_of_isMaxOn {h : ℝ → ℝ} {s₀ s₁ h' : ℝ}
    (hs₀_pos : 0 < s₀) (hs₀_le : s₀ ≤ s₁)
    (hmax : ∀ x ∈ Set.Icc 0 s₁, h x ≤ h s₀)
    (hderiv : HasDerivAt h h' s₀) :
    0 ≤ h' := by
  by_contra! hh'
  have h_tendsto := hasDerivAt_iff_tendsto.mp hderiv
  have h_ev := Metric.tendsto_nhds.mp h_tendsto (-h' / 2) (by linarith)
  rcases Metric.eventually_nhds_iff.mp h_ev with ⟨r, hr_pos, hr⟩
  let η := min (s₀ / 2) (r / 2)
  have hη_pos : 0 < η := lt_min (by linarith) (by linarith)
  have hη_le_s₀ : η ≤ s₀ / 2 := min_le_left _ _
  have hη_le_r : η ≤ r / 2 := min_le_right _ _
  let y := s₀ - η
  have hy_mem : y ∈ Set.Icc 0 s₁ := ⟨by linarith, by linarith⟩
  have hy_le : h y ≤ h s₀ := hmax y hy_mem
  have hy_sub : y - s₀ = -η := by ring
  have hy_norm : ‖y - s₀‖ = η := by
    rw [hy_sub, norm_neg, Real.norm_of_nonneg (le_of_lt hη_pos)]
  have hy_dist : dist y s₀ < r := by
    rw [Real.dist_eq, ← Real.norm_eq_abs, hy_norm]
    linarith
  have h_bound := hr hy_dist
  have h_nonneg : 0 ≤ ‖y - s₀‖⁻¹ * ‖h y - h s₀ - (y - s₀) • h'‖ := by positivity
  rw [Real.dist_0_eq_abs, abs_of_nonneg h_nonneg, hy_norm, smul_eq_mul, hy_sub] at h_bound
  have h_mul : ‖h y - h s₀ - (-η * h')‖ < η * (-h' / 2) := by
    have h1 := mul_lt_mul_of_pos_left h_bound hη_pos
    rwa [← mul_assoc, mul_inv_cancel₀ (ne_of_gt hη_pos), one_mul] at h1
  have h_le_norm : -(h y - h s₀ - (-η * h')) ≤ ‖h y - h s₀ - (-η * h')‖ := by
    rw [Real.norm_eq_abs]
    exact neg_le_abs _
  nlinarith

/-- Derivative of `kmsCompFunc Γ_coh Γ_diss δ` at `s ≥ 0` for `Γ_diss ≥ 0` and `δ > 0`. -/
lemma hasDerivAt_kmsCompFunc {Γ_coh Γ_diss δ s : ℝ}
    (hΓ_diss : 0 ≤ Γ_diss) (hδ : 0 < δ) (hs : 0 ≤ s) :
    let r := Real.sqrt ((1 / 2 : ℝ) * Γ_diss * s + δ ^ 2)
    let u := Γ_coh * s + r
    HasDerivAt (kmsCompFunc Γ_coh Γ_diss δ)
      (2 * u * (Γ_coh + Γ_diss / (4 * r))) s := by
  intro r u
  have h_inner_pos : 0 < (1 / 2 : ℝ) * Γ_diss * s + δ ^ 2 := by positivity
  have h_inner : HasDerivAt (fun x : ℝ => (1 / 2 : ℝ) * Γ_diss * x + δ ^ 2)
      ((1 / 2 : ℝ) * Γ_diss) s := by
    simpa using ((hasDerivAt_id' s).const_mul ((1 / 2 : ℝ) * Γ_diss)).add_const (δ ^ 2)
  have h_sqrt : HasDerivAt (fun x : ℝ => Real.sqrt ((1 / 2 : ℝ) * Γ_diss * x + δ ^ 2))
      (((1 / 2 : ℝ) * Γ_diss) / (2 * r)) s :=
    h_inner.sqrt (ne_of_gt h_inner_pos)
  have h_lin : HasDerivAt (fun x : ℝ => Γ_coh * x) Γ_coh s := by
    simpa using (hasDerivAt_id' s).const_mul Γ_coh
  have h_u : HasDerivAt (fun x : ℝ => Γ_coh * x + Real.sqrt ((1 / 2 : ℝ) * Γ_diss * x + δ ^ 2))
      (Γ_coh + ((1 / 2 : ℝ) * Γ_diss) / (2 * r)) s :=
    h_lin.add h_sqrt
  have h_sq := h_u.fun_pow 2
  exact h_sq.congr_deriv (by ring)

/-- Square root and derivative lower bound for `kmsCompFunc Γ_coh Γ_diss δ s`. -/
theorem kmsCompFunc_sqrt_and_deriv_ge {Γ_coh Γ_diss δ s : ℝ}
    (hΓ_coh : 0 ≤ Γ_coh) (hΓ_diss : 0 ≤ Γ_diss) (hδ : 0 < δ) (hs : 0 ≤ s) :
    let r := Real.sqrt ((1 / 2 : ℝ) * Γ_diss * s + δ ^ 2)
    let u := Γ_coh * s + r
    Real.sqrt (kmsCompFunc Γ_coh Γ_diss δ s) = u ∧
    δ ≤ u ∧
    2 * Γ_coh * Real.sqrt (kmsCompFunc Γ_coh Γ_diss δ s) + (1 / 2 : ℝ) * Γ_diss ≤
      2 * u * (Γ_coh + Γ_diss / (4 * r)) := by
  intro r u
  have hr_pos : 0 < r := Real.sqrt_pos.mpr (by positivity)
  have hr_ne : r ≠ 0 := ne_of_gt hr_pos
  have h_sqrt : Real.sqrt (kmsCompFunc Γ_coh Γ_diss δ s) = u := by
    dsimp [kmsCompFunc, u]
    exact Real.sqrt_sq (by positivity)
  have hδ_le_r : δ ≤ r := by
    calc δ
      _ = Real.sqrt (δ ^ 2) := (Real.sqrt_sq (le_of_lt hδ)).symm
      _ ≤ Real.sqrt ((1 / 2 : ℝ) * Γ_diss * s + δ ^ 2) :=
        Real.sqrt_le_sqrt (by linarith [mul_nonneg (by positivity : 0 ≤ (1 / 2 : ℝ) * Γ_diss) hs])
  have hδ_le_u : δ ≤ u := by
    dsimp [u]
    linarith [mul_nonneg hΓ_coh hs]
  refine ⟨h_sqrt, hδ_le_u, ?_⟩
  rw [h_sqrt]
  have h_eq : 2 * r * (Γ_diss / (4 * r)) = (1 / 2 : ℝ) * Γ_diss := by
    field_simp [hr_ne]
    ring
  have h_le : 2 * r * (Γ_diss / (4 * r)) ≤ 2 * u * (Γ_diss / (4 * r)) := by
    have h_div_nonneg : 0 ≤ Γ_diss / (4 * r) := by positivity
    have h_r_le : r ≤ u := by
      dsimp [u]
      linarith [mul_nonneg hΓ_coh hs]
    nlinarith
  linarith

/-- Derivative of the polynomial weight $(s_1 + 1 - x)^{m + 1}$. -/
lemma hasDerivAt_polyWeight (s₁ : ℝ) (m : ℕ) (s : ℝ) :
    HasDerivAt (fun x : ℝ => (s₁ + 1 - x) ^ (m + 1))
      (-(((m : ℝ) + 1) * (s₁ + 1 - s) ^ m)) s := by
  have h1 : HasDerivAt (fun x : ℝ => s₁ + 1 - x) (-1) s :=
    (hasDerivAt_id' s).const_sub (s₁ + 1)
  have h2 := h1.fun_pow (m + 1)
  convert h2 using 1
  push_cast
  ring

/-- **Grönwall ODE Integration Bound (`kms_gronwall_ode_integral_bound`; Part I, Section 5.5 (`subsec:unperturbed-kms-lifetime`), Theorem 5.8 (`thm:unperturbed-kms-lifetime`); Part II, Section 6.2 (`subsec:kms-gronwall`), Theorem 6.2 (`thm:kms-gronwall-bare`), Equation (90) (`eq:gronwall-sqrt-drift`))**:
    If $f : \mathbb{R} \to \mathbb{R}$ satisfies $f(0) \le 0$, $0 \le f(s)$, and
    $f'(s) \le 2\Gamma_{\mathrm{coh}}\sqrt{f(s)} + \frac{1}{2}\Gamma_{\mathrm{diss}}$ on $[0, t]$,
    then $\sqrt{f(s)} \le s\,\Gamma_{\mathrm{coh}} + \sqrt{\frac{s}{2}\,\Gamma_{\mathrm{diss}}}$
    for all $s \in [0, t]$. -/
theorem kms_gronwall_ode_integral_bound
    {f f' : ℝ → ℝ} {Γ_coh Γ_diss t : ℝ}
    (hΓ_coh : 0 ≤ Γ_coh) (hΓ_diss : 0 ≤ Γ_diss) (ht : 0 ≤ t)
    (hf0 : f 0 ≤ 0)
    (hf_nonneg : ∀ s ∈ Set.Icc 0 t, 0 ≤ f s)
    (hf_deriv : ∀ s ∈ Set.Icc 0 t, HasDerivAt f (f' s) s)
    (hf_ineq : ∀ s ∈ Set.Icc 0 t,
      f' s ≤ 2 * Γ_coh * Real.sqrt (f s) + (1 / 2 : ℝ) * Γ_diss) :
    ∀ s ∈ Set.Icc 0 t,
      Real.sqrt (f s) ≤ kmsDriftDirichletBound Γ_coh Γ_diss s := by
  intro s₁ hs₁
  have hs₁_nonneg : 0 ≤ s₁ := hs₁.1
  have hs₁_le_t : s₁ ≤ t := hs₁.2
  have h_for_delta : ∀ δ : ℝ, 0 < δ → f s₁ ≤ kmsCompFunc Γ_coh Γ_diss δ s₁ := by
    intro δ hδ
    let m : ℕ := Nat.ceil ((s₁ + 1) * (Γ_coh / δ))
    let g := kmsCompFunc Γ_coh Γ_diss δ
    let g' : ℝ → ℝ := fun s =>
      let r := Real.sqrt ((1 / 2 : ℝ) * Γ_diss * s + δ ^ 2)
      let u := Γ_coh * s + r
      2 * u * (Γ_coh + Γ_diss / (4 * r))
    let w : ℝ → ℝ := fun s => (s₁ + 1 - s) ^ (m + 1)
    let w' : ℝ → ℝ := fun s => -(((m : ℝ) + 1) * (s₁ + 1 - s) ^ m)
    let h : ℝ → ℝ := fun s => w s * (f s - g s)
    let h' : ℝ → ℝ := fun s => w' s * (f s - g s) + w s * (f' s - g' s)
    have hh_deriv : ∀ s ∈ Set.Icc 0 s₁, HasDerivAt h (h' s) s := by
      intro s hs
      have hs_t : s ∈ Set.Icc 0 t := ⟨hs.1, le_trans hs.2 hs₁_le_t⟩
      exact (hasDerivAt_polyWeight s₁ m s).mul
        ((hf_deriv s hs_t).sub (hasDerivAt_kmsCompFunc hΓ_diss hδ hs.1))
    have hh_cont : ContinuousOn h (Set.Icc 0 s₁) :=
      HasDerivAt.continuousOn hh_deriv
    rcases isCompact_Icc.exists_isMaxOn (Set.nonempty_Icc.mpr hs₁_nonneg) hh_cont with
      ⟨s₀, hs₀_mem, hs₀_max⟩
    have hs₀_le_all : ∀ x ∈ Set.Icc 0 s₁, h x ≤ h s₀ := isMaxOn_iff.mp hs₀_max
    have hh_s₀_nonpos : h s₀ ≤ 0 := by
      by_contra! hh_pos
      have hs₀_nonneg : 0 ≤ s₀ := hs₀_mem.1
      have hs₀_le_s₁ : s₀ ≤ s₁ := hs₀_mem.2
      have hs₀_t : s₀ ∈ Set.Icc 0 t := ⟨hs₀_nonneg, le_trans hs₀_le_s₁ hs₁_le_t⟩
      let u₀ := s₁ + 1 - s₀
      have hu₀_ge_one : 1 ≤ u₀ := by dsimp [u₀]; linarith
      have hu₀_pos : 0 < u₀ := by linarith
      have hu₀_le : u₀ ≤ s₁ + 1 := by dsimp [u₀]; linarith
      have hw_s₀_pos : 0 < w s₀ := pow_pos hu₀_pos (m + 1)
      have h_diff_pos : 0 < f s₀ - g s₀ := by
        by_contra! h_nonpos
        have : h s₀ ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (le_of_lt hw_s₀_pos) h_nonpos
        linarith
      have hg0 : g 0 = δ ^ 2 := by
        dsimp [g, kmsCompFunc]
        rw [mul_zero, zero_add, mul_zero, zero_add, Real.sqrt_sq (le_of_lt hδ)]
      have hh0_neg : h 0 < 0 := by
        dsimp [h]
        have hw0_pos : 0 < w 0 := by
          dsimp [w]
          exact pow_pos (by linarith) (m + 1)
        have hfg0 : f 0 - g 0 < 0 := by
          rw [hg0]
          linarith [sq_pos_of_pos hδ]
        exact mul_neg_of_pos_of_neg hw0_pos hfg0
      have hs₀_ne_zero : s₀ ≠ 0 := by
        intro h_eq
        rw [h_eq] at hh_pos
        linarith
      have hs₀_pos : 0 < s₀ := lt_of_le_of_ne hs₀_nonneg (Ne.symm hs₀_ne_zero)
      have hh'_nonneg : 0 ≤ h' s₀ :=
        not_neg_deriv_at_right_of_isMaxOn hs₀_pos hs₀_le_s₁ hs₀_le_all (hh_deriv s₀ hs₀_mem)
      rcases kmsCompFunc_sqrt_and_deriv_ge hΓ_coh hΓ_diss hδ hs₀_nonneg with
        ⟨h_sqrt_g, hδ_le_sqrt_g, hg'_ge⟩
      have hf'_le : f' s₀ ≤ 2 * Γ_coh * Real.sqrt (f s₀) + (1 / 2 : ℝ) * Γ_diss :=
        hf_ineq s₀ hs₀_t
      have h_f'_sub_g' :
          f' s₀ - g' s₀ ≤ 2 * Γ_coh * (Real.sqrt (f s₀) - Real.sqrt (g s₀)) := by
        dsimp [g', g] at hg'_ge ⊢
        linarith
      set a := Real.sqrt (f s₀)
      set b := Real.sqrt (g s₀)
      have ha_nonneg : 0 ≤ a := Real.sqrt_nonneg _
      have hb_ge_δ : δ ≤ b := by
        rw [h_sqrt_g]
        exact hδ_le_sqrt_g
      have ha_sq : a ^ 2 = f s₀ := Real.sq_sqrt (hf_nonneg s₀ hs₀_t)
      have hb_sq : b ^ 2 = g s₀ := Real.sq_sqrt (by dsimp [g, kmsCompFunc]; positivity)
      have hab_prod : (a - b) * (a + b) = f s₀ - g s₀ := by
        calc (a - b) * (a + b)
          _ = a ^ 2 - b ^ 2 := by ring
          _ = f s₀ - g s₀ := by rw [ha_sq, hb_sq]
      have hab_sum_pos : 0 < a + b := by linarith
      have ha_sub_b_pos : 0 < a - b := by
        by_contra! hab_nonpos
        have : (a - b) * (a + b) ≤ 0 :=
          mul_nonpos_of_nonpos_of_nonneg hab_nonpos (le_of_lt hab_sum_pos)
        linarith
      have hab_sum_ge : 2 * δ ≤ a + b := by linarith
      have h_2δ_mul : 2 * δ * (a - b) ≤ f s₀ - g s₀ := by
        calc 2 * δ * (a - b)
          _ ≤ (a + b) * (a - b) :=
            mul_le_mul_of_nonneg_right hab_sum_ge (le_of_lt ha_sub_b_pos)
          _ = (a - b) * (a + b) := mul_comm _ _
          _ = f s₀ - g s₀ := hab_prod
      have h_deriv_diff_bound :
          f' s₀ - g' s₀ ≤ (Γ_coh / δ) * (f s₀ - g s₀) := by
        have h_scale :
            (Γ_coh / δ) * (2 * δ * (a - b)) ≤ (Γ_coh / δ) * (f s₀ - g s₀) :=
          mul_le_mul_of_nonneg_left h_2δ_mul (by positivity)
        have h_lhs_eq : (Γ_coh / δ) * (2 * δ * (a - b)) = 2 * Γ_coh * (a - b) := by
          field_simp [ne_of_gt hδ]
        linarith
      have h_m_ge : (s₁ + 1) * (Γ_coh / δ) ≤ (m : ℝ) :=
        Nat.le_ceil ((s₁ + 1) * (Γ_coh / δ))
      have h_u₀_deriv_bound :
          u₀ * (f' s₀ - g' s₀) ≤ (m : ℝ) * (f s₀ - g s₀) := by
        calc u₀ * (f' s₀ - g' s₀)
          _ ≤ u₀ * ((Γ_coh / δ) * (f s₀ - g s₀)) :=
            mul_le_mul_of_nonneg_left h_deriv_diff_bound (le_of_lt hu₀_pos)
          _ = (u₀ * (Γ_coh / δ)) * (f s₀ - g s₀) := by ring
          _ ≤ ((s₁ + 1) * (Γ_coh / δ)) * (f s₀ - g s₀) := by
            refine mul_le_mul_of_nonneg_right ?_ (le_of_lt h_diff_pos)
            exact mul_le_mul_of_nonneg_right hu₀_le (by positivity)
          _ ≤ (m : ℝ) * (f s₀ - g s₀) :=
            mul_le_mul_of_nonneg_right h_m_ge (le_of_lt h_diff_pos)
      have hu₀_pow_pos : 0 < u₀ ^ m := pow_pos hu₀_pos m
      have hh'_eq :
          h' s₀ = u₀ ^ m * (-(((m : ℝ) + 1) * (f s₀ - g s₀)) + u₀ * (f' s₀ - g' s₀)) := by
        dsimp [h', w', w, u₀]
        rw [pow_succ]
        ring
      have hh'_neg : h' s₀ < 0 := by
        rw [hh'_eq]
        refine mul_neg_of_pos_of_neg hu₀_pow_pos ?_
        linarith
      linarith
    have hh_s₁_le : h s₁ ≤ 0 := le_trans (hs₀_le_all s₁ ⟨hs₁_nonneg, le_rfl⟩) hh_s₀_nonpos
    dsimp [h] at hh_s₁_le
    have hw_s₁' : w s₁ = 1 := by
      dsimp [w]
      have : s₁ + 1 - s₁ = 1 := by ring
      rw [this, one_pow]
    rw [hw_s₁', one_mul] at hh_s₁_le
    linarith
  have h_sqrt_for_delta :
      ∀ δ : ℝ, 0 < δ → Real.sqrt (f s₁) ≤ kmsDriftDirichletBound Γ_coh Γ_diss s₁ + δ := by
    intro δ hδ
    have h_le := Real.sqrt_le_sqrt (h_for_delta δ hδ)
    have h_rhs_eq :
        Real.sqrt (kmsCompFunc Γ_coh Γ_diss δ s₁) =
          Γ_coh * s₁ + Real.sqrt ((1 / 2 : ℝ) * Γ_diss * s₁ + δ ^ 2) :=
      (kmsCompFunc_sqrt_and_deriv_ge hΓ_coh hΓ_diss hδ hs₁_nonneg).1
    rw [h_rhs_eq] at h_le
    set a := (s₁ / 2) * Γ_diss
    have ha_nonneg : 0 ≤ a := by dsimp [a]; positivity
    have ha_eq : (1 / 2 : ℝ) * Γ_diss * s₁ = a := by dsimp [a]; ring
    have h_subadd : Real.sqrt (a + δ ^ 2) ≤ Real.sqrt a + δ := by
      have h_sq_le : a + δ ^ 2 ≤ (Real.sqrt a + δ) ^ 2 := by
        have h_sq_a : Real.sqrt a ^ 2 = a := Real.sq_sqrt ha_nonneg
        have h_prod_nonneg : 0 ≤ 2 * Real.sqrt a * δ := by positivity
        nlinarith
      calc Real.sqrt (a + δ ^ 2)
        _ ≤ Real.sqrt ((Real.sqrt a + δ) ^ 2) := Real.sqrt_le_sqrt h_sq_le
        _ = Real.sqrt a + δ := Real.sqrt_sq (by positivity)
    rw [ha_eq] at h_le
    dsimp [kmsDriftDirichletBound]
    linarith
  by_contra! h_gt
  let δ := (Real.sqrt (f s₁) - kmsDriftDirichletBound Γ_coh Γ_diss s₁) / 2
  have hδ_pos : 0 < δ := by dsimp [δ]; linarith
  have h_bound := h_sqrt_for_delta δ hδ_pos
  dsimp [δ] at h_bound
  linarith

/-- **Derivation of the Scalar Differential Inequality from the Heisenberg–Lindblad Generator
    (`kms_lindblad_generator_deriv_ineq`; Part I, Section 5.5 (`subsec:unperturbed-kms-lifetime`), Theorem 5.8 (`thm:unperturbed-kms-lifetime`); Part II, Section 6.2 (`subsec:kms-gronwall`), Theorem 6.2 (`thm:kms-gronwall-bare`), Equations (90) and (94) (`eq:gronwall-sqrt-drift`, `eq:gronwall-diff-identity`))**. -/
theorem kms_lindblad_generator_deriv_ineq {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    [∀ x, Nonempty (Site x)]
    {BathIdx : Type} [Fintype BathIdx]
    (sys : CommutingProjectorHamiltonian D L Site)
    (V : LocalPerturbation D L Site)
    (ψ_eig : ManyBodyConfig Site → ManyBodyHilbertSpace Site)
    (E_eig : ManyBodyConfig Site → ℝ) (β : ℝ)
    (h_onb : ∀ ω₁ ω₂ : ManyBodyConfig Site,
      inner ℂ (ψ_eig ω₁) (ψ_eig ω₂) = if ω₁ = ω₂ then (1 : ℂ) else 0)
    (h_tr_basis : ∀ X : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site,
      hilbertTrace X = ∑ ω : ManyBodyConfig Site, RCLike.re (inner ℂ (ψ_eig ω) (X (ψ_eig ω))))
    (h_eig : ∀ ω : ManyBodyConfig Site,
      (sys.H0 + V.totalPerturbation) * rankOneKetBra (ψ_eig ω) =
        (E_eig ω : ℂ) • rankOneKetBra (ψ_eig ω) ∧
      rankOneKetBra (ψ_eig ω) * (sys.H0 + V.totalPerturbation) =
        (E_eig ω : ℂ) • rankOneKetBra (ψ_eig ω) ∧
      ∀ A : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site,
        hilbertTrace (rankOneKetBra (ψ_eig ω) * A) =
          hilbertTrace (A * rankOneKetBra (ψ_eig ω)))
    (L_jump : BoxD D L → BathIdx → (ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site))
    (D_star : (ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site) →
      (ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site))
    (O O_s : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site)
    (f'_s : ℝ)
    (hO_sa : IsSelfAdjoint O) (hOs_sa : IsSelfAdjoint O_s)
    (hD_diss : kmsInnerReal ψ_eig E_eig β (O_s - O) (D_star O_s) ≤
      -kmsDirichletForm ψ_eig E_eig β L_jump O_s +
        Real.sqrt (kmsDirichletForm ψ_eig E_eig β L_jump O) *
          Real.sqrt (kmsDirichletForm ψ_eig E_eig β L_jump O_s))
    (h_gen : (1 / 2 : ℝ) * f'_s =
      kmsInnerReal ψ_eig E_eig β (O_s - O)
        (Complex.I • opCommutator (sys.H0 + V.totalPerturbation) O_s + D_star O_s)) :
    f'_s ≤
      2 * kmsCoherentDrift sys V ψ_eig E_eig β O * kmsNorm ψ_eig E_eig β (O_s - O) +
        (1 / 2 : ℝ) * kmsDirichletForm ψ_eig E_eig β L_jump O := by
  have hΔ_sa : IsSelfAdjoint (O_s - O) := by
    rw [ContinuousLinearMap.isSelfAdjoint_iff'] at hO_sa hOs_sa ⊢
    rw [map_sub, hOs_sa, hO_sa]
  have h_split :
      (1 / 2 : ℝ) * f'_s =
        kmsInnerReal ψ_eig E_eig β (O_s - O)
          (Complex.I • opCommutator (sys.H0 + V.totalPerturbation) (O_s - O)) +
        kmsInnerReal ψ_eig E_eig β (O_s - O)
          (Complex.I • opCommutator (sys.H0 + V.totalPerturbation) O) +
        kmsInnerReal ψ_eig E_eig β (O_s - O) (D_star O_s) := by
    rw [h_gen, kmsInnerReal_add_right,
      opCommutator_sub_add_cancel (sys.H0 + V.totalPerturbation) O_s O,
      kmsInnerReal_add_right]
  have h_skew :
      kmsInnerReal ψ_eig E_eig β (O_s - O)
        (Complex.I • opCommutator (sys.H0 + V.totalPerturbation) (O_s - O)) = 0 :=
    kmsInnerReal_commutator_eq_zero (sys.H0 + V.totalPerturbation) ψ_eig E_eig β h_eig (O_s - O) hΔ_sa
  have h_coh :
      kmsInnerReal ψ_eig E_eig β (O_s - O)
        (Complex.I • opCommutator (sys.H0 + V.totalPerturbation) O) ≤
      kmsNorm ψ_eig E_eig β (O_s - O) * kmsCoherentDrift sys V ψ_eig E_eig β O :=
    kmsInnerReal_coherent_commutator_le sys V ψ_eig E_eig β h_onb h_tr_basis (O_s - O) O
  have h_young :
      -kmsDirichletForm ψ_eig E_eig β L_jump O_s +
        Real.sqrt (kmsDirichletForm ψ_eig E_eig β L_jump O) *
          Real.sqrt (kmsDirichletForm ψ_eig E_eig β L_jump O_s) ≤
      (1 / 4 : ℝ) * kmsDirichletForm ψ_eig E_eig β L_jump O :=
    kms_dirichlet_young_ineq
      (kmsDirichletForm_nonneg ψ_eig E_eig β h_onb h_tr_basis L_jump O)
      (kmsDirichletForm_nonneg ψ_eig E_eig β h_onb h_tr_basis L_jump O_s)
  linarith

end
