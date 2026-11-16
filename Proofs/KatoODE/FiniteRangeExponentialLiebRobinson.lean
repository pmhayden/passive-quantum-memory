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

import Proofs.LiebRobinson.BochnerQuasiLocality
import Proofs.LiebRobinson.LiebRobinsonSeries

/-!
# Finite-Range Exponential Lieb–Robinson Commutator Bound

Proves the exponential spatial-decay Lieb–Robinson commutator bound `norm_opCommutator_heisenbergEvolve_shortRange_le` for lattice Hamiltonians of finite interaction diameter using exponential spatial weights `expWeightY` and iterated Duhamel–Grönwall induction.

## References

* Part I, Section 6.2 (`subsec:bochner-lr`), Proposition 6.3 (`prop:bochner-time-convolution`)
* Lieb–Robinson (1972), Communications in Mathematical Physics 28, 251–257
-/

noncomputable section

open scoped Classical InnerProduct ComplexConjugate BigOperators
open Filter Topology Asymptotics MeasureTheory ContinuousLinearMap

set_option maxRecDepth 200000
set_option maxHeartbeats 800000

/-!
## 1. Finite-Range Exponential Lieb–Robinson Bound (`expWeightY`)
-/

/-- Exponential spatial decay weight $w_Y^{(R)}(x) := \exp(-\mathrm{boxRegionDist}(x, Y) / R)$. -/
def expWeightY {D L : ℕ} (Y : Finset (BoxD D L)) (R : ℕ) (x : BoxD D L) : ℝ :=
  Real.exp (- (boxRegionDist x Y : ℝ) / (R : ℝ))

lemma expWeightY_pos {D L : ℕ} (Y : Finset (BoxD D L)) (R : ℕ) (x : BoxD D L) :
    0 < expWeightY Y R x := Real.exp_pos _

lemma exp_diam_expWeightY_le {D L : ℕ} {Y Z : Finset (BoxD D L)} (hY : Y.Nonempty) (x z : BoxD D L)
    {R : ℕ} (hR : 1 ≤ R) (hZ_diam : regionDiam Z ≤ R) (hx : x ∈ Z) (hz : z ∈ Z) :
    expWeightY Y R z ≤ Real.exp 1 * expWeightY Y R x := by
  unfold expWeightY; rw [← Real.exp_add]; apply Real.exp_le_exp.mpr
  have hR_pos : (0 : ℝ) < (R : ℝ) := Nat.cast_pos.mpr (Nat.succ_le_iff.mp hR)
  have h_dist : (boxRegionDist x Y : ℝ) ≤ (R : ℝ) + (boxRegionDist z Y : ℝ) := by
    have h1 := boxRegionDist_le_regionDiam_add hY hx hz
    exact_mod_cast le_trans h1 (Nat.add_le_add_right hZ_diam _)
  have h_div := div_le_div_of_nonneg_right h_dist hR_pos.le
  rw [add_div, div_self hR_pos.ne'] at h_div; simp only [neg_div]; linarith

lemma sum_expWeightY_le {D L : ℕ} {Y Z : Finset (BoxD D L)} (hY : Y.Nonempty) (x : BoxD D L)
    {R : ℕ} (hR : 1 ≤ R) (hZ_diam : regionDiam Z ≤ R) (hx : x ∈ Z) :
    ∑ z ∈ Z, expWeightY Y R z ≤ (Z.card : ℝ) * Real.exp 1 * expWeightY Y R x := by
  calc ∑ z ∈ Z, expWeightY Y R z
    _ ≤ ∑ _z ∈ Z, Real.exp 1 * expWeightY Y R x :=
      Finset.sum_le_sum (fun z hz => exp_diam_expWeightY_le hY x z hR hZ_diam hx hz)
    _ = (Z.card : ℝ) * Real.exp 1 * expWeightY Y R x := by rw [Finset.sum_const, nsmul_eq_mul]; ring

lemma sum_expWeightY_regionDist_le {D L : ℕ}
    (X Y : Finset (BoxD D L)) (hY : Y.Nonempty) (R : ℕ) :
    ∑ x ∈ X, expWeightY Y R x ≤ (X.card : ℝ) * Real.exp (- (regionDist X Y : ℝ) / (R : ℝ)) := by
  have hx_le : ∀ x ∈ X, expWeightY Y R x ≤ Real.exp (- (regionDist X Y : ℝ) / (R : ℝ)) := by
    intro x hx; unfold expWeightY; apply Real.exp_le_exp.mpr
    have hd_nat : regionDist X Y ≤ boxRegionDist x Y := by
      suffices h_le : ∀ k, k ≤ regionDist X Y → k ≤ boxRegionDist x Y from h_le _ le_rfl
      intro k hk; dsimp [boxRegionDist, regionDist]
      have hne : ({x} : Finset (BoxD D L)).Nonempty ∧ Y.Nonempty := ⟨Finset.singleton_nonempty x, hY⟩
      rw [dif_pos hne, Finset.le_inf'_iff]; intro p hp
      rcases Finset.mem_product.mp hp with ⟨hp1, hp2⟩
      rw [Finset.mem_singleton] at hp1
      have h1 : regionDist X Y ≤ boxDist p.1 p.2 := hp1 ▸ regionDist_le_boxDist hx hp2
      omega
    exact div_le_div_of_nonneg_right (neg_le_neg (Nat.cast_le.mpr hd_nat)) (Nat.cast_nonneg R)
  calc ∑ x ∈ X, expWeightY Y R x
    _ ≤ ∑ _x ∈ X, Real.exp (- (regionDist X Y : ℝ) / (R : ℝ)) := Finset.sum_le_sum hx_le
    _ = (X.card : ℝ) * Real.exp (- (regionDist X Y : ℝ) / (R : ℝ)) := by
      rw [Finset.sum_const, nsmul_eq_mul]

/-- Exponential-weight site quotient $(w_Y^{(R)}(x))^{-1} \sum_{Z \ni x} \|[\tau_{\sigma\tau}^H(h_Z), B]\|$. -/
def siteQuotientExp {D L : ℕ} {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    (H : LatticeHamiltonian D L Site) (Y : Finset (BoxD D L)) (R : ℕ)
    (B : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site) (σ : ℝ) (x : BoxD D L) (τ : ℝ) : ℝ :=
  (expWeightY Y R x)⁻¹ * siteCommSum H B σ x τ

/-- Supremum over $x \in \mathrm{BoxD}\ D\ L$ of `siteQuotientExp`. -/
def maxQuotientExp {D L : ℕ} [NeZero D] [NeZero L]
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    (H : LatticeHamiltonian D L Site) (Y : Finset (BoxD D L)) (R : ℕ)
    (B : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site) (σ : ℝ) (τ : ℝ) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty (fun x => siteQuotientExp H Y R B σ x τ)

lemma maxQuotientExp_nonneg {D L : ℕ} [NeZero D] [NeZero L]
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    (H : LatticeHamiltonian D L Site) (Y : Finset (BoxD D L)) (R : ℕ)
    (B : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site) (σ : ℝ) (τ : ℝ) :
    0 ≤ maxQuotientExp H Y R B σ τ := by
  have x0 : BoxD D L := fun _ => ⟨0, NeZero.pos L⟩
  have h0 : 0 ≤ siteQuotientExp H Y R B σ x0 τ :=
    mul_nonneg (inv_nonneg.mpr (le_of_lt (expWeightY_pos Y R x0))) (siteCommSum_nonneg H B σ x0 τ)
  exact le_trans h0 (Finset.le_sup' (fun x => siteQuotientExp H Y R B σ x τ) (Finset.mem_univ x0))

lemma siteCommSum_le_mul_maxQuotientExp {D L : ℕ} [NeZero D] [NeZero L]
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    (H : LatticeHamiltonian D L Site) (Y : Finset (BoxD D L)) (R : ℕ)
    (B : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site) (σ : ℝ) (x : BoxD D L) (τ : ℝ) :
    siteCommSum H B σ x τ ≤ expWeightY Y R x * maxQuotientExp H Y R B σ τ := by
  have hw : 0 < expWeightY Y R x := expWeightY_pos Y R x
  have hq : siteQuotientExp H Y R B σ x τ ≤ maxQuotientExp H Y R B σ τ :=
    Finset.le_sup' (fun z => siteQuotientExp H Y R B σ z τ) (Finset.mem_univ x)
  have hmul := mul_le_mul_of_nonneg_left hq (le_of_lt hw)
  unfold siteQuotientExp at hmul
  rwa [← mul_assoc, mul_inv_cancel₀ (ne_of_gt hw), one_mul] at hmul

lemma siteCommSum_zero_exp_le {D L : ℕ} [NeZero D] [NeZero L]
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    (H : LatticeHamiltonian D L Site) {R : ℕ} (hR : 1 ≤ R)
    (h_range : ∀ Z : Finset (BoxD D L), R < regionDiam Z → H.h Z = 0) {Y : Finset (BoxD D L)}
    {B : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site}
    (hB : IsSupportedOn Site Y B) (σ : ℝ) (x : BoxD D L) :
    siteCommSum H B σ x 0 ≤ 2 * ‖B‖ * Real.exp 1 * H.s1 0 * expWeightY Y R x := by
  unfold siteCommSum
  have hev0 : ∀ Z, H.heisenbergEvolve (σ * 0) (H.h Z) = H.h Z := fun Z => by
    unfold LatticeHamiltonian.heisenbergEvolve heisenbergFlow
    rw [mul_zero, neg_zero, timeEvolutionOp_zero, one_mul, mul_one]
  simp only [hev0]
  have hterm : ∀ Z ∈ Finset.univ.filter (fun Z : Finset (BoxD D L) => x ∈ Z),
      ‖opCommutator (H.h Z) B‖ ≤ 2 * ‖B‖ * Real.exp 1 * expWeightY Y R x *
        (‖H.h Z‖ * (Z.card : ℝ) * (1 + (regionDiam Z : ℝ)) ^ (0 : ℝ)) := by
    intro Z hZ; rw [Finset.mem_filter] at hZ
    have hw : 0 ≤ expWeightY Y R x := le_of_lt (expWeightY_pos Y R x)
    by_cases hdiam : R < regionDiam Z
    · rw [h_range Z hdiam, opCommutator, zero_mul, mul_zero, sub_self, norm_zero]; positivity
    · push_neg at hdiam
      by_cases hdisj : Disjoint Z Y
      · rw [opCommutator_eq_zero_of_disjoint hdisj (H.is_supported Z) hB, norm_zero]; positivity
      · rw [Finset.not_disjoint_iff] at hdisj; rcases hdisj with ⟨y, hyZ, hyY⟩
        have hcomm : ‖opCommutator (H.h Z) B‖ ≤ 2 * ‖H.h Z‖ * ‖B‖ := norm_opCommutator_le _ _
        have hR_pos : (0 : ℝ) < (R : ℝ) := Nat.cast_pos.mpr (Nat.succ_le_iff.mp hR)
        have hd : (boxRegionDist x Y : ℝ) ≤ (R : ℝ) := by
          have h1 : boxRegionDist x Y ≤ regionDiam Z :=
            le_trans (regionDist_le_boxDist (Finset.mem_singleton_self x) hyY)
              (boxDist_le_regionDiam hZ.2 hyZ)
          exact_mod_cast le_trans h1 hdiam
        have hexp_ge_one : 1 ≤ Real.exp 1 * expWeightY Y R x := by
          unfold expWeightY; rw [← Real.exp_add]; apply Real.one_le_exp
          have hdiv : (boxRegionDist x Y : ℝ) / (R : ℝ) ≤ 1 := (div_le_iff₀ hR_pos).mpr (by linarith)
          simp only [neg_div]; linarith
        have hcard : (1 : ℝ) ≤ (Z.card : ℝ) := Nat.one_le_cast.mpr (Finset.card_pos.mpr ⟨x, hZ.2⟩)
        have h1 : 1 ≤ Real.exp 1 * expWeightY Y R x *
            ((Z.card : ℝ) * (1 + (regionDiam Z : ℝ)) ^ (0 : ℝ)) := by
          rw [Real.rpow_zero, mul_one]; nlinarith
        calc ‖opCommutator (H.h Z) B‖
          _ ≤ 2 * ‖H.h Z‖ * ‖B‖ * 1 := by linarith
          _ ≤ 2 * ‖H.h Z‖ * ‖B‖ * (Real.exp 1 * expWeightY Y R x *
                ((Z.card : ℝ) * (1 + (regionDiam Z : ℝ)) ^ (0 : ℝ))) :=
            mul_le_mul_of_nonneg_left h1 (by positivity)
          _ = 2 * ‖B‖ * Real.exp 1 * expWeightY Y R x *
              (‖H.h Z‖ * (Z.card : ℝ) * (1 + (regionDiam Z : ℝ)) ^ (0 : ℝ)) := by ring
  calc ∑ Z ∈ Finset.univ.filter (fun Z : Finset (BoxD D L) => x ∈ Z), ‖opCommutator (H.h Z) B‖
    _ ≤ ∑ Z ∈ Finset.univ.filter (fun Z : Finset (BoxD D L) => x ∈ Z),
          2 * ‖B‖ * Real.exp 1 * expWeightY Y R x *
            (‖H.h Z‖ * (Z.card : ℝ) * (1 + (regionDiam Z : ℝ)) ^ (0 : ℝ)) := Finset.sum_le_sum hterm
    _ = 2 * ‖B‖ * Real.exp 1 * expWeightY Y R x *
          ∑ Z ∈ Finset.univ.filter (fun Z : Finset (BoxD D L) => x ∈ Z),
            ‖H.h Z‖ * (Z.card : ℝ) * (1 + (regionDiam Z : ℝ)) ^ (0 : ℝ) := by rw [← Finset.mul_sum]
    _ ≤ 2 * ‖B‖ * Real.exp 1 * expWeightY Y R x * H.s1 0 := by
      refine mul_le_mul_of_nonneg_left ?_ (mul_nonneg (by positivity) (le_of_lt (expWeightY_pos Y R x)))
      unfold LatticeHamiltonian.s1
      exact Finset.le_sup' (f := fun z => ∑ Z ∈ Finset.univ.filter (fun Z => z ∈ Z),
        ‖H.h Z‖ * (Z.card : ℝ) * (1 + (regionDiam Z : ℝ)) ^ (0 : ℝ)) (Finset.mem_univ x)
    _ = 2 * ‖B‖ * Real.exp 1 * H.s1 0 * expWeightY Y R x := by ring

lemma maxQuotientExp_zero_le {D L : ℕ} [NeZero D] [NeZero L]
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    (H : LatticeHamiltonian D L Site) {R : ℕ} (hR : 1 ≤ R)
    (h_range : ∀ Z : Finset (BoxD D L), R < regionDiam Z → H.h Z = 0) {Y : Finset (BoxD D L)}
    {B : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site}
    (hB : IsSupportedOn Site Y B) (σ : ℝ) :
    maxQuotientExp H Y R B σ 0 ≤ 2 * ‖B‖ * Real.exp 1 * H.s1 0 := by
  unfold maxQuotientExp; rw [Finset.sup'_le_iff]; intro x _; unfold siteQuotientExp
  have hw : 0 < expWeightY Y R x := expWeightY_pos Y R x
  calc (expWeightY Y R x)⁻¹ * siteCommSum H B σ x 0
    _ ≤ (expWeightY Y R x)⁻¹ * (2 * ‖B‖ * Real.exp 1 * H.s1 0 * expWeightY Y R x) :=
      mul_le_mul_of_nonneg_left (siteCommSum_zero_exp_le H hR h_range hB σ x) (inv_nonneg.mpr (le_of_lt hw))
    _ = 2 * ‖B‖ * Real.exp 1 * H.s1 0 * ((expWeightY Y R x)⁻¹ * expWeightY Y R x) := by ring
    _ = 2 * ‖B‖ * Real.exp 1 * H.s1 0 := by rw [inv_mul_cancel₀ (ne_of_gt hw), mul_one]

lemma continuous_maxQuotientExp {D L : ℕ} [NeZero D] [NeZero L]
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    (H : LatticeHamiltonian D L Site) (Y : Finset (BoxD D L)) (R : ℕ)
    (B : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site) (σ : ℝ) :
    Continuous (maxQuotientExp H Y R B σ) := by
  unfold maxQuotientExp; apply continuous_finset_sup' Finset.univ Finset.univ_nonempty; intro x _
  unfold siteQuotientExp siteCommSum
  exact continuous_const.mul (continuous_finset_sum _ (fun Z _ =>
    continuous_norm_opCommutator_heisenbergEvolve H (H.is_supported Z) B σ))

lemma eventually_slope_maxQuotientExp_lt {D L : ℕ} [NeZero D] [NeZero L]
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    (H : LatticeHamiltonian D L Site) {R : ℕ} (hR : 1 ≤ R)
    (h_range : ∀ Z : Finset (BoxD D L), R < regionDiam Z → H.h Z = 0) {Y : Finset (BoxD D L)}
    (hY : Y.Nonempty) (B : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site)
    {σ : ℝ} (hσ : |σ| = 1) (τ r : ℝ)
    (hr : 2 * Real.exp 1 * H.s1 0 * maxQuotientExp H Y R B σ τ < r) :
    ∀ᶠ z in 𝓝[>] τ, (z - τ)⁻¹ * (maxQuotientExp H Y R B σ z - maxQuotientExp H Y R B σ τ) < r := by
  unfold maxQuotientExp
  apply eventually_slope_sup'_lt (fun x z => siteQuotientExp H Y R B σ x z) τ r; intro x
  have hw : 0 < expWeightY Y R x := expWeightY_pos Y R x
  set Sx := Finset.univ.filter (fun Z : Finset (BoxD D L) => x ∈ Z)
  set f' : Finset (BoxD D L) → ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site :=
    fun Z => opCommutator (H.h Z)
      ((Complex.I * ((-σ : ℝ) : ℂ)) • opCommutator (H.regionInteraction Z) (H.heisenbergEvolve (-σ * τ) B))
  have hf_deriv : ∀ Z ∈ Sx, HasDerivAt (fun z => psiOp H Z (H.h Z) B σ τ z) (f' Z) τ :=
    fun Z _ => hasDerivAt_psiOp H (H.opCommutator_H_tot_sub_regionInteraction_eq_zero (H.is_supported Z)) B σ τ
  have hZ_bound : ∀ Z ∈ Sx, ‖f' Z‖ ≤
      2 * Real.exp 1 * (‖H.h Z‖ * (Z.card : ℝ) * (1 + (regionDiam Z : ℝ)) ^ (0 : ℝ)) *
        expWeightY Y R x * maxQuotientExp H Y R B σ τ := by
    intro Z hZ; rw [Finset.mem_filter] at hZ
    have hq_nn := maxQuotientExp_nonneg H Y R B σ τ
    by_cases hdiam : R < regionDiam Z
    · dsimp [f']; rw [h_range Z hdiam, opCommutator, zero_mul, mul_zero, sub_self, norm_zero]; positivity
    · push_neg at hdiam
      have hd := norm_deriv_psiOp_le H Z (H.h Z) B hσ τ
      have hinter := sum_filter_inter_nonempty_le Z
        (fun W => ‖opCommutator (H.heisenbergEvolve (σ * τ) (H.h W)) B‖) (fun _ => norm_nonneg _)
      have hsum_z : ∑ z ∈ Z, siteCommSum H B σ z τ ≤
          (Z.card : ℝ) * Real.exp 1 * expWeightY Y R x * maxQuotientExp H Y R B σ τ := by
        calc ∑ z ∈ Z, siteCommSum H B σ z τ
          _ ≤ ∑ z ∈ Z, expWeightY Y R z * maxQuotientExp H Y R B σ τ :=
            Finset.sum_le_sum (fun z _ => siteCommSum_le_mul_maxQuotientExp H Y R B σ z τ)
          _ = (∑ z ∈ Z, expWeightY Y R z) * maxQuotientExp H Y R B σ τ := by rw [← Finset.sum_mul]
          _ ≤ ((Z.card : ℝ) * Real.exp 1 * expWeightY Y R x) * maxQuotientExp H Y R B σ τ :=
            mul_le_mul_of_nonneg_right (sum_expWeightY_le hY x hR hdiam hZ.2) hq_nn
          _ = (Z.card : ℝ) * Real.exp 1 * expWeightY Y R x * maxQuotientExp H Y R B σ τ := by ring
      calc ‖f' Z‖
        _ ≤ 2 * ‖H.h Z‖ * ∑ W ∈ Finset.univ.filter (fun W => (W ∩ Z).Nonempty),
              ‖opCommutator (H.heisenbergEvolve (σ * τ) (H.h W)) B‖ := hd
        _ ≤ 2 * ‖H.h Z‖ * ∑ z ∈ Z, siteCommSum H B σ z τ := mul_le_mul_of_nonneg_left hinter (by positivity)
        _ ≤ 2 * ‖H.h Z‖ * ((Z.card : ℝ) * Real.exp 1 * expWeightY Y R x * maxQuotientExp H Y R B σ τ) :=
          mul_le_mul_of_nonneg_left hsum_z (by positivity)
        _ = 2 * Real.exp 1 * (‖H.h Z‖ * (Z.card : ℝ) * (1 + (regionDiam Z : ℝ)) ^ (0 : ℝ)) *
            expWeightY Y R x * maxQuotientExp H Y R B σ τ := by rw [Real.rpow_zero, mul_one]; ring
  have hsum_f' : ∑ Z ∈ Sx, ‖f' Z‖ ≤
      2 * Real.exp 1 * H.s1 0 * maxQuotientExp H Y R B σ τ * expWeightY Y R x := by
    calc ∑ Z ∈ Sx, ‖f' Z‖
      _ ≤ ∑ Z ∈ Sx, 2 * Real.exp 1 * (‖H.h Z‖ * (Z.card : ℝ) * (1 + (regionDiam Z : ℝ)) ^ (0 : ℝ)) *
            expWeightY Y R x * maxQuotientExp H Y R B σ τ := Finset.sum_le_sum hZ_bound
      _ = 2 * Real.exp 1 * (∑ Z ∈ Sx, ‖H.h Z‖ * (Z.card : ℝ) * (1 + (regionDiam Z : ℝ)) ^ (0 : ℝ)) *
            expWeightY Y R x * maxQuotientExp H Y R B σ τ := by
        rw [Finset.mul_sum, Finset.sum_mul, Finset.sum_mul]
      _ ≤ 2 * Real.exp 1 * H.s1 0 * expWeightY Y R x * maxQuotientExp H Y R B σ τ := by
        have hs1 : ∑ Z ∈ Sx, ‖H.h Z‖ * (Z.card : ℝ) * (1 + (regionDiam Z : ℝ)) ^ (0 : ℝ) ≤ H.s1 0 := by
          unfold LatticeHamiltonian.s1
          exact Finset.le_sup' (f := fun z => ∑ Z ∈ Finset.univ.filter (fun Z => z ∈ Z),
            ‖H.h Z‖ * (Z.card : ℝ) * (1 + (regionDiam Z : ℝ)) ^ (0 : ℝ)) (Finset.mem_univ x)
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hs1 (by positivity)) (le_of_lt hw))
          (maxQuotientExp_nonneg H Y R B σ τ)
      _ = 2 * Real.exp 1 * H.s1 0 * maxQuotientExp H Y R B σ τ * expWeightY Y R x := by ring
  have hsum_lt : (∑ Z ∈ Sx, ‖f' Z‖) < r * expWeightY Y R x :=
    lt_of_le_of_lt hsum_f' (mul_lt_mul_of_pos_right hr hw)
  have ev := eventually_slope_sum_norm_lt Sx (fun Z z => psiOp H Z (H.h Z) B σ τ z) f' τ hf_deriv hsum_lt
  refine ev.mono (fun z hz => ?_)
  have h_psi_eq : ∀ u, (∑ Z ∈ Sx, ‖psiOp H Z (H.h Z) B σ τ u‖) = siteCommSum H B σ x u :=
    fun u => Finset.sum_congr rfl (fun Z _ => norm_psiOp_eq H Z (H.h Z) B σ τ u)
  rw [h_psi_eq z, h_psi_eq τ] at hz
  have hz' := mul_lt_mul_of_pos_left hz (inv_pos.mpr hw)
  unfold siteQuotientExp
  calc (z - τ)⁻¹ * ((expWeightY Y R x)⁻¹ * siteCommSum H B σ x z -
        (expWeightY Y R x)⁻¹ * siteCommSum H B σ x τ)
    _ = (expWeightY Y R x)⁻¹ * ((z - τ)⁻¹ * (siteCommSum H B σ x z - siteCommSum H B σ x τ)) := by ring
    _ < (expWeightY Y R x)⁻¹ * (r * expWeightY Y R x) := hz'
    _ = r * ((expWeightY Y R x)⁻¹ * expWeightY Y R x) := by ring
    _ = r := by rw [inv_mul_cancel₀ (ne_of_gt hw), mul_one]

lemma maxQuotientExp_le_exp {D L : ℕ} [NeZero D] [NeZero L]
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    (H : LatticeHamiltonian D L Site) {R : ℕ} (hR : 1 ≤ R)
    (h_range : ∀ Z : Finset (BoxD D L), R < regionDiam Z → H.h Z = 0) {Y : Finset (BoxD D L)}
    (hY : Y.Nonempty) {B : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site}
    (hB : IsSupportedOn Site Y B) {σ : ℝ} (hσ : |σ| = 1) (T : ℝ) {τ : ℝ} (hτ : τ ∈ Set.Icc 0 T) :
    maxQuotientExp H Y R B σ τ ≤
      2 * ‖B‖ * Real.exp 1 * H.s1 0 * Real.exp (2 * Real.exp 1 * H.s1 0 * τ) :=
  le_exp_of_eventually_slope_lt (continuous_maxQuotientExp H Y R B σ).continuousOn
    (maxQuotientExp_zero_le H hR h_range hB σ)
    (fun u _ r hr => eventually_slope_maxQuotientExp_lt H hR h_range hY B hσ u r hr) hτ

/-- **Finite-Range Exponential Lieb–Robinson Commutator Bound**:
    For any lattice Hamiltonian $H$ whose terms of diameter $> R$ vanish ($R \ge 1$) and any
    operators $A, B$ supported on nonempty regions $X, Y \subseteq \mathrm{BoxD}\ D\ L$,
    $$\|[\tau_t^H(A), B]\| \le 2 \|A\| \|B\| |X| \exp\left(-\frac{\mathrm{regionDist}(X, Y)}{R}\right)
      \exp\left(2 e H.s_1(0) |t|\right).$$ -/
theorem norm_opCommutator_heisenbergEvolve_shortRange_le {D L : ℕ} [NeZero D] [NeZero L]
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    (H : LatticeHamiltonian D L Site) {R : ℕ} (hR : 1 ≤ R)
    (h_range : ∀ Z : Finset (BoxD D L), R < regionDiam Z → H.h Z = 0)
    {X Y : Finset (BoxD D L)} (hX : X.Nonempty) (hY : Y.Nonempty)
    {A B : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site}
    (hA : IsSupportedOn Site X A) (hB : IsSupportedOn Site Y B) (t : ℝ) :
    ‖opCommutator (H.heisenbergEvolve t A) B‖ ≤
      2 * ‖A‖ * ‖B‖ * (X.card : ℝ) * Real.exp (- (regionDist X Y : ℝ) / (R : ℝ)) *
        Real.exp (2 * Real.exp 1 * H.s1 0 * |t|) := by
  have hs1_nonneg : 0 ≤ H.s1 0 := by
    unfold LatticeHamiltonian.s1
    have x0 : BoxD D L := fun _ => ⟨0, NeZero.pos L⟩
    have h0 : 0 ≤ ∑ Z ∈ Finset.univ.filter (fun Z : Finset (BoxD D L) => x0 ∈ Z),
        ‖H.h Z‖ * (Z.card : ℝ) * (1 + (regionDiam Z : ℝ)) ^ (0 : ℝ) :=
      Finset.sum_nonneg (fun Z _ => by positivity)
    exact le_trans h0 (Finset.le_sup' (f := fun x => ∑ Z ∈ Finset.univ.filter (fun Z => x ∈ Z),
      ‖H.h Z‖ * (Z.card : ℝ) * (1 + (regionDiam Z : ℝ)) ^ (0 : ℝ)) (Finset.mem_univ x0))
  by_cases h_dist0 : regionDist X Y = 0
  · rw [h_dist0, Nat.cast_zero, neg_zero, zero_div, Real.exp_zero, mul_one]
    have hcard : (1 : ℝ) ≤ (X.card : ℝ) := Nat.one_le_cast.mpr (Finset.card_pos.mpr hX)
    have hexp_ge : 1 ≤ Real.exp (2 * Real.exp 1 * H.s1 0 * |t|) := Real.one_le_exp (by positivity)
    have h_step := norm_commutator_heisenbergFlow_duhamel_step H.isSelfAdjoint_totalHamiltonian A B t
    calc ‖opCommutator (H.heisenbergEvolve t A) B‖
      _ ≤ 2 * ‖A‖ * ‖B‖ * 1 * 1 := by rw [mul_one, mul_one]; exact h_step
      _ ≤ 2 * ‖A‖ * ‖B‖ * (X.card : ℝ) * Real.exp (2 * Real.exp 1 * H.s1 0 * |t|) :=
        mul_le_mul (mul_le_mul_of_nonneg_left hcard (by positivity)) hexp_ge zero_le_one (by positivity)
  · have h_dist_pos : 0 < regionDist X Y := Nat.pos_of_ne_zero h_dist0
    set σ : ℝ := if 0 ≤ t then 1 else -1
    have hσ_abs : |σ| = 1 := by dsimp [σ]; split_ifs <;> simp
    have hσ_mul : σ * |t| = t := by
      dsimp [σ]; split_ifs with ht
      · rw [one_mul, abs_of_nonneg ht]
      · push_neg at ht; rw [neg_one_mul, abs_of_neg ht, neg_neg]
    set f : ℝ → ℝ := fun τ => ‖opCommutator (H.heisenbergEvolve (σ * τ) A) B‖
    set C_LR : ℝ := 2 * ‖A‖ * ‖B‖ * (X.card : ℝ) * Real.exp (- (regionDist X Y : ℝ) / (R : ℝ))
    set K : ℝ := 2 * Real.exp 1 * H.s1 0
    set B_LR : ℝ → ℝ := fun τ => C_LR * (Real.exp (K * τ) - 1)
    set B'_LR : ℝ → ℝ := fun τ => C_LR * (K * Real.exp (K * τ))
    have hf_cont : ContinuousOn f (Set.Icc 0 |t|) :=
      (continuous_norm_opCommutator_heisenbergEvolve H hA B σ).continuousOn
    have hf0 : f 0 ≤ B_LR 0 := by
      dsimp [f, B_LR]
      have hev0 : H.heisenbergEvolve (σ * 0) A = A := by
        unfold LatticeHamiltonian.heisenbergEvolve heisenbergFlow
        rw [mul_zero, neg_zero, timeEvolutionOp_zero, one_mul, mul_one]
      rw [hev0, opCommutator_eq_zero_of_disjoint (disjoint_of_regionDist_pos h_dist_pos) hA hB,
        norm_zero, mul_zero, Real.exp_zero, sub_self, mul_zero]
    have hB_deriv : ∀ τ : ℝ, HasDerivAt B_LR (B'_LR τ) τ := fun τ =>
      (((hasDerivAt_real_exp_const_mul K τ).sub_const 1).const_mul C_LR)
    have hB_cont : ContinuousOn B_LR (Set.Icc 0 |t|) :=
      fun τ _ => (hB_deriv τ).continuousAt.continuousWithinAt
    have hB_within : ∀ τ ∈ Set.Ico 0 |t|, HasDerivWithinAt B_LR (B'_LR τ) (Set.Ici τ) τ :=
      fun τ _ => (hB_deriv τ).hasDerivWithinAt
    have h_slope : ∀ τ ∈ Set.Ico 0 |t|, ∀ r, B'_LR τ < r → ∃ᶠ z in 𝓝[>] τ, slope f τ z < r := by
      intro τ hτ r hr
      have hQ_le := maxQuotientExp_le_exp H hR h_range hY hB hσ_abs |t| (Set.Ico_subset_Icc_self hτ)
      set dA := opCommutator A
        ((Complex.I * ((-σ : ℝ) : ℂ)) • opCommutator (H.regionInteraction X) (H.heisenbergEvolve (-σ * τ) B))
      have hd_psi := hasDerivAt_psiOp H (H.opCommutator_H_tot_sub_regionInteraction_eq_zero hA) B σ τ
      have hd_norm_le : ‖dA‖ ≤ B'_LR τ := by
        have hd1 := norm_deriv_psiOp_le H X A B hσ_abs τ
        have hinter := sum_filter_inter_nonempty_le X
          (fun W => ‖opCommutator (H.heisenbergEvolve (σ * τ) (H.h W)) B‖) (fun _ => norm_nonneg _)
        have h2A_nonneg : 0 ≤ 2 * ‖A‖ := mul_nonneg zero_le_two (norm_nonneg A)
        have hsum_X : ∑ x ∈ X, siteCommSum H B σ x τ ≤
            ((X.card : ℝ) * Real.exp (- (regionDist X Y : ℝ) / (R : ℝ))) *
              (2 * ‖B‖ * Real.exp 1 * H.s1 0 * Real.exp (K * τ)) := by
          calc ∑ x ∈ X, siteCommSum H B σ x τ
            _ ≤ ∑ x ∈ X, expWeightY Y R x * maxQuotientExp H Y R B σ τ :=
              Finset.sum_le_sum (fun x _ => siteCommSum_le_mul_maxQuotientExp H Y R B σ x τ)
            _ = (∑ x ∈ X, expWeightY Y R x) * maxQuotientExp H Y R B σ τ := by rw [← Finset.sum_mul]
            _ ≤ ((X.card : ℝ) * Real.exp (- (regionDist X Y : ℝ) / (R : ℝ))) *
                  (2 * ‖B‖ * Real.exp 1 * H.s1 0 * Real.exp (K * τ)) :=
              mul_le_mul (sum_expWeightY_regionDist_le X Y hY R) hQ_le
                (maxQuotientExp_nonneg H Y R B σ τ) (by positivity)
        calc ‖dA‖
          _ ≤ 2 * ‖A‖ * ∑ W ∈ Finset.univ.filter (fun W => (W ∩ X).Nonempty),
                ‖opCommutator (H.heisenbergEvolve (σ * τ) (H.h W)) B‖ := hd1
          _ ≤ 2 * ‖A‖ * ∑ x ∈ X, siteCommSum H B σ x τ := mul_le_mul_of_nonneg_left hinter h2A_nonneg
          _ ≤ 2 * ‖A‖ * (((X.card : ℝ) * Real.exp (- (regionDist X Y : ℝ) / (R : ℝ))) *
                (2 * ‖B‖ * Real.exp 1 * H.s1 0 * Real.exp (K * τ))) :=
            mul_le_mul_of_nonneg_left hsum_X h2A_nonneg
          _ = B'_LR τ := by dsimp [B'_LR, C_LR, K]; ring
      have hd_lt : (∑ _u ∈ ({()} : Finset Unit), ‖dA‖) < r := by
        rw [Finset.sum_singleton]; exact lt_of_le_of_lt hd_norm_le hr
      have ev := eventually_slope_sum_norm_lt ({()} : Finset Unit)
        (fun _ z => psiOp H X A B σ τ z) (fun _ => dA) τ (fun _ _ => hd_psi) hd_lt
      refine (ev.mono (fun z hz => ?_)).frequently
      rw [Finset.sum_singleton, Finset.sum_singleton,
        norm_psiOp_eq H X A B σ τ z, norm_psiOp_eq H X A B σ τ τ] at hz
      rw [slope_def_field, div_eq_inv_mul]; exact hz
    have h_final := image_le_of_liminf_slope_right_le_deriv_boundary
      hf_cont hf0 hB_cont hB_within h_slope (Set.right_mem_Icc.mpr (abs_nonneg t))
    dsimp [f, B_LR] at h_final; rw [hσ_mul] at h_final
    have hC_nn : 0 ≤ C_LR := by dsimp [C_LR]; positivity
    calc ‖opCommutator (H.heisenbergEvolve t A) B‖
      _ ≤ C_LR * (Real.exp (K * |t|) - 1) := h_final
      _ ≤ C_LR * Real.exp (K * |t|) := mul_le_mul_of_nonneg_left (by linarith) hC_nn

end
