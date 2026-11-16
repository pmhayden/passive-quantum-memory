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
import Proofs.BoxMetricAndCollarLemmas
import Proofs.SupportAndCondExpLemmas
import Proofs.LiebRobinson.DuhamelAndGronwall

/-!
# Autonomous Hastings–Koma Lieb–Robinson Series on Open Boxes

Iterates the interaction-picture Duhamel inequality via Picard–Dyson series to prove the autonomous Hastings–Koma Lieb–Robinson commutator bound `hastings_koma_lieb_robinson_box` and the resulting conditional-expectation light-cone bound `norm_heisenbergFlow_sub_condExp_le_of_lieb_robinson` on open-box lattices `BoxD D L`.

## References

* Part I, Section 6.2 (`subsec:bochner-lr`), Equation (70) (`eq:hastings-koma-lr`)
* Hastings–Koma (2006), Communications in Mathematical Physics 265, 781–804
-/

noncomputable section

open scoped Classical InnerProduct ComplexConjugate BigOperators
open Filter Topology Asymptotics ContinuousLinearMap

/-! ## 1. One-Step Support Overlap Commutator Sum & Slope Helpers -/

lemma opCommutator_eq_zero_of_disjoint {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    {X Y : Finset (BoxD D L)} (hDisj : Disjoint X Y)
    {A B : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site}
    (hA : IsSupportedOn Site X A) (hB : IsSupportedOn Site Y B) :
    opCommutator A B = 0 :=
  sub_eq_zero.mpr (commute_of_isSupportedOn_disjoint hDisj hA hB)

lemma LatticeHamiltonian.opCommutator_H_tot_sub_regionInteraction_eq_zero {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    (H : LatticeHamiltonian D L Site) {X : Finset (BoxD D L)}
    {A : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site}
    (hA : IsSupportedOn Site X A) :
    opCommutator (H.totalHamiltonian - H.regionInteraction X) A = 0 := by
  have h_sub : H.totalHamiltonian - H.regionInteraction X =
      ∑ Z ∈ Finset.univ.filter (fun Z : Finset (BoxD D L) => ¬(Z ∩ X).Nonempty), H.h Z := by
    unfold LatticeHamiltonian.totalHamiltonian LatticeHamiltonian.regionInteraction
    rw [sub_eq_iff_eq_add, add_comm, Finset.sum_filter_add_sum_filter_not]
  rw [h_sub]; unfold opCommutator
  rw [Finset.sum_mul, Finset.mul_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_eq_zero (fun Z hZ => ?_)
  rw [Finset.mem_filter] at hZ
  have hdisj : Disjoint Z X :=
    Finset.disjoint_iff_inter_eq_empty.mpr (Finset.not_nonempty_iff_eq_empty.mp hZ.2)
  exact opCommutator_eq_zero_of_disjoint hdisj (H.is_supported Z) hA

/-- If $A$ is supported on $X \subseteq \mathrm{BoxD}\ D\ L$, the commutator $[H_{\Lambda_L}, A]$
    only receives contributions from local terms $h_Z$ whose support $Z$ intersects $X$. -/
lemma opCommutator_H_tot_eq_sum_inter {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    (H : LatticeHamiltonian D L Site) {X : Finset (BoxD D L)}
    {A : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site}
    (hA : IsSupportedOn Site X A) :
    opCommutator H.totalHamiltonian A =
      ∑ Z ∈ Finset.univ.filter (fun Z : Finset (BoxD D L) => ¬Disjoint Z X),
        opCommutator (H.h Z) A := by
  unfold LatticeHamiltonian.totalHamiltonian
  rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun Z : Finset (BoxD D L) => ¬Disjoint Z X)]
  unfold opCommutator; rw [add_mul, mul_add, add_sub_add_comm]
  have h_zero : (∑ x ∈ Finset.univ.filter (fun Z => ¬¬Disjoint Z X), H.h x) * A -
      A * (∑ x ∈ Finset.univ.filter (fun Z => ¬¬Disjoint Z X), H.h x) = 0 := by
    rw [Finset.sum_mul, Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_eq_zero (fun Z hZ => ?_)
    rw [Finset.mem_filter, not_not] at hZ
    exact opCommutator_eq_zero_of_disjoint hZ.2 (H.is_supported Z) hA
  rw [h_zero, add_zero, Finset.sum_mul, Finset.mul_sum, ← Finset.sum_sub_distrib]

lemma eventually_slope_sum_norm_lt {α E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (s : Finset α) (f : α → ℝ → E) (f' : α → E) (τ : ℝ)
    (hf : ∀ a ∈ s, HasDerivAt (f a) (f' a) τ) {R : ℝ} (hR : (∑ a ∈ s, ‖f' a‖) < R) :
    ∀ᶠ z in 𝓝[>] τ, (z - τ)⁻¹ * ((∑ a ∈ s, ‖f a z‖) - (∑ a ∈ s, ‖f a τ‖)) < R := by
  induction s using Finset.cons_induction generalizing R with
  | empty =>
    simp only [Finset.sum_empty, sub_self, mul_zero] at hR ⊢
    exact Filter.Eventually.of_forall (fun _ => hR)
  | cons a s ha ih =>
    rw [Finset.sum_cons] at hR
    set δ := (R - (‖f' a‖ + ∑ x ∈ s, ‖f' x‖)) / 2
    have hδ : 0 < δ := by dsimp [δ]; linarith
    have ha_lt : ‖f' a‖ < ‖f' a‖ + δ := by linarith
    have hs_lt : (∑ x ∈ s, ‖f' x‖) < R - (‖f' a‖ + δ) := by dsimp [δ]; linarith
    have ev_a : ∀ᶠ z in 𝓝[>] τ, (z - τ)⁻¹ * (‖f a z‖ - ‖f a τ‖) < ‖f' a‖ + δ := by
      have h1 := ((hf a (Finset.mem_cons_self a s)).hasDerivWithinAt (s := Set.Ioi τ)).limsup_slope_norm_le ha_lt
      refine h1.mp (Filter.Eventually.mono self_mem_nhdsWithin (fun z hz hlt => ?_))
      rwa [Real.norm_eq_abs, abs_of_pos (sub_pos.mpr hz)] at hlt
    have ev_s := ih (fun b hb => hf b (Finset.mem_cons.mpr (Or.inr hb))) hs_lt
    refine (ev_a.and ev_s).mono (fun z ⟨hza, hzs⟩ => ?_)
    rw [Finset.sum_cons, Finset.sum_cons]
    calc (z - τ)⁻¹ * ((‖f a z‖ + ∑ x ∈ s, ‖f x z‖) - (‖f a τ‖ + ∑ x ∈ s, ‖f x τ‖))
      _ = (z - τ)⁻¹ * (‖f a z‖ - ‖f a τ‖) + (z - τ)⁻¹ * ((∑ x ∈ s, ‖f x z‖) - (∑ x ∈ s, ‖f x τ‖)) := by ring
      _ < (‖f' a‖ + δ) + (R - (‖f' a‖ + δ)) := add_lt_add hza hzs
      _ = R := by ring

lemma sum_filter_inter_nonempty_le {D L : ℕ}
    (Z : Finset (BoxD D L)) (g : Finset (BoxD D L) → ℝ) (hg : ∀ W, 0 ≤ g W) :
    ∑ W ∈ Finset.univ.filter (fun W : Finset (BoxD D L) => (W ∩ Z).Nonempty), g W ≤
      ∑ z ∈ Z, ∑ W ∈ Finset.univ.filter (fun W : Finset (BoxD D L) => z ∈ W), g W := by
  have h1 : ∀ W ∈ Finset.univ.filter (fun W : Finset (BoxD D L) => (W ∩ Z).Nonempty),
      g W ≤ ∑ z ∈ Z, if z ∈ W then g W else 0 := by
    intro W hW; rw [Finset.mem_filter] at hW; rcases hW.2 with ⟨z0, hz0⟩
    rw [Finset.mem_inter] at hz0; rw [← Finset.sum_filter]
    exact Finset.single_le_sum (f := fun _ => g W) (fun _ _ => hg W)
      (Finset.mem_filter.mpr ⟨hz0.2, hz0.1⟩)
  calc ∑ W ∈ Finset.univ.filter (fun W : Finset (BoxD D L) => (W ∩ Z).Nonempty), g W
    _ ≤ ∑ W ∈ Finset.univ.filter (fun W : Finset (BoxD D L) => (W ∩ Z).Nonempty),
          ∑ z ∈ Z, if z ∈ W then g W else 0 := Finset.sum_le_sum h1
    _ ≤ ∑ W ∈ (Finset.univ : Finset (Finset (BoxD D L))),
          ∑ z ∈ Z, if z ∈ W then g W else 0 :=
      Finset.sum_le_univ_sum_of_nonneg (fun W =>
        Finset.sum_nonneg (fun z _ => by split_ifs <;> [exact hg W; exact le_rfl]))
    _ = ∑ z ∈ Z, ∑ W ∈ (Finset.univ : Finset (Finset (BoxD D L))),
          if z ∈ W then g W else 0 := Finset.sum_comm
    _ = ∑ z ∈ Z, ∑ W ∈ Finset.univ.filter (fun W : Finset (BoxD D L) => z ∈ W), g W :=
      Finset.sum_congr rfl (fun z _ => by rw [Finset.sum_filter])

lemma continuous_finset_sup' {ι : Type*} (s : Finset ι) (H : s.Nonempty)
    (f : ι → ℝ → ℝ) (hf : ∀ i ∈ s, Continuous (f i)) :
    Continuous (fun z : ℝ => s.sup' H (fun i => f i z)) := by
  have h := Finset.sup'_induction (s := s) (H := H) (f := f) (p := Continuous)
    (fun _ h1 _ h2 => h1.max h2) hf
  have h_eq : s.sup' H f = (fun z : ℝ => s.sup' H (fun i => f i z)) :=
    funext (fun z => Finset.sup'_apply H f z)
  rwa [h_eq] at h

lemma eventually_slope_sup'_lt {ι : Type*} [Fintype ι] [Nonempty ι]
    (q : ι → ℝ → ℝ) (τ r : ℝ)
    (hq : ∀ i : ι, ∀ᶠ z in 𝓝[>] τ, (z - τ)⁻¹ * (q i z - q i τ) < r) :
    ∀ᶠ z in 𝓝[>] τ,
      (z - τ)⁻¹ * ((Finset.univ.sup' Finset.univ_nonempty (fun i => q i z)) -
        (Finset.univ.sup' Finset.univ_nonempty (fun i => q i τ))) < r := by
  refine ((Filter.eventually_all.mpr hq).and self_mem_nhdsWithin).mono (fun z ⟨hz, hzt⟩ => ?_)
  have hpos : 0 < (z - τ)⁻¹ := inv_pos.mpr (sub_pos.mpr hzt)
  rcases Finset.exists_mem_eq_sup' Finset.univ_nonempty (fun i => q i z) with ⟨i0, hi0, hsup⟩
  rw [hsup]
  have hle : q i0 τ ≤ Finset.univ.sup' Finset.univ_nonempty (fun i => q i τ) :=
    Finset.le_sup' (fun i => q i τ) hi0
  calc (z - τ)⁻¹ * (q i0 z - Finset.univ.sup' Finset.univ_nonempty (fun i => q i τ))
    _ ≤ (z - τ)⁻¹ * (q i0 z - q i0 τ) :=
      mul_le_mul_of_nonneg_left (sub_le_sub_left hle (q i0 z)) (le_of_lt hpos)
    _ < r := hz i0

lemma continuous_norm_opCommutator_heisenbergEvolve {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    (H : LatticeHamiltonian D L Site) {Z : Finset (BoxD D L)}
    {O : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site}
    (hO : IsSupportedOn Site Z O)
    (B : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site) (σ : ℝ) :
    Continuous (fun z : ℝ => ‖opCommutator (H.heisenbergEvolve (σ * z) O) B‖) := by
  rw [continuous_iff_continuousAt]; intro τ
  have h1 : ContinuousAt (fun z : ℝ => ‖psiOp H Z O B σ τ z‖) τ :=
    (hasDerivAt_psiOp H (H.opCommutator_H_tot_sub_regionInteraction_eq_zero hO) B σ τ).continuousAt.norm
  have h2 : (fun z : ℝ => ‖psiOp H Z O B σ τ z‖) =
      (fun z : ℝ => ‖opCommutator (H.heisenbergEvolve (σ * z) O) B‖) :=
    funext (fun z => norm_psiOp_eq H Z O B σ τ z)
  rwa [h2] at h1

lemma hasDerivAt_real_exp_const_mul (c x : ℝ) :
    HasDerivAt (fun u : ℝ => Real.exp (c * u)) (c * Real.exp (c * x)) x := by
  have h1 := _root_.hasDerivAt_exp_smul_const' (𝕂 := ℝ) c x
  have h_fn : (fun u : ℝ => NormedSpace.exp (u • c)) = (fun u : ℝ => Real.exp (c * u)) := by
    funext u; rw [Real.exp_eq_exp_ℝ, smul_eq_mul, mul_comm]
  rw [h_fn] at h1
  refine h1.congr_deriv ?_
  rw [Real.exp_eq_exp_ℝ, smul_eq_mul, mul_comm x c]

lemma le_exp_of_eventually_slope_lt {f : ℝ → ℝ} {δ K T : ℝ}
    (hf_cont : ContinuousOn f (Set.Icc 0 T)) (hf0 : f 0 ≤ δ)
    (h_slope : ∀ τ ∈ Set.Ico 0 T, ∀ r, K * f τ < r →
      ∀ᶠ z in 𝓝[>] τ, (z - τ)⁻¹ * (f z - f τ) < r)
    {τ : ℝ} (hτ : τ ∈ Set.Icc 0 T) :
    f τ ≤ δ * Real.exp (K * τ) := by
  have H : ∀ ε' > 0, f τ ≤ δ * Real.exp (K * τ) + ε' * Real.exp ((K + 1) * τ) := by
    intro ε' hε'
    set B : ℝ → ℝ := fun u => δ * Real.exp (K * u) + ε' * Real.exp ((K + 1) * u)
    set B' : ℝ → ℝ := fun u => δ * (K * Real.exp (K * u)) + ε' * ((K + 1) * Real.exp ((K + 1) * u))
    have hB_deriv : ∀ u : ℝ, HasDerivAt B (B' u) u := fun u =>
      ((hasDerivAt_real_exp_const_mul K u).const_mul δ).add
        ((hasDerivAt_real_exp_const_mul (K + 1) u).const_mul ε')
    apply image_le_of_liminf_slope_right_lt_deriv_boundary hf_cont
      (fun u hu r hr => by simpa [slope_def_field, div_eq_inv_mul] using (h_slope u hu r hr).frequently)
      (by dsimp [B]; simp only [mul_zero, Real.exp_zero, mul_one]; linarith)
      hB_deriv
      (fun u _ hfu => by
        rw [hfu]; dsimp [B, B']
        have hpos : 0 < ε' * Real.exp ((K + 1) * u) := mul_pos hε' (Real.exp_pos _)
        linarith)
      hτ
  by_contra hlt; push_neg at hlt
  have hexp_pos : 0 < Real.exp ((K + 1) * τ) := Real.exp_pos _
  set ε' := (f τ - δ * Real.exp (K * τ)) / (2 * Real.exp ((K + 1) * τ))
  have hle := H ε' (div_pos (sub_pos.mpr hlt) (by positivity))
  have h_mul : ε' * Real.exp ((K + 1) * τ) = (f τ - δ * Real.exp (K * τ)) / 2 := by
    dsimp [ε']; rw [div_mul_eq_mul_div, mul_div_mul_right _ _ (ne_of_gt hexp_pos)]
  linarith

/-! ## 2. Hastings–Koma Theorem A.1 Polynomial-Decay Lieb–Robinson Bound on `BoxD D L` -/

lemma regionDist_le_boxDist {D L : ℕ} {X Y : Finset (BoxD D L)} {x y : BoxD D L}
    (hx : x ∈ X) (hy : y ∈ Y) : regionDist X Y ≤ boxDist x y := by
  dsimp [regionDist]
  have hne : X.Nonempty ∧ Y.Nonempty := ⟨⟨x, hx⟩, ⟨y, hy⟩⟩
  rw [dif_pos hne]
  exact Finset.inf'_le (fun p : BoxD D L × BoxD D L => boxDist p.1 p.2) (Finset.mk_mem_product hx hy)

lemma boxDist_le_regionDiam {D L : ℕ} {Z : Finset (BoxD D L)} {x y : BoxD D L}
    (hx : x ∈ Z) (hy : y ∈ Z) : boxDist x y ≤ regionDiam Z := by
  dsimp [regionDiam]
  exact Finset.le_sup (f := fun p : BoxD D L × BoxD D L => boxDist p.1 p.2)
    (Finset.mk_mem_product hx hy)

lemma disjoint_of_regionDist_pos {D L : ℕ} {X Y : Finset (BoxD D L)}
    (h : 0 < regionDist X Y) : Disjoint X Y := by
  rw [Finset.disjoint_left]; intro x hxX hxY
  have hle := regionDist_le_boxDist hxX hxY
  rw [boxDist_self] at hle; omega

lemma boxRegionDist_le_regionDiam_add {D L : ℕ} {Y Z : Finset (BoxD D L)} (hY : Y.Nonempty)
    {x z : BoxD D L} (hx : x ∈ Z) (hz : z ∈ Z) :
    boxRegionDist x Y ≤ regionDiam Z + boxRegionDist z Y := by
  suffices h_sub : ∀ k, k ≤ boxRegionDist x Y → k - regionDiam Z ≤ boxRegionDist z Y by
    have := h_sub (boxRegionDist x Y) le_rfl
    omega
  intro k hk
  dsimp [boxRegionDist, regionDist]
  have hne : ({z} : Finset (BoxD D L)).Nonempty ∧ Y.Nonempty :=
    ⟨Finset.singleton_nonempty z, hY⟩
  rw [dif_pos hne, Finset.le_inf'_iff]
  intro p hp
  rcases Finset.mem_product.mp hp with ⟨hp1, hp2⟩
  rw [Finset.mem_singleton] at hp1
  have h1 : boxRegionDist x Y ≤ boxDist x p.2 :=
    regionDist_le_boxDist (Finset.mem_singleton_self x) hp2
  have h2 : boxDist x p.2 ≤ boxDist x p.1 + boxDist p.1 p.2 := boxDist_triangle x p.1 p.2
  have h3 : boxDist x p.1 ≤ regionDiam Z := hp1 ▸ boxDist_le_regionDiam hx hz
  omega

/-- Point-to-set polynomial spatial decay weight $w_Y(x) = (1 + d_Y(x)/2)^{-\eta}$ on `BoxD D L`. -/
def weightY {D L : ℕ} (Y : Finset (BoxD D L)) (η : ℝ) (x : BoxD D L) : ℝ :=
  1 / (1 + (boxRegionDist x Y : ℝ) / 2) ^ η

lemma weightY_pos {D L : ℕ} (Y : Finset (BoxD D L)) (η : ℝ) (x : BoxD D L) :
    0 < weightY Y η x := by
  unfold weightY; exact one_div_pos.mpr (Real.rpow_pos_of_pos (by positivity) η)

lemma poly_diam_weightY_le {D L : ℕ}
    {Y Z : Finset (BoxD D L)} (hY : Y.Nonempty) (x z : BoxD D L) {η : ℝ} (hη : 0 ≤ η)
    (hx : x ∈ Z) (hz : z ∈ Z) :
    weightY Y η z ≤ (1 + (regionDiam Z : ℝ)) ^ η * weightY Y η x := by
  unfold weightY
  have h_dist : (boxRegionDist x Y : ℝ) ≤ (regionDiam Z : ℝ) + (boxRegionDist z Y : ℝ) := by
    exact_mod_cast boxRegionDist_le_regionDiam_add hY hx hz
  have hD_nonneg : (0 : ℝ) ≤ (regionDiam Z : ℝ) := Nat.cast_nonneg _
  have hdz_nonneg : (0 : ℝ) ≤ (boxRegionDist z Y : ℝ) := Nat.cast_nonneg _
  have h_base_le : 1 + (boxRegionDist x Y : ℝ) / 2 ≤
      (1 + (regionDiam Z : ℝ)) * (1 + (boxRegionDist z Y : ℝ) / 2) := by nlinarith
  have h_rpow_le : (1 + (boxRegionDist x Y : ℝ) / 2) ^ η ≤
      (1 + (regionDiam Z : ℝ)) ^ η * (1 + (boxRegionDist z Y : ℝ) / 2) ^ η := by
    calc (1 + (boxRegionDist x Y : ℝ) / 2) ^ η
      _ ≤ ((1 + (regionDiam Z : ℝ)) * (1 + (boxRegionDist z Y : ℝ) / 2)) ^ η :=
        Real.rpow_le_rpow (by positivity) h_base_le hη
      _ = (1 + (regionDiam Z : ℝ)) ^ η * (1 + (boxRegionDist z Y : ℝ) / 2) ^ η :=
        Real.mul_rpow (by positivity) (by positivity)
  have hpos_x : 0 < (1 + (boxRegionDist x Y : ℝ) / 2) ^ η := Real.rpow_pos_of_pos (by positivity) η
  have hpos_z : 0 < (1 + (boxRegionDist z Y : ℝ) / 2) ^ η := Real.rpow_pos_of_pos (by positivity) η
  rw [mul_one_div, div_le_div_iff₀ hpos_z hpos_x]; linarith

lemma sum_weightY_le {D L : ℕ}
    {Y Z : Finset (BoxD D L)} (hY : Y.Nonempty) (x : BoxD D L) {η : ℝ} (hη : 0 ≤ η) (hx : x ∈ Z) :
    ∑ z ∈ Z, weightY Y η z ≤ (Z.card : ℝ) * (1 + (regionDiam Z : ℝ)) ^ η * weightY Y η x := by
  calc ∑ z ∈ Z, weightY Y η z
    _ ≤ ∑ _z ∈ Z, (1 + (regionDiam Z : ℝ)) ^ η * weightY Y η x :=
      Finset.sum_le_sum (fun z hz => poly_diam_weightY_le hY x z hη hx hz)
    _ = (Z.card : ℝ) * (1 + (regionDiam Z : ℝ)) ^ η * weightY Y η x := by
      rw [Finset.sum_const, nsmul_eq_mul]; ring

lemma sum_weightY_regionDist_le {D L : ℕ}
    (X Y : Finset (BoxD D L)) (hY : Y.Nonempty) {η : ℝ} (hη : 0 ≤ η) :
    ∑ x ∈ X, weightY Y η x ≤ (X.card : ℝ) / (1 + (regionDist X Y : ℝ) / 2) ^ η := by
  have hx_le : ∀ x ∈ X, weightY Y η x ≤ 1 / (1 + (regionDist X Y : ℝ) / 2) ^ η := by
    intro x hx; unfold weightY
    have hd_nat : regionDist X Y ≤ boxRegionDist x Y := by
      suffices h_le : ∀ k, k ≤ regionDist X Y → k ≤ boxRegionDist x Y from h_le _ le_rfl
      intro k hk
      dsimp [boxRegionDist, regionDist]
      have hne : ({x} : Finset (BoxD D L)).Nonempty ∧ Y.Nonempty :=
        ⟨Finset.singleton_nonempty x, hY⟩
      rw [dif_pos hne, Finset.le_inf'_iff]
      intro p hp
      rcases Finset.mem_product.mp hp with ⟨hp1, hp2⟩
      rw [Finset.mem_singleton] at hp1
      have h1 : regionDist X Y ≤ boxDist p.1 p.2 := hp1 ▸ regionDist_le_boxDist hx hp2
      omega
    have hd : (regionDist X Y : ℝ) ≤ (boxRegionDist x Y : ℝ) := Nat.cast_le.mpr hd_nat
    exact one_div_le_one_div_of_le (Real.rpow_pos_of_pos (by positivity) η)
      (Real.rpow_le_rpow (by positivity) (by linarith) hη)
  calc ∑ x ∈ X, weightY Y η x
    _ ≤ ∑ _x ∈ X, 1 / (1 + (regionDist X Y : ℝ) / 2) ^ η := Finset.sum_le_sum hx_le
    _ = (X.card : ℝ) / (1 + (regionDist X Y : ℝ) / 2) ^ η := by
      rw [Finset.sum_const, nsmul_eq_mul]; ring

def siteCommSum {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    (H : LatticeHamiltonian D L Site)
    (B : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site)
    (σ : ℝ) (x : BoxD D L) (τ : ℝ) : ℝ :=
  ∑ Z ∈ Finset.univ.filter (fun Z : Finset (BoxD D L) => x ∈ Z),
    ‖opCommutator (H.heisenbergEvolve (σ * τ) (H.h Z)) B‖

def siteQuotient {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    (H : LatticeHamiltonian D L Site) (Y : Finset (BoxD D L)) (η : ℝ)
    (B : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site)
    (σ : ℝ) (x : BoxD D L) (τ : ℝ) : ℝ :=
  (weightY Y η x)⁻¹ * siteCommSum H B σ x τ

def maxQuotient {D L : ℕ} [NeZero D] [NeZero L]
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    (H : LatticeHamiltonian D L Site) (Y : Finset (BoxD D L)) (η : ℝ)
    (B : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site)
    (σ : ℝ) (τ : ℝ) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty (fun x => siteQuotient H Y η B σ x τ)

lemma siteCommSum_nonneg {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    (H : LatticeHamiltonian D L Site)
    (B : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site)
    (σ : ℝ) (x : BoxD D L) (τ : ℝ) : 0 ≤ siteCommSum H B σ x τ :=
  Finset.sum_nonneg (fun _ _ => norm_nonneg _)

lemma maxQuotient_nonneg {D L : ℕ} [NeZero D] [NeZero L]
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    (H : LatticeHamiltonian D L Site) (Y : Finset (BoxD D L)) (η : ℝ)
    (B : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site)
    (σ : ℝ) (τ : ℝ) : 0 ≤ maxQuotient H Y η B σ τ := by
  have x0 : BoxD D L := fun _ => ⟨0, NeZero.pos L⟩
  have h0 : 0 ≤ siteQuotient H Y η B σ x0 τ :=
    mul_nonneg (inv_nonneg.mpr (le_of_lt (weightY_pos Y η x0))) (siteCommSum_nonneg H B σ x0 τ)
  exact le_trans h0 (Finset.le_sup' (fun x => siteQuotient H Y η B σ x τ) (Finset.mem_univ x0))

lemma siteCommSum_le_mul_maxQuotient {D L : ℕ} [NeZero D] [NeZero L]
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    (H : LatticeHamiltonian D L Site) (Y : Finset (BoxD D L)) (η : ℝ)
    (B : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site)
    (σ : ℝ) (x : BoxD D L) (τ : ℝ) :
    siteCommSum H B σ x τ ≤ weightY Y η x * maxQuotient H Y η B σ τ := by
  have hw : 0 < weightY Y η x := weightY_pos Y η x
  have hq : siteQuotient H Y η B σ x τ ≤ maxQuotient H Y η B σ τ :=
    Finset.le_sup' (fun z => siteQuotient H Y η B σ z τ) (Finset.mem_univ x)
  have hmul := mul_le_mul_of_nonneg_left hq (le_of_lt hw)
  unfold siteQuotient at hmul
  rwa [← mul_assoc, mul_inv_cancel₀ (ne_of_gt hw), one_mul] at hmul

lemma siteCommSum_zero_le {D L : ℕ} [NeZero D] [NeZero L]
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    (H : LatticeHamiltonian D L Site) {Y : Finset (BoxD D L)}
    {B : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site}
    (hB : IsSupportedOn Site Y B) {η : ℝ} (hη : 0 ≤ η) (σ : ℝ) (x : BoxD D L) :
    siteCommSum H B σ x 0 ≤ 2 * ‖B‖ * H.s1 η * weightY Y η x := by
  unfold siteCommSum
  have hev0 : ∀ Z, H.heisenbergEvolve (σ * 0) (H.h Z) = H.h Z := fun Z => by
    unfold LatticeHamiltonian.heisenbergEvolve heisenbergFlow
    rw [mul_zero, neg_zero, timeEvolutionOp_zero, one_mul, mul_one]
  simp only [hev0]
  have hterm : ∀ Z ∈ Finset.univ.filter (fun Z : Finset (BoxD D L) => x ∈ Z),
      ‖opCommutator (H.h Z) B‖ ≤ 2 * ‖B‖ * weightY Y η x *
        (‖H.h Z‖ * (Z.card : ℝ) * (1 + (regionDiam Z : ℝ)) ^ η) := by
    intro Z hZ; rw [Finset.mem_filter] at hZ
    by_cases hdisj : Disjoint Z Y
    · rw [opCommutator_eq_zero_of_disjoint hdisj (H.is_supported Z) hB, norm_zero]
      have hw : 0 ≤ weightY Y η x := le_of_lt (weightY_pos Y η x)
      positivity
    · rw [Finset.not_disjoint_iff] at hdisj; rcases hdisj with ⟨y, hyZ, hyY⟩
      have hcomm : ‖opCommutator (H.h Z) B‖ ≤ 2 * ‖H.h Z‖ * ‖B‖ := norm_opCommutator_le _ _
      have hd : (boxRegionDist x Y : ℝ) ≤ (regionDiam Z : ℝ) :=
        Nat.cast_le.mpr (le_trans (regionDist_le_boxDist (Finset.mem_singleton_self x) hyY)
          (boxDist_le_regionDiam hZ.2 hyZ))
      have hcard : (1 : ℝ) ≤ (Z.card : ℝ) := Nat.one_le_cast.mpr (Finset.card_pos.mpr ⟨x, hZ.2⟩)
      have hpos : 0 < (1 + (boxRegionDist x Y : ℝ) / 2) ^ η := Real.rpow_pos_of_pos (by positivity) η
      have hrpow : (1 + (boxRegionDist x Y : ℝ) / 2) ^ η ≤ (1 + (regionDiam Z : ℝ)) ^ η :=
        Real.rpow_le_rpow (by positivity) (by linarith) hη
      have h1 : 1 ≤ weightY Y η x * ((Z.card : ℝ) * (1 + (regionDiam Z : ℝ)) ^ η) := by
        unfold weightY; rw [one_div, le_inv_mul_iff₀ hpos]
        nlinarith [Real.rpow_pos_of_pos (by positivity : 0 < 1 + (regionDiam Z : ℝ)) η]
      calc ‖opCommutator (H.h Z) B‖
        _ ≤ 2 * ‖H.h Z‖ * ‖B‖ * 1 := by linarith
        _ ≤ 2 * ‖H.h Z‖ * ‖B‖ *
            (weightY Y η x * ((Z.card : ℝ) * (1 + (regionDiam Z : ℝ)) ^ η)) := by gcongr
        _ = 2 * ‖B‖ * weightY Y η x *
            (‖H.h Z‖ * (Z.card : ℝ) * (1 + (regionDiam Z : ℝ)) ^ η) := by ring
  calc ∑ Z ∈ Finset.univ.filter (fun Z : Finset (BoxD D L) => x ∈ Z), ‖opCommutator (H.h Z) B‖
    _ ≤ ∑ Z ∈ Finset.univ.filter (fun Z : Finset (BoxD D L) => x ∈ Z),
          2 * ‖B‖ * weightY Y η x *
            (‖H.h Z‖ * (Z.card : ℝ) * (1 + (regionDiam Z : ℝ)) ^ η) := Finset.sum_le_sum hterm
    _ = 2 * ‖B‖ * weightY Y η x *
          ∑ Z ∈ Finset.univ.filter (fun Z : Finset (BoxD D L) => x ∈ Z),
            ‖H.h Z‖ * (Z.card : ℝ) * (1 + (regionDiam Z : ℝ)) ^ η := by rw [← Finset.mul_sum]
    _ ≤ 2 * ‖B‖ * weightY Y η x * H.s1 η := by
      refine mul_le_mul_of_nonneg_left ?_
        (mul_nonneg (by positivity) (le_of_lt (weightY_pos Y η x)))
      unfold LatticeHamiltonian.s1
      exact Finset.le_sup' (f := fun z => ∑ Z ∈ Finset.univ.filter (fun Z => z ∈ Z),
        ‖H.h Z‖ * (Z.card : ℝ) * (1 + (regionDiam Z : ℝ)) ^ η) (Finset.mem_univ x)
    _ = 2 * ‖B‖ * H.s1 η * weightY Y η x := by ring

lemma maxQuotient_zero_le {D L : ℕ} [NeZero D] [NeZero L]
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    (H : LatticeHamiltonian D L Site) {Y : Finset (BoxD D L)}
    {B : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site}
    (hB : IsSupportedOn Site Y B) {η : ℝ} (hη : 0 ≤ η) (σ : ℝ) :
    maxQuotient H Y η B σ 0 ≤ 2 * ‖B‖ * H.s1 η := by
  unfold maxQuotient; rw [Finset.sup'_le_iff]; intro x _; unfold siteQuotient
  have hw : 0 < weightY Y η x := weightY_pos Y η x
  calc (weightY Y η x)⁻¹ * siteCommSum H B σ x 0
    _ ≤ (weightY Y η x)⁻¹ * (2 * ‖B‖ * H.s1 η * weightY Y η x) :=
      mul_le_mul_of_nonneg_left (siteCommSum_zero_le H hB hη σ x) (inv_nonneg.mpr (le_of_lt hw))
    _ = 2 * ‖B‖ * H.s1 η * ((weightY Y η x)⁻¹ * weightY Y η x) := by ring
    _ = 2 * ‖B‖ * H.s1 η := by rw [inv_mul_cancel₀ (ne_of_gt hw), mul_one]

lemma continuous_maxQuotient {D L : ℕ} [NeZero D] [NeZero L]
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    (H : LatticeHamiltonian D L Site) (Y : Finset (BoxD D L)) (η : ℝ)
    (B : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site) (σ : ℝ) :
    Continuous (maxQuotient H Y η B σ) := by
  unfold maxQuotient
  apply continuous_finset_sup' Finset.univ Finset.univ_nonempty
  intro x _
  unfold siteQuotient siteCommSum
  exact continuous_const.mul (continuous_finset_sum _ (fun Z _ =>
    continuous_norm_opCommutator_heisenbergEvolve H (H.is_supported Z) B σ))

lemma eventually_slope_maxQuotient_lt {D L : ℕ} [NeZero D] [NeZero L]
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    (H : LatticeHamiltonian D L Site) {Y : Finset (BoxD D L)} (hY : Y.Nonempty)
    {η : ℝ} (hη : 0 ≤ η)
    (B : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site)
    {σ : ℝ} (hσ : |σ| = 1) (τ r : ℝ)
    (hr : 2 * H.s1 η * maxQuotient H Y η B σ τ < r) :
    ∀ᶠ z in 𝓝[>] τ, (z - τ)⁻¹ * (maxQuotient H Y η B σ z - maxQuotient H Y η B σ τ) < r := by
  unfold maxQuotient
  apply eventually_slope_sup'_lt (fun x z => siteQuotient H Y η B σ x z) τ r; intro x
  have hw : 0 < weightY Y η x := weightY_pos Y η x
  set Sx := Finset.univ.filter (fun Z : Finset (BoxD D L) => x ∈ Z)
  set f' : Finset (BoxD D L) → ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site :=
    fun Z => opCommutator (H.h Z)
      ((Complex.I * ((-σ : ℝ) : ℂ)) • opCommutator (H.regionInteraction Z) (H.heisenbergEvolve (-σ * τ) B))
  have hf_deriv : ∀ Z ∈ Sx, HasDerivAt (fun z => psiOp H Z (H.h Z) B σ τ z) (f' Z) τ :=
    fun Z _ => hasDerivAt_psiOp H (H.opCommutator_H_tot_sub_regionInteraction_eq_zero (H.is_supported Z)) B σ τ
  have hZ_bound : ∀ Z ∈ Sx, ‖f' Z‖ ≤ 2 * (‖H.h Z‖ * (Z.card : ℝ) * (1 + (regionDiam Z : ℝ)) ^ η) *
      weightY Y η x * maxQuotient H Y η B σ τ := by
    intro Z hZ; rw [Finset.mem_filter] at hZ
    have hd := norm_deriv_psiOp_le H Z (H.h Z) B hσ τ
    have hinter := sum_filter_inter_nonempty_le Z
      (fun W => ‖opCommutator (H.heisenbergEvolve (σ * τ) (H.h W)) B‖) (fun _ => norm_nonneg _)
    have hsum_z : ∑ z ∈ Z, siteCommSum H B σ z τ ≤
        (Z.card : ℝ) * (1 + (regionDiam Z : ℝ)) ^ η * weightY Y η x * maxQuotient H Y η B σ τ := by
      calc ∑ z ∈ Z, siteCommSum H B σ z τ
        _ ≤ ∑ z ∈ Z, weightY Y η z * maxQuotient H Y η B σ τ :=
          Finset.sum_le_sum (fun z _ => siteCommSum_le_mul_maxQuotient H Y η B σ z τ)
        _ = (∑ z ∈ Z, weightY Y η z) * maxQuotient H Y η B σ τ := by rw [← Finset.sum_mul]
        _ ≤ ((Z.card : ℝ) * (1 + (regionDiam Z : ℝ)) ^ η * weightY Y η x) *
              maxQuotient H Y η B σ τ :=
          mul_le_mul_of_nonneg_right (sum_weightY_le hY x hη hZ.2) (maxQuotient_nonneg H Y η B σ τ)
        _ = (Z.card : ℝ) * (1 + (regionDiam Z : ℝ)) ^ η * weightY Y η x *
              maxQuotient H Y η B σ τ := by ring
    calc ‖f' Z‖
      _ ≤ 2 * ‖H.h Z‖ * ∑ W ∈ Finset.univ.filter (fun W => (W ∩ Z).Nonempty),
            ‖opCommutator (H.heisenbergEvolve (σ * τ) (H.h W)) B‖ := hd
      _ ≤ 2 * ‖H.h Z‖ * ∑ z ∈ Z, siteCommSum H B σ z τ :=
        mul_le_mul_of_nonneg_left hinter (by positivity)
      _ ≤ 2 * ‖H.h Z‖ *
          ((Z.card : ℝ) * (1 + (regionDiam Z : ℝ)) ^ η * weightY Y η x * maxQuotient H Y η B σ τ) :=
        mul_le_mul_of_nonneg_left hsum_z (by positivity)
      _ = 2 * (‖H.h Z‖ * (Z.card : ℝ) * (1 + (regionDiam Z : ℝ)) ^ η) *
          weightY Y η x * maxQuotient H Y η B σ τ := by ring
  have hsum_f' : ∑ Z ∈ Sx, ‖f' Z‖ ≤ 2 * H.s1 η * maxQuotient H Y η B σ τ * weightY Y η x := by
    calc ∑ Z ∈ Sx, ‖f' Z‖
      _ ≤ ∑ Z ∈ Sx, 2 * (‖H.h Z‖ * (Z.card : ℝ) * (1 + (regionDiam Z : ℝ)) ^ η) *
            weightY Y η x * maxQuotient H Y η B σ τ := Finset.sum_le_sum hZ_bound
      _ = 2 * (∑ Z ∈ Sx, ‖H.h Z‖ * (Z.card : ℝ) * (1 + (regionDiam Z : ℝ)) ^ η) *
            weightY Y η x * maxQuotient H Y η B σ τ := by
        rw [Finset.mul_sum, Finset.sum_mul, Finset.sum_mul]
      _ ≤ 2 * H.s1 η * weightY Y η x * maxQuotient H Y η B σ τ := by
        have hs1 : ∑ Z ∈ Sx, ‖H.h Z‖ * (Z.card : ℝ) * (1 + (regionDiam Z : ℝ)) ^ η ≤ H.s1 η := by
          unfold LatticeHamiltonian.s1
          exact Finset.le_sup' (f := fun z => ∑ Z ∈ Finset.univ.filter (fun Z => z ∈ Z),
            ‖H.h Z‖ * (Z.card : ℝ) * (1 + (regionDiam Z : ℝ)) ^ η) (Finset.mem_univ x)
        have hpos : 0 ≤ weightY Y η x * maxQuotient H Y η B σ τ :=
          mul_nonneg (le_of_lt hw) (maxQuotient_nonneg H Y η B σ τ)
        nlinarith
      _ = 2 * H.s1 η * maxQuotient H Y η B σ τ * weightY Y η x := by ring
  have hsum_lt : (∑ Z ∈ Sx, ‖f' Z‖) < r * weightY Y η x :=
    lt_of_le_of_lt hsum_f' (mul_lt_mul_of_pos_right hr hw)
  have ev := eventually_slope_sum_norm_lt Sx (fun Z z => psiOp H Z (H.h Z) B σ τ z) f' τ hf_deriv hsum_lt
  refine ev.mono (fun z hz => ?_)
  have h_psi_eq : ∀ u, (∑ Z ∈ Sx, ‖psiOp H Z (H.h Z) B σ τ u‖) = siteCommSum H B σ x u :=
    fun u => Finset.sum_congr rfl (fun Z _ => norm_psiOp_eq H Z (H.h Z) B σ τ u)
  rw [h_psi_eq z, h_psi_eq τ] at hz
  have hz' := mul_lt_mul_of_pos_left hz (inv_pos.mpr hw)
  unfold siteQuotient
  calc (z - τ)⁻¹ * ((weightY Y η x)⁻¹ * siteCommSum H B σ x z - (weightY Y η x)⁻¹ * siteCommSum H B σ x τ)
    _ = (weightY Y η x)⁻¹ * ((z - τ)⁻¹ * (siteCommSum H B σ x z - siteCommSum H B σ x τ)) := by ring
    _ < (weightY Y η x)⁻¹ * (r * weightY Y η x) := hz'
    _ = r * ((weightY Y η x)⁻¹ * weightY Y η x) := by ring
    _ = r := by rw [inv_mul_cancel₀ (ne_of_gt hw), mul_one]

lemma maxQuotient_le_exp {D L : ℕ} [NeZero D] [NeZero L]
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    (H : LatticeHamiltonian D L Site) {Y : Finset (BoxD D L)} (hY : Y.Nonempty)
    {B : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site}
    (hB : IsSupportedOn Site Y B) {η : ℝ} (hη : 0 ≤ η)
    {σ : ℝ} (hσ : |σ| = 1) (T : ℝ) {τ : ℝ} (hτ : τ ∈ Set.Icc 0 T) :
    maxQuotient H Y η B σ τ ≤ 2 * ‖B‖ * H.s1 η * Real.exp (2 * H.s1 η * τ) :=
  le_exp_of_eventually_slope_lt
    (continuous_maxQuotient H Y η B σ).continuousOn
    (maxQuotient_zero_le H hB hη σ)
    (fun u _ r hr => eventually_slope_maxQuotient_lt H hY hη B hσ u r hr)
    hτ

set_option maxHeartbeats 800000 in
/-- **Hastings–Koma Polynomial-Decay Lieb–Robinson Commutator Bound (`hastings_koma_lieb_robinson_box`)**:
    For any local lattice Hamiltonian $H = \sum_{Z \subseteq \mathrm{BoxD}\ D\ L} h_Z$ with polynomial
    interaction constants $s_0(\eta)$ and $s_1(\eta)$, and any operators $A, B \in \mathcal{B}(\mathcal{H})$
    supported on nonempty subsets $X, Y \subseteq \mathrm{BoxD}\ D\ L$,
    $$\|[\tau_t^H(A), B]\| \le
      2 \|A\| \|B\| |X|
      \left(
        \frac{\exp(2 s_1(\eta) |t|) - 1}{(1 + \mathrm{regionDist}(X, Y)/2)^\eta}
        + \exp(2 s_1(\eta) |t|) \, \mathbb{I}_{\{\mathrm{regionDist}(X, Y) = 0\}}
      \right).$$ -/
theorem hastings_koma_lieb_robinson_box
    {D L : ℕ} [NeZero D] [NeZero L]
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    (H : LatticeHamiltonian D L Site) (η : ℝ) (hη : 0 ≤ η)
    (X Y : Finset (BoxD D L)) (hX : X.Nonempty) (hY : Y.Nonempty)
    (A B : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site)
    (hA : IsSupportedOn Site X A) (hB : IsSupportedOn Site Y B) (t : ℝ) :
    ‖opCommutator (H.heisenbergEvolve t A) B‖ ≤
      2 * ‖A‖ * ‖B‖ * (X.card : ℝ) *
        ((Real.exp (2 * H.s1 η * |t|) - 1) /
          (1 + (regionDist X Y : ℝ) / 2) ^ η +
          Real.exp (2 * H.s1 η * |t|) * (if regionDist X Y = 0 then (1 : ℝ) else 0)) := by
  have hs1_nonneg : 0 ≤ H.s1 η := by
    unfold LatticeHamiltonian.s1
    have x0 : BoxD D L := fun _ => ⟨0, NeZero.pos L⟩
    have h0 : 0 ≤ ∑ Z ∈ Finset.univ.filter (fun Z : Finset (BoxD D L) => x0 ∈ Z),
        ‖H.h Z‖ * (Z.card : ℝ) * (1 + (regionDiam Z : ℝ)) ^ η :=
      Finset.sum_nonneg (fun Z _ => by positivity)
    exact le_trans h0 (Finset.le_sup' (f := fun x => ∑ Z ∈ Finset.univ.filter (fun Z => x ∈ Z),
      ‖H.h Z‖ * (Z.card : ℝ) * (1 + (regionDiam Z : ℝ)) ^ η) (Finset.mem_univ x0))
  by_cases h_dist0 : regionDist X Y = 0
  · rw [if_pos h_dist0, mul_one]
    have hcard : (1 : ℝ) ≤ (X.card : ℝ) := Nat.one_le_cast.mpr (Finset.card_pos.mpr hX)
    have hexp_ge : 1 ≤ Real.exp (2 * H.s1 η * |t|) := Real.one_le_exp (by positivity)
    have hdiv_nonneg : 0 ≤ (Real.exp (2 * H.s1 η * |t|) - 1) /
        (1 + (regionDist X Y : ℝ) / 2) ^ η :=
      div_nonneg (by linarith) (le_of_lt (Real.rpow_pos_of_pos (by positivity) η))
    have h_step := norm_commutator_heisenbergFlow_duhamel_step H.isSelfAdjoint_totalHamiltonian A B t
    have h_ab_nonneg : 0 ≤ 2 * ‖A‖ * ‖B‖ := by positivity
    calc ‖opCommutator (H.heisenbergEvolve t A) B‖
      _ ≤ 2 * ‖A‖ * ‖B‖ * 1 * 1 := by rw [mul_one, mul_one]; exact h_step
      _ ≤ 2 * ‖A‖ * ‖B‖ * (X.card : ℝ) *
          ((Real.exp (2 * H.s1 η * |t|) - 1) / (1 + (regionDist X Y : ℝ) / 2) ^ η +
            Real.exp (2 * H.s1 η * |t|)) := by gcongr; linarith
  · rw [if_neg h_dist0, mul_zero, add_zero]
    have h_dist_pos : 0 < regionDist X Y := Nat.pos_of_ne_zero h_dist0
    set σ : ℝ := if 0 ≤ t then 1 else -1
    have hσ_abs : |σ| = 1 := by dsimp [σ]; split_ifs <;> simp
    have hσ_mul : σ * |t| = t := by
      dsimp [σ]; split_ifs with ht
      · rw [one_mul, abs_of_nonneg ht]
      · push_neg at ht; rw [neg_one_mul, abs_of_neg ht, neg_neg]
    set f : ℝ → ℝ := fun τ => ‖opCommutator (H.heisenbergEvolve (σ * τ) A) B‖
    set C_LR : ℝ := 2 * ‖A‖ * ‖B‖ * (X.card : ℝ) / (1 + (regionDist X Y : ℝ) / 2) ^ η
    set B_LR : ℝ → ℝ := fun τ => C_LR * (Real.exp (2 * H.s1 η * τ) - 1)
    set B'_LR : ℝ → ℝ := fun τ => C_LR * (2 * H.s1 η * Real.exp (2 * H.s1 η * τ))
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
      (((hasDerivAt_real_exp_const_mul (2 * H.s1 η) τ).sub_const 1).const_mul C_LR)
    have hB_cont : ContinuousOn B_LR (Set.Icc 0 |t|) :=
      fun τ _ => (hB_deriv τ).continuousAt.continuousWithinAt
    have hB_within : ∀ τ ∈ Set.Ico 0 |t|, HasDerivWithinAt B_LR (B'_LR τ) (Set.Ici τ) τ :=
      fun τ _ => (hB_deriv τ).hasDerivWithinAt
    have h_slope : ∀ τ ∈ Set.Ico 0 |t|, ∀ r, B'_LR τ < r → ∃ᶠ z in 𝓝[>] τ, slope f τ z < r := by
      intro τ hτ r hr
      have hQ_le := maxQuotient_le_exp H hY hB hη hσ_abs |t| (Set.Ico_subset_Icc_self hτ)
      set dA := opCommutator A
        ((Complex.I * ((-σ : ℝ) : ℂ)) • opCommutator (H.regionInteraction X) (H.heisenbergEvolve (-σ * τ) B))
      have hd_psi := hasDerivAt_psiOp H (H.opCommutator_H_tot_sub_regionInteraction_eq_zero hA) B σ τ
      have hd_norm_le : ‖dA‖ ≤ B'_LR τ := by
        have hd1 := norm_deriv_psiOp_le H X A B hσ_abs τ
        have hinter := sum_filter_inter_nonempty_le X
          (fun W => ‖opCommutator (H.heisenbergEvolve (σ * τ) (H.h W)) B‖) (fun _ => norm_nonneg _)
        have h2A_nonneg : 0 ≤ 2 * ‖A‖ := mul_nonneg zero_le_two (norm_nonneg A)
        have hsum_X : ∑ x ∈ X, siteCommSum H B σ x τ ≤
            ((X.card : ℝ) / (1 + (regionDist X Y : ℝ) / 2) ^ η) *
              (2 * ‖B‖ * H.s1 η * Real.exp (2 * H.s1 η * τ)) := by
          calc ∑ x ∈ X, siteCommSum H B σ x τ
            _ ≤ ∑ x ∈ X, weightY Y η x * maxQuotient H Y η B σ τ :=
              Finset.sum_le_sum (fun x _ => siteCommSum_le_mul_maxQuotient H Y η B σ x τ)
            _ = (∑ x ∈ X, weightY Y η x) * maxQuotient H Y η B σ τ := by rw [← Finset.sum_mul]
            _ ≤ ((X.card : ℝ) / (1 + (regionDist X Y : ℝ) / 2) ^ η) *
                  (2 * ‖B‖ * H.s1 η * Real.exp (2 * H.s1 η * τ)) :=
              mul_le_mul (sum_weightY_regionDist_le X Y hY hη) hQ_le
                (maxQuotient_nonneg H Y η B σ τ)
                (div_nonneg (Nat.cast_nonneg _) (le_of_lt (Real.rpow_pos_of_pos (by positivity) η)))
        calc ‖dA‖
          _ ≤ 2 * ‖A‖ * ∑ W ∈ Finset.univ.filter (fun W => (W ∩ X).Nonempty),
                ‖opCommutator (H.heisenbergEvolve (σ * τ) (H.h W)) B‖ := hd1
          _ ≤ 2 * ‖A‖ * ∑ x ∈ X, siteCommSum H B σ x τ :=
            mul_le_mul_of_nonneg_left hinter h2A_nonneg
          _ ≤ 2 * ‖A‖ *
              (((X.card : ℝ) / (1 + (regionDist X Y : ℝ) / 2) ^ η) *
                (2 * ‖B‖ * H.s1 η * Real.exp (2 * H.s1 η * τ))) :=
            mul_le_mul_of_nonneg_left hsum_X h2A_nonneg
          _ = B'_LR τ := by dsimp [B'_LR, C_LR]; ring
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
    dsimp [f, B_LR, C_LR] at h_final; rw [hσ_mul] at h_final
    calc ‖opCommutator (H.heisenbergEvolve t A) B‖
      _ ≤ 2 * ‖A‖ * ‖B‖ * (X.card : ℝ) / (1 + (regionDist X Y : ℝ) / 2) ^ η *
            (Real.exp (2 * H.s1 η * |t|) - 1) := h_final
      _ = 2 * ‖A‖ * ‖B‖ * (X.card : ℝ) *
            ((Real.exp (2 * H.s1 η * |t|) - 1) / (1 + (regionDist X Y : ℝ) / 2) ^ η) := by ring

/-- **Light-Cone Spatial Tail Bound via Conditional Expectation (`norm_heisenbergFlow_sub_condExp_le`)**:
    For an operator $O_A$ supported on a cube $A = \mathrm{boxCube}(x_0, r_0)$ and an enlarged cube
    $B \supseteq A$ at distance $\ell$, the conditional expectation error $\| \tau_t^H(O_A) - \mathbb{E}_B(\tau_t^H(O_A)) \|$
    is controlled by the Lieb–Robinson commutator bound against operators supported on $\Lambda_L \setminus B$. -/
theorem norm_heisenbergFlow_sub_condExp_le_of_lieb_robinson
    {D L : ℕ} [NeZero D] [NeZero L]
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    [∀ x, Nonempty (Site x)]
    (H : LatticeHamiltonian D L Site) (B : Finset (BoxD D L))
    (O : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site)
    (t : ℝ) {ε : ℝ} (hε : 0 ≤ ε)
    (h_comm : ∀ Y : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site,
      IsSupportedOn Site (Finset.univ \ B) Y →
        ‖opCommutator (H.heisenbergEvolve t O) Y‖ ≤ ε * ‖Y‖) :
    ‖H.heisenbergEvolve t O - condExp Site B (H.heisenbergEvolve t O)‖ ≤ ε :=
  norm_sub_condExp_le_of_commutator_bound B (H.heisenbergEvolve t O) hε h_comm
