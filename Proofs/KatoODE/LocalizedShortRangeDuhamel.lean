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

import Proofs.KatoODE.FiniteRangeExponentialLiebRobinson

/-!
# Collar Short-Range Truncation and Conditional Expectation Light-Cone Bound

Defines the collar-localized finite-range Hamiltonian truncation `LatticeHamiltonian.locShort` and proves the conditional expectation light-cone bound `norm_heisenbergEvolve_sub_condExp_le_of_collar`, combining exact support invariance, Duhamel truncation error, finite-range exponential Lieb–Robinson decay, and polynomial interaction-tail bounds.

## References

* Part I, Section 6.2 (`subsec:bochner-lr`), Proposition 6.3 (`prop:bochner-time-convolution`)
* Lieb–Robinson (1972), Communications in Mathematical Physics 28, 251–257
* Bravyi–Hastings–Michalakis (2010), Journal of Mathematical Physics 51, 093512
-/

noncomputable section

open scoped Classical InnerProduct ComplexConjugate BigOperators
open Filter Topology Asymptotics MeasureTheory ContinuousLinearMap

set_option maxRecDepth 200000
set_option maxHeartbeats 800000

/-!
## 1. Exact Support Preservation of `heisenbergFlow` and MVT Duhamel Difference Bound
-/

/-- If both the Hamiltonian $H'$ and the observable $O$ are supported on $B \subseteq \mathrm{BoxD}\ D\ L$,
    then the Heisenberg evolution $\tau_t^{H'}(O)$ is supported on $B$ for all $t \in \mathbb{R}$. -/
theorem isSupportedOn_heisenbergFlow {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    [∀ x, Nonempty (Site x)] {B : Finset (BoxD D L)}
    {H' O : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site}
    (hH' : IsSupportedOn Site B H') (hO : IsSupportedOn Site B O) (t : ℝ) :
    IsSupportedOn Site B (heisenbergFlow H' t O) := by
  have h_sub : ‖heisenbergFlow H' t O - condExp Site B (heisenbergFlow H' t O)‖ ≤ 0 := by
    refine norm_sub_condExp_le_of_commutator_bound B (heisenbergFlow H' t O) le_rfl (fun Y hY => ?_)
    have hH_comm : Commute H' Y := commute_of_isSupportedOn_disjoint Finset.disjoint_sdiff hH' hY
    have hO_comm : Commute O Y := commute_of_isSupportedOn_disjoint Finset.disjoint_sdiff hO hY
    have hU_pos : Commute (timeEvolutionOp H' t) Y :=
      (commute_smul_left_clm hH_comm (Complex.I * (t : ℂ))).exp_left
    have hU_neg : Commute (timeEvolutionOp H' (-t)) Y :=
      (commute_smul_left_clm hH_comm (Complex.I * ((-t : ℝ) : ℂ))).exp_left
    have h_flow : Commute (heisenbergFlow H' t O) Y := (hU_pos.mul_left hO_comm).mul_left hU_neg
    rw [show opCommutator (heisenbergFlow H' t O) Y = 0 from sub_eq_zero.mpr h_flow.eq,
      norm_zero, zero_mul]
  have h_eq : heisenbergFlow H' t O = condExp Site B (heisenbergFlow H' t O) :=
    sub_eq_zero.mp (norm_le_zero_iff.mp h_sub)
  rw [h_eq]; exact isSupportedOn_condExp Site B (heisenbergFlow H' t O)

/-- If $Y$ is supported on $B$, then $\|X - \mathbb{E}_B(X)\| \le 2 \|X - Y\|$. -/
lemma norm_sub_condExp_le_two_mul_norm_sub_of_isSupportedOn {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    [∀ x, Nonempty (Site x)] {B : Finset (BoxD D L)}
    (X : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site)
    {Y : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site} (hY : IsSupportedOn Site B Y) :
    ‖X - condExp Site B X‖ ≤ 2 * ‖X - Y‖ := by
  have hce : condExp Site B Y = Y := condExp_eq_self_of_isSupportedOn hY
  have hsub : condExp Site B (X - Y) = condExp Site B X - Y := by
    change (condExpCLM Site B) (X - Y) = condExp Site B X - Y
    rw [(condExpCLM Site B).map_sub X Y]
    change condExp Site B X - condExp Site B Y = condExp Site B X - Y; rw [hce]
  have hid : X - condExp Site B X = (X - Y) - condExp Site B (X - Y) := by rw [hsub]; abel
  rw [hid]
  have h_le : ‖condExp Site B (X - Y)‖ ≤ ‖X - Y‖ := norm_condExp_le B (X - Y)
  linarith [norm_sub_le (X - Y) (condExp Site B (X - Y))]

/-- Interaction-picture derivative of $u \mapsto \tau_{-u}^{H_1}(\tau_u^{H_2}(O))$. -/
lemma hasDerivAt_heisenbergFlow_neg_comp {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    (H1 H2 O : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site) (u : ℝ) :
    HasDerivAt (fun s : ℝ => heisenbergFlow H1 (-s) (heisenbergFlow H2 s O))
      (heisenbergFlow H1 (-u)
        ((Complex.I : ℂ) • opCommutator (H2 - H1) (heisenbergFlow H2 u O))) u := by
  have d1 := hasDerivAt_timeEvolutionOp_neg_right H1 u
  have d2 := hasDerivAt_heisenbergFlow H2 O u
  have d3 := hasDerivAt_timeEvolutionOp H1 u
  have d123 : HasDerivAt (fun s : ℝ => heisenbergFlow H1 (-s) (heisenbergFlow H2 s O)) _ u :=
    ((d1.mul d2).mul d3).congr_of_eventuallyEq
      (Filter.Eventually.of_forall (fun s : ℝ => by
        change heisenbergFlow H1 (-s) (heisenbergFlow H2 s O) =
          timeEvolutionOp H1 (-s) * heisenbergFlow H2 s O * timeEvolutionOp H1 s
        unfold heisenbergFlow; rw [neg_neg]))
  refine d123.congr_deriv ?_
  dsimp; unfold heisenbergFlow opCommutator; rw [neg_neg]
  simp only [clm_smul_mul_assoc, clm_mul_smul_comm,
    sub_mul, mul_sub, add_mul, smul_sub, mul_assoc]
  simp only [clm_neg_smul]
  abel

/-- **Mean Value Theorem Duhamel Difference Bound (`norm_heisenbergFlow_sub_heisenbergFlow_le`)**:
    For self-adjoint $H_1, H_2$, if $\|[H_1 - H_2, \tau_u^{H_2}(O)]\| \le M$ for all $u \in [-T, T]$
    ($T \ge 0$), then $\|\tau_t^{H_1}(O) - \tau_t^{H_2}(O)\| \le M \cdot T$ for all $t \in [-T, T]$. -/
theorem norm_heisenbergFlow_sub_heisenbergFlow_le {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    {H1 H2 : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site} (hH1 : IsSelfAdjoint H1)
    (O : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site) {T M : ℝ} (hT : 0 ≤ T)
    (hM : ∀ u ∈ Set.Icc (-T) T, ‖opCommutator (H1 - H2) (heisenbergFlow H2 u O)‖ ≤ M)
    {t : ℝ} (ht : t ∈ Set.Icc (-T) T) :
    ‖heisenbergFlow H1 t O - heisenbergFlow H2 t O‖ ≤ M * T := by
  let g : ℝ → (ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site) :=
    fun s => heisenbergFlow H1 (-s) (heisenbergFlow H2 s O)
  let g' : ℝ → (ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site) :=
    fun s => heisenbergFlow H1 (-s) ((Complex.I : ℂ) • opCommutator (H2 - H1) (heisenbergFlow H2 s O))
  have hg0 : g 0 = O := by
    dsimp [g]; unfold heisenbergFlow; simp only [neg_zero, timeEvolutionOp_zero, one_mul, mul_one]
  have h_id : heisenbergFlow H1 (-t) (heisenbergFlow H1 t O - heisenbergFlow H2 t O) = O - g t := by
    dsimp [g]; unfold heisenbergFlow; simp only [mul_sub, sub_mul, neg_neg]
    have h_inv : timeEvolutionOp H1 (-t) *
        (timeEvolutionOp H1 t * O * timeEvolutionOp H1 (-t)) * timeEvolutionOp H1 t = O := by
      calc timeEvolutionOp H1 (-t) * (timeEvolutionOp H1 t * O * timeEvolutionOp H1 (-t)) * timeEvolutionOp H1 t
        _ = (timeEvolutionOp H1 (-t) * timeEvolutionOp H1 t) * O *
            (timeEvolutionOp H1 (-t) * timeEvolutionOp H1 t) := by simp only [mul_assoc]
        _ = 1 * O * 1 := by rw [(timeEvolutionOp_mul_neg H1 t).2]
        _ = O := by simp only [one_mul, mul_one]
    rw [h_inv]
  have h_norm_eq : ‖heisenbergFlow H1 t O - heisenbergFlow H2 t O‖ = ‖g t - g 0‖ := by
    rw [← norm_heisenbergFlow_eq hH1 (-t) (heisenbergFlow H1 t O - heisenbergFlow H2 t O),
      h_id, hg0, norm_sub_rev]
  have h0_mem : (0 : ℝ) ∈ Set.Icc (-T) T := ⟨by linarith, hT⟩
  have h_mvt : ‖g t - g 0‖ ≤ M * ‖t - 0‖ := by
    refine Convex.norm_image_sub_le_of_norm_hasDerivWithin_le (f := g) (f' := g') (s := Set.Icc (-T) T)
      (fun u _ => (hasDerivAt_heisenbergFlow_neg_comp H1 H2 O u).hasDerivWithinAt)
      (fun u hu => ?_) (convex_Icc (-T) T) h0_mem ht
    dsimp [g']; rw [norm_heisenbergFlow_eq hH1 (-u), norm_smul, Complex.norm_I, one_mul]
    have h_neg : opCommutator (H2 - H1) (heisenbergFlow H2 u O) =
        - opCommutator (H1 - H2) (heisenbergFlow H2 u O) := by
      unfold opCommutator; simp only [sub_mul, mul_sub]; abel
    rw [h_neg, norm_neg]; exact hM u hu
  have hM_nn : 0 ≤ M := le_trans (norm_nonneg _) (hM 0 h0_mem)
  have ht_abs : ‖t - 0‖ ≤ T := by rw [sub_zero, Real.norm_eq_abs, abs_le]; exact ht
  rw [h_norm_eq]; exact le_trans h_mvt (mul_le_mul_of_nonneg_left ht_abs hM_nn)

/-!
## 2. Localized Short-Range Hamiltonian `H.locShort B R` & Pointwise Light-Cone Bound
-/

/-- Localized short-range truncation of a lattice Hamiltonian $H$ to terms supported inside $B$
    of diameter at most $R$. -/
def LatticeHamiltonian.locShort {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    (H : LatticeHamiltonian D L Site) (B : Finset (BoxD D L)) (R : ℕ) :
    LatticeHamiltonian D L Site where
  h Z := if Z ⊆ B ∧ regionDiam Z ≤ R then H.h Z else 0
  is_selfAdjoint Z := by
    split_ifs
    · exact H.is_selfAdjoint Z
    · exact IsSelfAdjoint.zero (ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site)
  is_supported Z := by
    split_ifs
    · exact H.is_supported Z
    · exact isSupportedOn_zero Z

lemma isSupportedOn_locShort_H_tot {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    (H : LatticeHamiltonian D L Site) (B : Finset (BoxD D L)) (R : ℕ) :
    IsSupportedOn Site B (H.locShort B R).totalHamiltonian := by
  unfold LatticeHamiltonian.totalHamiltonian
  refine isSupportedOn_finset_sum B Finset.univ (fun Z => (H.locShort B R).h Z) (fun Z _ => ?_)
  dsimp [LatticeHamiltonian.locShort]; split_ifs with hZ
  · exact isSupportedOn_mono hZ.1 (H.is_supported Z)
  · exact isSupportedOn_zero B

lemma locShort_h_eq_zero_of_lt_regionDiam {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    (H : LatticeHamiltonian D L Site) (B : Finset (BoxD D L)) {R : ℕ}
    {Z : Finset (BoxD D L)} (hZ : R < regionDiam Z) :
    (H.locShort B R).h Z = 0 := by
  dsimp [LatticeHamiltonian.locShort]; rw [if_neg]; intro h; omega

lemma sub_locShort_h_eq {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    (H : LatticeHamiltonian D L Site) (B : Finset (BoxD D L)) (R : ℕ) (Z : Finset (BoxD D L)) :
    H.h Z - (H.locShort B R).h Z = if Z ⊆ B ∧ regionDiam Z ≤ R then 0 else H.h Z := by
  dsimp [LatticeHamiltonian.locShort]
  split_ifs
  · exact sub_self (H.h Z)
  · exact sub_zero (H.h Z)

lemma locShort_s1_le {D L : ℕ} [NeZero D] [NeZero L]
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    (H : LatticeHamiltonian D L Site) (B : Finset (BoxD D L)) (R : ℕ) (η : ℝ) :
    (H.locShort B R).s1 η ≤ H.s1 η := by
  unfold LatticeHamiltonian.s1; rw [Finset.sup'_le_iff]; intro x hx
  refine le_trans (Finset.sum_le_sum (fun Z _ => ?_))
    (Finset.le_sup' (f := fun z => ∑ Z ∈ Finset.univ.filter (fun Z => z ∈ Z),
      ‖H.h Z‖ * (Z.card : ℝ) * (1 + (regionDiam Z : ℝ)) ^ η) hx)
  have hnorm : ‖(H.locShort B R).h Z‖ ≤ ‖H.h Z‖ := by
    dsimp [LatticeHamiltonian.locShort]; split_ifs
    · exact le_rfl
    · rw [norm_zero]; exact norm_nonneg _
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right hnorm (Nat.cast_nonneg _))
    (le_of_lt (Real.rpow_pos_of_pos (by positivity) η))

lemma LatticeHamiltonian.s1_nonneg {D L : ℕ} [NeZero D] [NeZero L]
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    (H : LatticeHamiltonian D L Site) (η : ℝ) : 0 ≤ H.s1 η := by
  unfold LatticeHamiltonian.s1
  have x0 : BoxD D L := fun _ => ⟨0, NeZero.pos L⟩
  have h0 : 0 ≤ ∑ Z ∈ Finset.univ.filter (fun Z : Finset (BoxD D L) => x0 ∈ Z),
      ‖H.h Z‖ * (Z.card : ℝ) * (1 + (regionDiam Z : ℝ)) ^ η :=
    Finset.sum_nonneg (fun Z _ => by positivity)
  exact le_trans h0 (Finset.le_sup' (f := fun x => ∑ Z ∈ Finset.univ.filter (fun Z => x ∈ Z),
    ‖H.h Z‖ * (Z.card : ℝ) * (1 + (regionDiam Z : ℝ)) ^ η) (Finset.mem_univ x0))

lemma LatticeHamiltonian.sum_filter_mem_le_s1 {D L : ℕ} [NeZero D] [NeZero L]
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    (H : LatticeHamiltonian D L Site) (b : BoxD D L) (η : ℝ) :
    (∑ Z ∈ Finset.univ.filter (fun Z : Finset (BoxD D L) => b ∈ Z),
      ‖H.h Z‖ * (Z.card : ℝ) * (1 + (regionDiam Z : ℝ)) ^ η) ≤ H.s1 η := by
  unfold LatticeHamiltonian.s1
  exact Finset.le_sup' (f := fun z => ∑ Z ∈ Finset.univ.filter (fun Z => z ∈ Z),
    ‖H.h Z‖ * (Z.card : ℝ) * (1 + (regionDiam Z : ℝ)) ^ η) (Finset.mem_univ b)

/-- Collar distance lower bound for any short-range term $Z$ (`regionDiam Z ≤ R`) not contained in $B$. -/
lemma regionDist_sub_le_of_not_subset {D L : ℕ}
    {X B Z : Finset (BoxD D L)} (hX : X.Nonempty)
    {d R : ℕ} (h_collar : ∀ x ∈ X, ∀ y : BoxD D L, y ∉ B → d ≤ boxDist x y)
    (hZ_not : ¬(Z ⊆ B)) (hZ_diam : regionDiam Z ≤ R) :
    Z.Nonempty ∧ d - R ≤ regionDist X Z := by
  rcases Finset.not_subset.mp hZ_not with ⟨y, hyZ, hyB⟩
  have hZ_ne : Z.Nonempty := ⟨y, hyZ⟩
  refine ⟨hZ_ne, ?_⟩
  suffices h_le : ∀ k, k ≤ d - R → k ≤ regionDist X Z from h_le _ le_rfl
  intro k hk; dsimp [regionDist]
  rw [dif_pos ⟨hX, hZ_ne⟩, Finset.le_inf'_iff]; intro p hp
  rcases Finset.mem_product.mp hp with ⟨hx, hz⟩
  have h1 : d ≤ boxDist p.1 y := h_collar p.1 hx y hyB
  have h2 : boxDist p.1 y ≤ boxDist p.1 p.2 + boxDist p.2 y := boxDist_triangle p.1 p.2 y
  have h3 : boxDist p.2 y ≤ R := le_trans (boxDist_le_regionDiam hz hyZ) hZ_diam
  omega

attribute [local irreducible] LatticeHamiltonian.locShort LatticeHamiltonian.s1

lemma opCommutator_H_tot_sub_eq_sum_filter {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    (H H_loc : LatticeHamiltonian D L Site) {B : Finset (BoxD D L)}
    {A_u : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site}
    (hA_supp : IsSupportedOn Site B A_u) :
    opCommutator (H.totalHamiltonian - H_loc.totalHamiltonian) A_u =
      ∑ Z ∈ Finset.univ.filter (fun Z : Finset (BoxD D L) => (Z ∩ B).Nonempty),
        opCommutator (H.h Z - H_loc.h Z) A_u := by
  unfold LatticeHamiltonian.totalHamiltonian
  rw [← Finset.sum_sub_distrib,
    ← Finset.sum_filter_add_sum_filter_not Finset.univ
      (fun Z : Finset (BoxD D L) => (Z ∩ B).Nonempty)]
  unfold opCommutator; rw [add_mul, mul_add, add_sub_add_comm]
  have h_zero : (∑ Z ∈ Finset.univ.filter (fun Z : Finset (BoxD D L) => ¬(Z ∩ B).Nonempty),
        (H.h Z - H_loc.h Z)) * A_u -
      A_u * (∑ Z ∈ Finset.univ.filter (fun Z : Finset (BoxD D L) => ¬(Z ∩ B).Nonempty),
        (H.h Z - H_loc.h Z)) = 0 := by
    rw [Finset.sum_mul, Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_eq_zero (fun Z hZ => ?_); rw [Finset.mem_filter] at hZ
    have hdisj : Disjoint Z B :=
      Finset.disjoint_iff_inter_eq_empty.mpr (Finset.not_nonempty_iff_eq_empty.mp hZ.2)
    exact opCommutator_eq_zero_of_disjoint hdisj
      (isSupportedOn_sub Z (H.is_supported Z) (H_loc.is_supported Z)) hA_supp
  rw [h_zero, add_zero, Finset.sum_mul, Finset.mul_sum, ← Finset.sum_sub_distrib]

/-- Pointwise commutator bound on $[H.H_{\mathrm{tot}} - (H.\mathrm{locShort}\ B\ R).H_{\mathrm{tot}}, \tau_u^{H_{\mathrm{loc}}}(O_X)]$
    combining finite-range exponential decay for boundary terms (`regionDiam Z ≤ R`) and Markov
    $s_1(m)$ decay for long-range terms (`regionDiam Z > R`). -/
lemma norm_opCommutator_sub_locShort_heisenbergEvolve_le {D L : ℕ} [NeZero D] [NeZero L]
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)] [∀ x, Nonempty (Site x)]
    (H : LatticeHamiltonian D L Site) {X B : Finset (BoxD D L)} (hX : X.Nonempty) (hXB : X ⊆ B)
    {O_X : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site} (hO : IsSupportedOn Site X O_X)
    {d R : ℕ} (hR1 : 1 ≤ R) (hRd : R ≤ d)
    (h_collar : ∀ x ∈ X, ∀ y : BoxD D L, y ∉ B → d ≤ boxDist x y)
    (m : ℕ) {T u : ℝ} (hu : u ∈ Set.Icc (-T) T) :
    ‖opCommutator (H.totalHamiltonian - (H.locShort B R).totalHamiltonian)
      (heisenbergFlow (H.locShort B R).totalHamiltonian u O_X)‖ ≤
      2 * ‖O_X‖ * (B.card : ℝ) *
        ((X.card : ℝ) * Real.exp 1 * H.s1 0 * Real.exp (- (d : ℝ) / (R : ℝ)) *
          Real.exp (2 * Real.exp 1 * H.s1 0 * T) + H.s1 (m : ℝ) / (1 + (R : ℝ)) ^ m) := by
  have hA_supp : IsSupportedOn Site B (heisenbergFlow (H.locShort B R).totalHamiltonian u O_X) :=
    isSupportedOn_heisenbergFlow (isSupportedOn_locShort_H_tot H B R) (isSupportedOn_mono hXB hO) u
  have h_abs_u : |u| ≤ T := abs_le.mpr hu
  have hs1_0_nn : 0 ≤ H.s1 0 := H.s1_nonneg 0
  have hs1_loc_le : (H.locShort B R).s1 0 ≤ H.s1 0 := locShort_s1_le H B R 0
  have hR_pos : (0 : ℝ) < (R : ℝ) := Nat.cast_pos.mpr (Nat.succ_le_iff.mp hR1)
  have h1R_pos : (0 : ℝ) < (1 + (R : ℝ)) ^ m := by positivity
  set S_B := Finset.univ.filter (fun Z : Finset (BoxD D L) => (Z ∩ B).Nonempty)
  set g1 : Finset (BoxD D L) → ℝ := fun Z => ‖H.h Z‖ * (Z.card : ℝ) * (1 + (regionDiam Z : ℝ)) ^ (0 : ℝ)
  set gm : Finset (BoxD D L) → ℝ := fun Z => ‖H.h Z‖ * (Z.card : ℝ) * (1 + (regionDiam Z : ℝ)) ^ (m : ℝ)
  set C_short : ℝ := 2 * ‖O_X‖ * (X.card : ℝ) * Real.exp 1 * Real.exp (- (d : ℝ) / (R : ℝ)) *
    Real.exp (2 * Real.exp 1 * H.s1 0 * T)
  set C_long : ℝ := 2 * ‖O_X‖ / (1 + (R : ℝ)) ^ m
  have hC_short_nn : 0 ≤ C_short := by dsimp [C_short]; positivity
  have hC_long_nn : 0 ≤ C_long := by dsimp [C_long]; positivity
  have hg1_nn : ∀ Z, 0 ≤ g1 Z := fun Z => by dsimp [g1]; positivity
  have hgm_nn : ∀ Z, 0 ≤ gm Z := fun Z => by dsimp [gm]; positivity
  have h_term : ∀ Z ∈ S_B,
      ‖opCommutator (H.h Z - (H.locShort B R).h Z) (heisenbergFlow (H.locShort B R).totalHamiltonian u O_X)‖ ≤
        C_short * g1 Z + C_long * gm Z := by
    intro Z hZ; rw [Finset.mem_filter] at hZ
    have hZ_card_ge : (1 : ℝ) ≤ (Z.card : ℝ) :=
      Nat.one_le_cast.mpr (Finset.card_pos.mpr (hZ.2.mono Finset.inter_subset_left))
    have hg1Z := hg1_nn Z
    have hgmZ := hgm_nn Z
    by_cases hdiam : regionDiam Z ≤ R
    · by_cases hsub : Z ⊆ B
      · rw [sub_locShort_h_eq, if_pos ⟨hsub, hdiam⟩, opCommutator, zero_mul, mul_zero, sub_self, norm_zero]
        exact add_nonneg (mul_nonneg hC_short_nn hg1Z) (mul_nonneg hC_long_nn hgmZ)
      · rw [sub_locShort_h_eq, if_neg (fun h => hsub h.1)]
        rcases regionDist_sub_le_of_not_subset hX h_collar hsub hdiam with ⟨hZ_ne, hdist_ge⟩
        have h_lr : ‖opCommutator (heisenbergFlow (H.locShort B R).totalHamiltonian u O_X) (H.h Z)‖ ≤
            2 * ‖O_X‖ * ‖H.h Z‖ * (X.card : ℝ) * Real.exp (- (regionDist X Z : ℝ) / (R : ℝ)) *
              Real.exp (2 * Real.exp 1 * (H.locShort B R).s1 0 * |u|) :=
          norm_opCommutator_heisenbergEvolve_shortRange_le (H.locShort B R) hR1
            (fun W hW => locShort_h_eq_zero_of_lt_regionDiam H B hW) hX hZ_ne hO (H.is_supported Z) u
        have h_comm_symm : ‖opCommutator (H.h Z) (heisenbergFlow (H.locShort B R).totalHamiltonian u O_X)‖ =
            ‖opCommutator (heisenbergFlow (H.locShort B R).totalHamiltonian u O_X) (H.h Z)‖ := by
          unfold opCommutator; rw [norm_sub_rev]
        have h_exp_dist : Real.exp (- (regionDist X Z : ℝ) / (R : ℝ)) ≤
            Real.exp 1 * Real.exp (- (d : ℝ) / (R : ℝ)) := by
          rw [← Real.exp_add]; apply Real.exp_le_exp.mpr
          have h1 : ((d - R : ℕ) : ℝ) ≤ (regionDist X Z : ℝ) := Nat.cast_le.mpr hdist_ge
          have h2 : (d : ℝ) - (R : ℝ) ≤ (regionDist X Z : ℝ) := by rw [← Nat.cast_sub hRd]; exact h1
          have h3 := div_le_div_of_nonneg_right h2 hR_pos.le
          rw [sub_div, div_self hR_pos.ne'] at h3; simp only [neg_div]; linarith
        have h_exp_time : Real.exp (2 * Real.exp 1 * (H.locShort B R).s1 0 * |u|) ≤
            Real.exp (2 * Real.exp 1 * H.s1 0 * T) := by
          apply Real.exp_le_exp.mpr
          have h1 : 2 * Real.exp 1 * (H.locShort B R).s1 0 ≤ 2 * Real.exp 1 * H.s1 0 :=
            mul_le_mul_of_nonneg_left hs1_loc_le (by positivity)
          exact mul_le_mul h1 h_abs_u (abs_nonneg u) (mul_nonneg (by positivity) hs1_0_nn)
        have h_g1_ge : ‖H.h Z‖ ≤ g1 Z := by
          dsimp [g1]; rw [Real.rpow_zero, mul_one]
          exact le_mul_of_one_le_right (norm_nonneg (H.h Z)) hZ_card_ge
        have h_short_le : ‖opCommutator (H.h Z) (heisenbergFlow (H.locShort B R).totalHamiltonian u O_X)‖ ≤
            C_short * g1 Z := by
          rw [h_comm_symm]
          have h_p1 : 2 * ‖O_X‖ * ‖H.h Z‖ * (X.card : ℝ) ≤ 2 * ‖O_X‖ * g1 Z * (X.card : ℝ) :=
            mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_left h_g1_ge (by positivity)) (Nat.cast_nonneg _)
          have h_p2 : 2 * ‖O_X‖ * ‖H.h Z‖ * (X.card : ℝ) *
              Real.exp (- (regionDist X Z : ℝ) / (R : ℝ)) ≤
              2 * ‖O_X‖ * g1 Z * (X.card : ℝ) *
              (Real.exp 1 * Real.exp (- (d : ℝ) / (R : ℝ))) :=
            mul_le_mul h_p1 h_exp_dist (by positivity)
              (mul_nonneg (mul_nonneg (by positivity) hg1Z) (Nat.cast_nonneg _))
          have h_p3 : 2 * ‖O_X‖ * ‖H.h Z‖ * (X.card : ℝ) *
              Real.exp (- (regionDist X Z : ℝ) / (R : ℝ)) *
              Real.exp (2 * Real.exp 1 * (H.locShort B R).s1 0 * |u|) ≤
              2 * ‖O_X‖ * g1 Z * (X.card : ℝ) *
              (Real.exp 1 * Real.exp (- (d : ℝ) / (R : ℝ))) *
              Real.exp (2 * Real.exp 1 * H.s1 0 * T) :=
            mul_le_mul h_p2 h_exp_time (by positivity)
              (mul_nonneg (mul_nonneg (mul_nonneg (by positivity) hg1Z) (Nat.cast_nonneg _))
                (by positivity))
          have h_eq_rhs : 2 * ‖O_X‖ * g1 Z * (X.card : ℝ) *
              (Real.exp 1 * Real.exp (- (d : ℝ) / (R : ℝ))) *
              Real.exp (2 * Real.exp 1 * H.s1 0 * T) = C_short * g1 Z := by
            dsimp [C_short]; ring
          exact le_trans h_lr (le_trans h_p3 (le_of_eq h_eq_rhs))
        linarith [mul_nonneg hC_long_nn hgmZ]
    · push_neg at hdiam
      rw [sub_locShort_h_eq, if_neg (fun h => not_le.mpr hdiam h.2)]
      have h_comm : ‖opCommutator (H.h Z) (heisenbergFlow (H.locShort B R).totalHamiltonian u O_X)‖ ≤
          2 * ‖O_X‖ * ‖H.h Z‖ := by
        calc ‖opCommutator (H.h Z) (heisenbergFlow (H.locShort B R).totalHamiltonian u O_X)‖
          _ ≤ 2 * ‖H.h Z‖ * ‖heisenbergFlow (H.locShort B R).totalHamiltonian u O_X‖ := norm_opCommutator_le _ _
          _ ≤ 2 * ‖H.h Z‖ * ‖O_X‖ :=
            mul_le_mul_of_nonneg_left
              (norm_heisenbergFlow_le (H.locShort B R).isSelfAdjoint_totalHamiltonian u O_X) (by positivity)
          _ = 2 * ‖O_X‖ * ‖H.h Z‖ := by ring
      have h_pow : (1 + (R : ℝ)) ^ m ≤ (1 + (regionDiam Z : ℝ)) ^ (m : ℝ) := by
        rw [Real.rpow_natCast]; refine pow_le_pow_left₀ (by positivity) ?_ m
        have : (R : ℝ) ≤ (regionDiam Z : ℝ) := Nat.cast_le.mpr hdiam.le
        linarith
      have h_gm_ge : (1 + (R : ℝ)) ^ m * ‖H.h Z‖ ≤ gm Z := by
        dsimp [gm]
        calc (1 + (R : ℝ)) ^ m * ‖H.h Z‖
          _ ≤ (1 + (regionDiam Z : ℝ)) ^ (m : ℝ) * (‖H.h Z‖ * (Z.card : ℝ)) :=
            mul_le_mul h_pow (le_mul_of_one_le_right (norm_nonneg (H.h Z)) hZ_card_ge)
              (norm_nonneg _) (by positivity)
          _ = ‖H.h Z‖ * (Z.card : ℝ) * (1 + (regionDiam Z : ℝ)) ^ (m : ℝ) := by ring
      have h_long_le : ‖opCommutator (H.h Z) (heisenbergFlow (H.locShort B R).totalHamiltonian u O_X)‖ ≤
          C_long * gm Z := by
        dsimp [C_long]; rw [div_mul_eq_mul_div, le_div_iff₀ h1R_pos]
        calc ‖opCommutator (H.h Z) (heisenbergFlow (H.locShort B R).totalHamiltonian u O_X)‖ * (1 + (R : ℝ)) ^ m
          _ ≤ (2 * ‖O_X‖ * ‖H.h Z‖) * (1 + (R : ℝ)) ^ m := mul_le_mul_of_nonneg_right h_comm h1R_pos.le
          _ = 2 * ‖O_X‖ * ((1 + (R : ℝ)) ^ m * ‖H.h Z‖) := by ring
          _ ≤ 2 * ‖O_X‖ * gm Z := mul_le_mul_of_nonneg_left h_gm_ge (by positivity)
      linarith [mul_nonneg hC_short_nn hg1Z]
  have h_inter := sum_filter_inter_nonempty_le B
    (fun Z => C_short * g1 Z + C_long * gm Z)
    (fun Z => add_nonneg (mul_nonneg hC_short_nn (hg1_nn Z)) (mul_nonneg hC_long_nn (hgm_nn Z)))
  have h_site_bound : ∀ b ∈ B,
      (∑ Z ∈ Finset.univ.filter (fun Z : Finset (BoxD D L) => b ∈ Z),
        (C_short * g1 Z + C_long * gm Z)) ≤ C_short * H.s1 0 + C_long * H.s1 (m : ℝ) := by
    intro b _; rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
    exact add_le_add
      (mul_le_mul_of_nonneg_left (H.sum_filter_mem_le_s1 b 0) hC_short_nn)
      (mul_le_mul_of_nonneg_left (H.sum_filter_mem_le_s1 b (m : ℝ)) hC_long_nn)
  have h_norm_sum :
      ‖opCommutator (H.totalHamiltonian - (H.locShort B R).totalHamiltonian)
        (heisenbergFlow (H.locShort B R).totalHamiltonian u O_X)‖ =
      ‖∑ Z ∈ S_B, opCommutator (H.h Z - (H.locShort B R).h Z)
        (heisenbergFlow (H.locShort B R).totalHamiltonian u O_X)‖ :=
    congrArg norm (opCommutator_H_tot_sub_eq_sum_filter H (H.locShort B R) hA_supp)
  have h_algebra : (B.card : ℝ) * (C_short * H.s1 0 + C_long * H.s1 (m : ℝ)) =
      2 * ‖O_X‖ * (B.card : ℝ) *
        ((X.card : ℝ) * Real.exp 1 * H.s1 0 * Real.exp (- (d : ℝ) / (R : ℝ)) *
          Real.exp (2 * Real.exp 1 * H.s1 0 * T) + H.s1 (m : ℝ) / (1 + (R : ℝ)) ^ m) := by
    dsimp [C_short, C_long]; ring
  calc ‖opCommutator (H.totalHamiltonian - (H.locShort B R).totalHamiltonian)
          (heisenbergFlow (H.locShort B R).totalHamiltonian u O_X)‖
    _ = ‖∑ Z ∈ S_B, opCommutator (H.h Z - (H.locShort B R).h Z)
          (heisenbergFlow (H.locShort B R).totalHamiltonian u O_X)‖ := h_norm_sum
    _ ≤ ∑ Z ∈ S_B, ‖opCommutator (H.h Z - (H.locShort B R).h Z)
          (heisenbergFlow (H.locShort B R).totalHamiltonian u O_X)‖ := norm_sum_le _ _
    _ ≤ ∑ Z ∈ S_B, (C_short * g1 Z + C_long * gm Z) := Finset.sum_le_sum h_term
    _ ≤ ∑ b ∈ B, ∑ Z ∈ Finset.univ.filter (fun Z : Finset (BoxD D L) => b ∈ Z),
          (C_short * g1 Z + C_long * gm Z) := h_inter
    _ ≤ ∑ _b ∈ B, (C_short * H.s1 0 + C_long * H.s1 (m : ℝ)) := Finset.sum_le_sum h_site_bound
    _ = (B.card : ℝ) * (C_short * H.s1 0 + C_long * H.s1 (m : ℝ)) := by rw [Finset.sum_const, nsmul_eq_mul]
    _ = 2 * ‖O_X‖ * (B.card : ℝ) *
        ((X.card : ℝ) * Real.exp 1 * H.s1 0 * Real.exp (- (d : ℝ) / (R : ℝ)) *
          Real.exp (2 * Real.exp 1 * H.s1 0 * T) + H.s1 (m : ℝ) / (1 + (R : ℝ)) ^ m) := h_algebra

/-- **Master Pointwise Conditional Expectation Light-Cone Bound (`norm_heisenbergEvolve_sub_condExp_le_of_collar`)**:
    For any lattice Hamiltonian $H$, any operator $O_X$ supported on $X \subseteq B$ separated from
    $B^c$ by collar distance $d \ge R \ge 1$, any moment order $m \in \mathbb{N}$, and any $t \in [-T, T]$ ($T \ge 0$),
    $$\|\tau_t^H(O_X) - \mathbb{E}_B(\tau_t^H(O_X))\| \le
      4 \|O_X\| |B| T \left( |X| e H.s_1(0) e^{-d / R} \exp(2 e H.s_1(0) T) + \frac{H.s_1(m)}{(1 + R)^m} \right).$$ -/
theorem norm_heisenbergEvolve_sub_condExp_le_of_collar {D L : ℕ} [NeZero D] [NeZero L]
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)] [∀ x, Nonempty (Site x)]
    (H : LatticeHamiltonian D L Site) {X B : Finset (BoxD D L)} (hX : X.Nonempty) (hXB : X ⊆ B)
    {O_X : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site} (hO : IsSupportedOn Site X O_X)
    {d R : ℕ} (hR1 : 1 ≤ R) (hRd : R ≤ d)
    (h_collar : ∀ x ∈ X, ∀ y : BoxD D L, y ∉ B → d ≤ boxDist x y)
    (m : ℕ) {T t : ℝ} (hT : 0 ≤ T) (ht : t ∈ Set.Icc (-T) T) :
    ‖H.heisenbergEvolve t O_X - condExp Site B (H.heisenbergEvolve t O_X)‖ ≤
      4 * ‖O_X‖ * (B.card : ℝ) * T *
        ((X.card : ℝ) * Real.exp 1 * H.s1 0 * Real.exp (- (d : ℝ) / (R : ℝ)) *
          Real.exp (2 * Real.exp 1 * H.s1 0 * T) + H.s1 (m : ℝ) / (1 + (R : ℝ)) ^ m) := by
  have h_supp_loc : IsSupportedOn Site B (heisenbergFlow (H.locShort B R).totalHamiltonian t O_X) :=
    isSupportedOn_heisenbergFlow (isSupportedOn_locShort_H_tot H B R) (isSupportedOn_mono hXB hO) t
  have h1 := norm_sub_condExp_le_two_mul_norm_sub_of_isSupportedOn (H.heisenbergEvolve t O_X) h_supp_loc
  have h2 := norm_heisenbergFlow_sub_heisenbergFlow_le H.isSelfAdjoint_totalHamiltonian O_X hT
    (fun u hu => norm_opCommutator_sub_locShort_heisenbergEvolve_le
      H hX hXB hO hR1 hRd h_collar m hu) ht
  calc ‖H.heisenbergEvolve t O_X - condExp Site B (H.heisenbergEvolve t O_X)‖
    _ ≤ 2 * ‖H.heisenbergEvolve t O_X - heisenbergFlow (H.locShort B R).totalHamiltonian t O_X‖ := h1
    _ ≤ 2 * (2 * ‖O_X‖ * (B.card : ℝ) *
          ((X.card : ℝ) * Real.exp 1 * H.s1 0 * Real.exp (- (d : ℝ) / (R : ℝ)) *
            Real.exp (2 * Real.exp 1 * H.s1 0 * T) + H.s1 (m : ℝ) / (1 + (R : ℝ)) ^ m) * T) :=
      mul_le_mul_of_nonneg_left h2 zero_le_two
    _ = 4 * ‖O_X‖ * (B.card : ℝ) * T *
        ((X.card : ℝ) * Real.exp 1 * H.s1 0 * Real.exp (- (d : ℝ) / (R : ℝ)) *
          Real.exp (2 * Real.exp 1 * H.s1 0 * T) + H.s1 (m : ℝ) / (1 + (R : ℝ)) ^ m) := by ring

end
