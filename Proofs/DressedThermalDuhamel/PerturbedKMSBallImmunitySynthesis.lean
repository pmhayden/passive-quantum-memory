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

import Proofs.DressedThermalDuhamel.PerturbedKMSLindbladODEBounds

/-!
# Perturbed KMS Lindblad Lifetime Synthesis from Dressed Ball Immunity

Synthesizes perturbed KMS Lindblad trajectory lifetime bounds (`indexed_perturbed_kms_lifetime_of_ball_immunity` and `boxCubes_one_immunity_of_single_site`) by combining dressed safe-subspace logical immunity, quasi-local unitary dressing tails, and perturbed Gibbs failure probability bounds.

## References

* Part II, Section 6.3 (`subsec:main-theorems`), Theorem 6.5 (`thm:main-D`)
* Part II, Section 6 (`sec:lindblad`), Lemma 6.1 (`lem:kms-fourth-root`)
* Part II, Section 6.2 (`subsec:kms-gronwall`), Theorem 6.2 (`thm:kms-gronwall-bare`)
-/

noncomputable section

open scoped Classical InnerProduct ComplexConjugate BigOperators
open Filter Topology Asymptotics ContinuousLinearMap KMSPinchedGibbs

set_option maxRecDepth 200000

/-! ## 1. Unconditional `IndexedCommutingProjectorHamiltonian` KMS Memory Lifetime Synthesis -/

/-- **Unconditional Perturbed KMS Memory Lifetime & Drift Synthesis for
`IndexedCommutingProjectorHamiltonian` + `QuasiLocalPerturbation`
(`indexed_perturbed_kms_memory_lifetime_and_drift_bound`)**:
Provides an unconditional, `h_pin_all`-free synthesis of the KMS coherent commutator bound and
the KMS-Lindblad trajectory drift-plus-Dirichlet bound for any `IndexedCommutingProjectorHamiltonian`
and `QuasiLocalPerturbation`. -/
theorem indexed_perturbed_kms_memory_lifetime_and_drift_bound
    {D L : ℕ} {Site : BoxD D L → Type}
    [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)] [∀ x, Nonempty (Site x)]
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (sys : IndexedCommutingProjectorHamiltonian D L Site ι)
    (V : QuasiLocalPerturbation D L Site)
    (hH_pert : IsSelfAdjoint (sys.H0 + V.totalPerturbation))
    (β : ℝ)
    (bath : Finset (BathChannel D L Site))
    (O_dec Pi_safe : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site)
    (hO_sa : IsSelfAdjoint O_dec) (hO_norm : ‖O_dec‖ ≤ 1)
    (h_comm_H0 : Commute sys.H0 O_dec)
    (hPi : IsStarProjection Pi_safe)
    (h_bath : ∀ ch ∈ bath, 0 ≤ ch.γ ∧
      Pi_safe * (ch.L * O_dec - O_dec * ch.L) * Pi_safe = 0)
    {p_fail : ℝ}
    (hp_le : gibbsFailureProb (sys.H0 + V.totalPerturbation) hH_pert β (1 - Pi_safe) ≤ p_fail) :
    opKMSNorm (sys.H0 + V.totalPerturbation) hH_pert β (V.totalPerturbation * O_dec - O_dec * V.totalPerturbation) ≤
      ‖Pi_safe * (V.totalPerturbation * O_dec - O_dec * V.totalPerturbation) * Pi_safe‖ +
        2 * ‖V.totalPerturbation * O_dec - O_dec * V.totalPerturbation‖ * (p_fail ^ (1 / 4 : ℝ)) ∧
    (∀ (O_t : ℝ → (ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site)) (t : ℝ),
      0 ≤ t →
      SatisfiesKMSLindbladODE (sys.H0 + V.totalPerturbation) hH_pert β bath O_dec O_t t →
      opKMSNorm (sys.H0 + V.totalPerturbation) hH_pert β (O_t t - O_dec) ≤
        kmsDriftDirichletBound
          (‖Pi_safe * (V.totalPerturbation * O_dec - O_dec * V.totalPerturbation) * Pi_safe‖ +
            2 * ‖V.totalPerturbation * O_dec - O_dec * V.totalPerturbation‖ * (p_fail ^ (1 / 4 : ℝ)))
          (16 * (∑ ch ∈ bath, ch.γ * ‖ch.L‖ ^ 2) * (p_fail ^ (1 / 2 : ℝ)))
          t) :=
  ⟨opKMSNorm_le_two_mul_norm_add_sandwich_norm (sys.H0 + V.totalPerturbation) hH_pert β hPi hp_le,
   fun O_t t ht h_ode =>
     opKMSNorm_le_kmsDriftDirichletBound_of_satisfiesKMSLindbladODE_unconditional
       hH_pert β bath O_dec Pi_safe hO_sa hO_norm h_comm_H0 hPi h_bath hp_le O_t t ht h_ode⟩

/-! ## 2. Radius-$r_{\mathrm{fw}}$ Ball Safe-Subspace Immunity & Superpolynomial Tail Bounds -/

/-- Every open-box cube of linear side length $1$ anchored at $v \in \mathrm{BoxD}\ D\ L$ is the
singleton $\{v\}$. -/
lemma boxCube_one_eq_singleton {D L : ℕ} (v : BoxD D L) :
    boxCube v 1 = {v} := by
  ext x
  simp only [boxCube, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
  constructor
  · intro h
    funext i
    have hi := h i
    exact Fin.ext (by omega)
  · rintro rfl i
    omega

/-- For $r_{\mathrm{fw}} = 1$, the cube-family safe-subspace immunity
`∀ r ∈ Finset.Icc 1 1, ∀ A ∈ BoxCubes D L r, Pi_safe * (V.term r A * O_dec - O_dec * V.term r A) * Pi_safe = 0`
follows automatically from the universal single-site safe-subspace immunity
`∀ (v : BoxD D L) A_v, IsSupportedOn Site {v} A_v → Pi_safe * (A_v * O_dec - O_dec * A_v) * Pi_safe = 0`. -/
lemma boxCubes_one_immunity_of_single_site {D L : ℕ} [NeZero L]
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    (V : QuasiLocalPerturbation D L Site)
    (O_dec Pi_safe : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site)
    (h_single : ∀ (v : BoxD D L)
      (A_v : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site),
      IsSupportedOn Site {v} A_v →
        Pi_safe * (A_v * O_dec - O_dec * A_v) * Pi_safe = 0) :
    ∀ r ∈ Finset.Icc 1 1, ∀ A ∈ boxCubes D L r,
      Pi_safe * (V.term r A * O_dec - O_dec * V.term r A) * Pi_safe = 0 := by
  intro r hr A hA
  have hr1 : r = 1 := by
    rw [Finset.mem_Icc] at hr
    omega
  subst hr1
  have h1L : 1 ∈ Finset.Icc 1 L := by
    rw [Finset.mem_Icc]
    exact ⟨le_rfl, Nat.one_le_iff_ne_zero.mpr (NeZero.ne L)⟩
  have h_supp : IsSupportedOn Site A (V.term 1 A) := V.is_supported 1 h1L A hA
  rw [boxCubes, Finset.mem_image] at hA
  rcases hA with ⟨v, _, hAv⟩
  have hA_eq : A = {v} := by rw [← hAv, boxCube_one_eq_singleton v]
  subst hA_eq
  exact h_single v (V.term 1 {v}) h_supp

lemma sandwich_commutator_sum {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {α : Type*} (s : Finset α) (f : α → (E →L[ℂ] E)) (O_dec Pi_safe : E →L[ℂ] E) :
    Pi_safe * ((∑ a ∈ s, f a) * O_dec - O_dec * (∑ a ∈ s, f a)) * Pi_safe =
      ∑ a ∈ s, Pi_safe * (f a * O_dec - O_dec * f a) * Pi_safe := by
  rw [Finset.sum_mul, Finset.mul_sum, ← Finset.sum_sub_distrib, Finset.mul_sum, Finset.sum_mul]

lemma pi_safe_commutator_V_tot_eq_sum {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    (V : QuasiLocalPerturbation D L Site)
    (O_dec Pi_safe : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site) :
    Pi_safe * (V.totalPerturbation * O_dec - O_dec * V.totalPerturbation) * Pi_safe =
      ∑ r ∈ Finset.Icc 1 L, ∑ A ∈ boxCubes D L r,
        Pi_safe * (V.term r A * O_dec - O_dec * V.term r A) * Pi_safe := by
  unfold QuasiLocalPerturbation.totalPerturbation
  rw [sandwich_commutator_sum]
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [sandwich_commutator_sum]

lemma commutator_V_tot_eq_sum {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    (V : QuasiLocalPerturbation D L Site)
    (O_dec : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site) :
    V.totalPerturbation * O_dec - O_dec * V.totalPerturbation =
      ∑ r ∈ Finset.Icc 1 L, ∑ A ∈ boxCubes D L r,
        (V.term r A * O_dec - O_dec * V.term r A) := by
  unfold QuasiLocalPerturbation.totalPerturbation
  rw [Finset.sum_mul, Finset.mul_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [Finset.sum_mul, Finset.mul_sum, ← Finset.sum_sub_distrib]

/-- Under the radius-$r_{\mathrm{fw}}$ safe-subspace operator immunity `h_fw`, all scale-$r$ contributions for
$1 \le r \le r_{\mathrm{fw}}$ in `Pi_safe * (V.V_tot * O_dec - O_dec * V.V_tot) * Pi_safe` vanish
identically, leaving only the tail scales $r \in [r_{\mathrm{fw}} + 1, L]$. -/
lemma pi_safe_commutator_V_tot_eq_tail_sum {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    (V : QuasiLocalPerturbation D L Site)
    (O_dec Pi_safe : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site)
    (r_fw : ℕ)
    (h_fw : ∀ r ∈ Finset.Icc 1 r_fw, ∀ A ∈ boxCubes D L r,
      Pi_safe * (V.term r A * O_dec - O_dec * V.term r A) * Pi_safe = 0) :
    Pi_safe * (V.totalPerturbation * O_dec - O_dec * V.totalPerturbation) * Pi_safe =
      ∑ r ∈ Finset.Icc (r_fw + 1) L, ∑ A ∈ boxCubes D L r,
        Pi_safe * (V.term r A * O_dec - O_dec * V.term r A) * Pi_safe := by
  rw [pi_safe_commutator_V_tot_eq_sum]
  refine (Finset.sum_subset (fun r hr => ?_) (fun r hr h_not => ?_)).symm
  · rw [Finset.mem_Icc] at hr ⊢
    exact ⟨by omega, hr.2⟩
  · rw [Finset.mem_Icc] at hr h_not
    have hr_fw : r ∈ Finset.Icc 1 r_fw := Finset.mem_Icc.mpr ⟨hr.1, by omega⟩
    exact Finset.sum_eq_zero fun A hA => h_fw r hr_fw A hA

/-- **Finite-Range Vanishing of the Safe-Subspace Commutator
(`pi_safe_commutator_V_tot_eq_zero_of_finite_range`)**:
If `Pi_safe` and `O_dec` satisfy safe-subspace operator immunity up to scale $r_{\mathrm{fw}}$ (`h_fw`) and
$V$ has interaction range $\le r_{\mathrm{fw}}$ (`∀ r > r_fw, ∀ A, V.term r A = 0`), then
`Pi_safe * (V.V_tot * O_dec - O_dec * V.V_tot) * Pi_safe = 0` identically, and the KMS norm of
`[V.V_tot, O_dec]` is bounded purely by the fourth-root Gibbs failure term
`2 * ‖V.V_tot * O_dec - O_dec * V.V_tot‖ * (p_fail ^ (1 / 4 : ℝ))`. -/
theorem pi_safe_commutator_V_tot_eq_zero_of_finite_range {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    [∀ x, Nonempty (Site x)]
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (sys : IndexedCommutingProjectorHamiltonian D L Site ι)
    (V : QuasiLocalPerturbation D L Site)
    (hH_pert : IsSelfAdjoint (sys.H0 + V.totalPerturbation))
    (β : ℝ)
    (O_dec Pi_safe : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site)
    (hPi : IsStarProjection Pi_safe)
    (r_fw : ℕ)
    (h_fw : ∀ r ∈ Finset.Icc 1 r_fw, ∀ A ∈ boxCubes D L r,
      Pi_safe * (V.term r A * O_dec - O_dec * V.term r A) * Pi_safe = 0)
    (h_range : ∀ r > r_fw, ∀ A : Finset (BoxD D L), V.term r A = 0)
    {p_fail : ℝ}
    (hp_le : gibbsFailureProb (sys.H0 + V.totalPerturbation) hH_pert β (1 - Pi_safe) ≤ p_fail) :
    Pi_safe * (V.totalPerturbation * O_dec - O_dec * V.totalPerturbation) * Pi_safe = 0 ∧
    opKMSNorm (sys.H0 + V.totalPerturbation) hH_pert β (V.totalPerturbation * O_dec - O_dec * V.totalPerturbation) ≤
      2 * ‖V.totalPerturbation * O_dec - O_dec * V.totalPerturbation‖ * (p_fail ^ (1 / 4 : ℝ)) := by
  have h_zero : Pi_safe * (V.totalPerturbation * O_dec - O_dec * V.totalPerturbation) * Pi_safe = 0 := by
    rw [pi_safe_commutator_V_tot_eq_tail_sum V O_dec Pi_safe r_fw h_fw]
    refine Finset.sum_eq_zero fun r hr => Finset.sum_eq_zero fun A _ => ?_
    rw [Finset.mem_Icc] at hr
    have hr_gt : r > r_fw := by omega
    simp [h_range r hr_gt A]
  exact ⟨h_zero,
    (opKMSNorm_le_two_mul_norm_of_sandwich_eq_zero
      (sys.H0 + V.totalPerturbation) hH_pert β hPi h_zero hp_le).1⟩

lemma card_boxCubes_le (D L r : ℕ) :
    ((boxCubes D L r).card : ℝ) ≤ (L : ℝ) ^ D := by
  have h_card : (boxCubes D L r).card ≤ L ^ D := by
    calc (boxCubes D L r).card
      _ ≤ (Finset.univ : Finset (BoxD D L)).card := Finset.card_image_le
      _ = Fintype.card (Fin D → Fin L) := Finset.card_univ
      _ = L ^ D := by simp [Fintype.card_fun, Fintype.card_fin]
  exact_mod_cast h_card

/-- For any `QuasiLocalPerturbation` satisfying `V.SatisfiesDecayBound J f` with $0 \le J$ and
$\forall r, 0 \le f(r)$, and any operator $O_{\mathrm{dec}}$ with $\|O_{\mathrm{dec}}\| \le 1$,
$$\|[V_{\mathrm{tot}}, O_{\mathrm{dec}}]\| \le 2 J L^D \sum_{r=1}^L f(r).$$ -/
lemma norm_commutator_V_tot_le {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    (V : QuasiLocalPerturbation D L Site)
    (O_dec : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site)
    (hO_norm : ‖O_dec‖ ≤ 1)
    {J : ℝ} {f : ℕ → ℝ} (hJ_nn : 0 ≤ J) (hf_nn : ∀ r : ℕ, 0 ≤ f r)
    (hV_decay : V.SatisfiesDecayBound J f) :
    ‖V.totalPerturbation * O_dec - O_dec * V.totalPerturbation‖ ≤
      2 * J * ((L : ℝ) ^ D) * ∑ r ∈ Finset.Icc 1 L, f r := by
  rw [commutator_V_tot_eq_sum]
  calc ‖∑ r ∈ Finset.Icc 1 L, ∑ A ∈ boxCubes D L r, (V.term r A * O_dec - O_dec * V.term r A)‖
    _ ≤ ∑ r ∈ Finset.Icc 1 L, ‖∑ A ∈ boxCubes D L r, (V.term r A * O_dec - O_dec * V.term r A)‖ :=
      norm_sum_le _ _
    _ ≤ ∑ r ∈ Finset.Icc 1 L, (2 * J * ((L : ℝ) ^ D) * f r) := by
      refine Finset.sum_le_sum fun r hr => ?_
      have h_inner : ‖∑ A ∈ boxCubes D L r, (V.term r A * O_dec - O_dec * V.term r A)‖ ≤
          ∑ A ∈ boxCubes D L r, (2 * (J * f r)) := by
        refine le_trans (norm_sum_le _ _) (Finset.sum_le_sum fun A hA => ?_)
        have h1 : ‖V.term r A * O_dec - O_dec * V.term r A‖ ≤ 2 * ‖V.term r A‖ :=
          norm_opCommutator_le_two_mul (V.term r A) hO_norm
        have h2 : ‖V.term r A‖ ≤ J * f r := hV_decay r hr A hA
        linarith
      rw [Finset.sum_const, nsmul_eq_mul] at h_inner
      have h_card : ((boxCubes D L r).card : ℝ) ≤ (L : ℝ) ^ D := card_boxCubes_le D L r
      have h_jf_nn : 0 ≤ 2 * (J * f r) := by have := hf_nn r; positivity
      have h_mul : ((boxCubes D L r).card : ℝ) * (2 * (J * f r)) ≤
          ((L : ℝ) ^ D) * (2 * (J * f r)) :=
        mul_le_mul_of_nonneg_right h_card h_jf_nn
      linarith
    _ = 2 * J * ((L : ℝ) ^ D) * ∑ r ∈ Finset.Icc 1 L, f r := by
      rw [← Finset.mul_sum]

/-- **Superpolynomial Tail Bound on Safe-Subspace Commutator (`norm_pi_safe_commutator_V_tot_le_tail`)**:
If `Pi_safe` and `O_dec` (`‖O_dec‖ ≤ 1`, `IsStarProjection Pi_safe`) satisfy safe-subspace operator immunity up
to scale $r_{\mathrm{fw}}$, and `V.SatisfiesDecayBound J f` ($0 \le J$, $\forall r, 0 \le f(r)$), then
$$\|\Pi_{\mathrm{safe}} [V_{\mathrm{tot}}, O_{\mathrm{dec}}] \Pi_{\mathrm{safe}}\|
  \le 2 J L^D \sum_{r = r_{\mathrm{fw}} + 1}^L f(r).$$ -/
theorem norm_pi_safe_commutator_V_tot_le_tail {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    (V : QuasiLocalPerturbation D L Site)
    (O_dec Pi_safe : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site)
    (hO_norm : ‖O_dec‖ ≤ 1)
    (hPi : IsStarProjection Pi_safe)
    (r_fw : ℕ)
    (h_fw : ∀ r ∈ Finset.Icc 1 r_fw, ∀ A ∈ boxCubes D L r,
      Pi_safe * (V.term r A * O_dec - O_dec * V.term r A) * Pi_safe = 0)
    {J : ℝ} {f : ℕ → ℝ} (hJ_nn : 0 ≤ J) (hf_nn : ∀ r : ℕ, 0 ≤ f r)
    (hV_decay : V.SatisfiesDecayBound J f) :
    ‖Pi_safe * (V.totalPerturbation * O_dec - O_dec * V.totalPerturbation) * Pi_safe‖ ≤
      2 * J * ((L : ℝ) ^ D) * ∑ r ∈ Finset.Icc (r_fw + 1) L, f r := by
  have hPi_norm : ‖Pi_safe‖ ≤ 1 := isStarProjection_norm_le_one hPi
  rw [pi_safe_commutator_V_tot_eq_tail_sum V O_dec Pi_safe r_fw h_fw]
  calc ‖∑ r ∈ Finset.Icc (r_fw + 1) L, ∑ A ∈ boxCubes D L r,
          Pi_safe * (V.term r A * O_dec - O_dec * V.term r A) * Pi_safe‖
    _ ≤ ∑ r ∈ Finset.Icc (r_fw + 1) L,
          ‖∑ A ∈ boxCubes D L r, Pi_safe * (V.term r A * O_dec - O_dec * V.term r A) * Pi_safe‖ :=
      norm_sum_le _ _
    _ ≤ ∑ r ∈ Finset.Icc (r_fw + 1) L, (2 * J * ((L : ℝ) ^ D) * f r) := by
      refine Finset.sum_le_sum fun r hr => ?_
      have hr1 : r ∈ Finset.Icc 1 L := by
        rw [Finset.mem_Icc] at hr ⊢
        exact ⟨by omega, hr.2⟩
      have h_inner :
          ‖∑ A ∈ boxCubes D L r, Pi_safe * (V.term r A * O_dec - O_dec * V.term r A) * Pi_safe‖ ≤
            ∑ A ∈ boxCubes D L r, (2 * (J * f r)) := by
        refine le_trans (norm_sum_le _ _) (Finset.sum_le_sum fun A hA => ?_)
        have h_sand :
            ‖Pi_safe * (V.term r A * O_dec - O_dec * V.term r A) * Pi_safe‖ ≤
              ‖V.term r A * O_dec - O_dec * V.term r A‖ :=
          le_trans (norm_mul_le_of_le_one_right hPi_norm) (norm_mul_le_of_le_one_left hPi_norm)
        have h1 : ‖V.term r A * O_dec - O_dec * V.term r A‖ ≤ 2 * ‖V.term r A‖ :=
          norm_opCommutator_le_two_mul (V.term r A) hO_norm
        have h2 : ‖V.term r A‖ ≤ J * f r := hV_decay r hr1 A hA
        linarith
      rw [Finset.sum_const, nsmul_eq_mul] at h_inner
      have h_card : ((boxCubes D L r).card : ℝ) ≤ (L : ℝ) ^ D := card_boxCubes_le D L r
      have h_jf_nn : 0 ≤ 2 * (J * f r) := by have := hf_nn r; positivity
      have h_mul : ((boxCubes D L r).card : ℝ) * (2 * (J * f r)) ≤
          ((L : ℝ) ^ D) * (2 * (J * f r)) :=
        mul_le_mul_of_nonneg_right h_card h_jf_nn
      linarith
    _ = 2 * J * ((L : ℝ) ^ D) * ∑ r ∈ Finset.Icc (r_fw + 1) L, f r := by
      rw [← Finset.mul_sum]

/-- **Radius-$r_{\mathrm{fw}}$ Ball Safe-Subspace Immunity KMS Memory Lifetime & Explicit Tail-Bounded Drift
(`indexed_perturbed_kms_lifetime_of_ball_immunity`)**:
Under the radius-$r_{\mathrm{fw}}$ safe-subspace operator immunity `h_fw` and quasi-local decay `V.SatisfiesDecayBound J f`,
every term in the KMS coherent drift and the KMS-Lindblad trajectory bound is explicitly bounded
in terms of $p_{\mathrm{fail}}^{1/4}$, $p_{\mathrm{fail}}^{1/2}$, and the superpolynomial tail sum
$\sum_{r = r_{\mathrm{fw}} + 1}^L f(r)$. -/
theorem indexed_perturbed_kms_lifetime_of_ball_immunity {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    [∀ x, Nonempty (Site x)]
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (sys : IndexedCommutingProjectorHamiltonian D L Site ι)
    (V : QuasiLocalPerturbation D L Site)
    (hH_pert : IsSelfAdjoint (sys.H0 + V.totalPerturbation))
    (β : ℝ)
    (bath : Finset (BathChannel D L Site))
    (O_dec Pi_safe : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site)
    (hO_sa : IsSelfAdjoint O_dec) (hO_norm : ‖O_dec‖ ≤ 1)
    (h_comm_H0 : Commute sys.H0 O_dec)
    (hPi : IsStarProjection Pi_safe)
    (r_fw : ℕ)
    (h_fw : ∀ r ∈ Finset.Icc 1 r_fw, ∀ A ∈ boxCubes D L r,
      Pi_safe * (V.term r A * O_dec - O_dec * V.term r A) * Pi_safe = 0)
    {J : ℝ} {f : ℕ → ℝ} (hJ_nn : 0 ≤ J) (hf_nn : ∀ r : ℕ, 0 ≤ f r)
    (hV_decay : V.SatisfiesDecayBound J f)
    (h_bath : ∀ ch ∈ bath, 0 ≤ ch.γ ∧
      Pi_safe * (ch.L * O_dec - O_dec * ch.L) * Pi_safe = 0)
    {p_fail : ℝ}
    (hp_le : gibbsFailureProb (sys.H0 + V.totalPerturbation) hH_pert β (1 - Pi_safe) ≤ p_fail) :
    let Γ_tail := 2 * J * ((L : ℝ) ^ D) * ∑ r ∈ Finset.Icc (r_fw + 1) L, f r
    let Γ_tot := 2 * J * ((L : ℝ) ^ D) * ∑ r ∈ Finset.Icc 1 L, f r
    ‖Pi_safe * (V.totalPerturbation * O_dec - O_dec * V.totalPerturbation) * Pi_safe‖ ≤ Γ_tail ∧
    ‖V.totalPerturbation * O_dec - O_dec * V.totalPerturbation‖ ≤ Γ_tot ∧
    opKMSNorm (sys.H0 + V.totalPerturbation) hH_pert β (V.totalPerturbation * O_dec - O_dec * V.totalPerturbation) ≤
      Γ_tail + 2 * Γ_tot * (p_fail ^ (1 / 4 : ℝ)) ∧
    (∀ (O_t : ℝ → (ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site)) (t : ℝ),
      0 ≤ t →
      SatisfiesKMSLindbladODE (sys.H0 + V.totalPerturbation) hH_pert β bath O_dec O_t t →
      opKMSNorm (sys.H0 + V.totalPerturbation) hH_pert β (O_t t - O_dec) ≤
        kmsDriftDirichletBound
          (Γ_tail + 2 * Γ_tot * (p_fail ^ (1 / 4 : ℝ)))
          (16 * (∑ ch ∈ bath, ch.γ * ‖ch.L‖ ^ 2) * (p_fail ^ (1 / 2 : ℝ)))
          t) := by
  intro Γ_tail Γ_tot
  have h_tail : ‖Pi_safe * (V.totalPerturbation * O_dec - O_dec * V.totalPerturbation) * Pi_safe‖ ≤ Γ_tail :=
    norm_pi_safe_commutator_V_tot_le_tail V O_dec Pi_safe hO_norm hPi r_fw h_fw hJ_nn hf_nn hV_decay
  have h_tot : ‖V.totalPerturbation * O_dec - O_dec * V.totalPerturbation‖ ≤ Γ_tot :=
    norm_commutator_V_tot_le V O_dec hO_norm hJ_nn hf_nn hV_decay
  have hp_nonneg : 0 ≤ p_fail :=
    le_trans (hilbertTrace_gibbsDensityOp_mul_proj_nonneg
      (opEigenbasis (sys.H0 + V.totalPerturbation) hH_pert) (opEigenvalues (sys.H0 + V.totalPerturbation) hH_pert) β
      (opEigenbasis_orthonormal (sys.H0 + V.totalPerturbation) hH_pert)
      (hilbertTrace_eq_sum_opEigenbasis (sys.H0 + V.totalPerturbation) hH_pert) hPi.one_sub) hp_le
  have h_rpow_nn : 0 ≤ p_fail ^ (1 / 4 : ℝ) := Real.rpow_nonneg hp_nonneg _
  have h_kms_raw := opKMSNorm_le_two_mul_norm_add_sandwich_norm
    (C := V.totalPerturbation * O_dec - O_dec * V.totalPerturbation) (sys.H0 + V.totalPerturbation) hH_pert β hPi hp_le
  have h_kms :
      opKMSNorm (sys.H0 + V.totalPerturbation) hH_pert β (V.totalPerturbation * O_dec - O_dec * V.totalPerturbation) ≤
        Γ_tail + 2 * Γ_tot * (p_fail ^ (1 / 4 : ℝ)) := by
    have h_mul : 2 * ‖V.totalPerturbation * O_dec - O_dec * V.totalPerturbation‖ * (p_fail ^ (1 / 4 : ℝ)) ≤
        2 * Γ_tot * (p_fail ^ (1 / 4 : ℝ)) := by
      nlinarith
    linarith
  have hΓ_tail_nn : 0 ≤ Γ_tail :=
    le_trans (norm_nonneg _) h_tail
  have hΓ_tot_nn : 0 ≤ Γ_tot :=
    le_trans (norm_nonneg _) h_tot
  refine ⟨h_tail, h_tot, h_kms, fun O_t t ht h_ode => ?_⟩
  have h_comm_H : opCommutator (sys.H0 + V.totalPerturbation) O_dec = V.totalPerturbation * O_dec - O_dec * V.totalPerturbation := by
    unfold opCommutator; rw [add_mul, mul_add, h_comm_H0.eq]; abel
  exact opKMSNorm_le_kmsDriftDirichletBound_of_commutator_bound
    (sys.H0 + V.totalPerturbation) hH_pert β bath O_dec Pi_safe (V.totalPerturbation * O_dec - O_dec * V.totalPerturbation)
    hO_sa hO_norm h_comm_H (by positivity) h_kms hPi h_bath hp_le O_t t ht h_ode

/-! ## 3. QAC-Dressed Observable & Dressed Safe Projector KMS Trajectory Bounds -/

lemma isSelfAdjoint_unitary_conj {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] [CompleteSpace E]
    (U : unitary (E →L[ℂ] E)) {O : E →L[ℂ] E} (hO : IsSelfAdjoint O) :
    IsSelfAdjoint (U.1 * O * U.1†) := by
  rw [IsSelfAdjoint]
  change star (U.1 * O * star U.1) = U.1 * O * star U.1
  rw [star_mul, star_mul, star_star, hO.star_eq, mul_assoc]

lemma sq_eq_one_unitary_conj {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] [CompleteSpace E]
    (U : unitary (E →L[ℂ] E)) {O : E →L[ℂ] E} (hO_sq : O * O = 1) :
    (U.1 * O * U.1†) * (U.1 * O * U.1†) = 1 := by
  have hU_star_self : U.1† * U.1 = 1 := Unitary.coe_star_mul_self U
  have hU_self_star : U.1 * U.1† = 1 := Unitary.coe_mul_star_self U
  calc (U.1 * O * U.1†) * (U.1 * O * U.1†)
    _ = U.1 * O * (U.1† * U.1) * O * U.1† := by simp only [mul_assoc]
    _ = U.1 * (O * O) * U.1† := by rw [hU_star_self, mul_one]; simp only [mul_assoc]
    _ = U.1 * U.1† := by rw [hO_sq, mul_one]
    _ = 1 := hU_self_star

lemma norm_unitary_conj_le {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] [CompleteSpace E]
    (U : unitary (E →L[ℂ] E)) (X : E →L[ℂ] E) :
    ‖U.1 * X * U.1†‖ ≤ ‖X‖ :=
  le_trans (norm_mul_le_of_le_one_right (unitary_star_norm_le_one U))
    (norm_mul_le_of_le_one_left (unitary_norm_le_one U))

/-- Unitary covariance of the safe-subspace commutator sandwich:
$$\Pi_{\mathrm{safe}}^{\mathrm{dress}} [H, O_{\mathrm{dec}}^{\mathrm{dress}}] \Pi_{\mathrm{safe}}^{\mathrm{dress}}
  = U \bigl(\Pi_{\mathrm{safe}} [U^\dagger H U, O_{\mathrm{dec}}] \Pi_{\mathrm{safe}}\bigr) U^\dagger.$$ -/
lemma dressed_sandwich_opCommutator_eq {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] [CompleteSpace E]
    (U : unitary (E →L[ℂ] E)) (H O_dec Pi_safe : E →L[ℂ] E) :
    let Pi_safe_dress := U.1 * Pi_safe * U.1†
    let O_dec_dress := U.1 * O_dec * U.1†
    Pi_safe_dress * opCommutator H O_dec_dress * Pi_safe_dress =
      U.1 * (Pi_safe * opCommutator (U.1† * H * U.1) O_dec * Pi_safe) * U.1† := by
  intro Pi_safe_dress O_dec_dress
  have hU_star_self : U.1† * U.1 = 1 := Unitary.coe_star_mul_self U
  dsimp [Pi_safe_dress, O_dec_dress, opCommutator]
  rw [mul_sub, sub_mul, mul_sub, sub_mul, mul_sub, sub_mul]
  congr 1
  · calc U.1 * Pi_safe * U.1† * (H * (U.1 * O_dec * U.1†)) * (U.1 * Pi_safe * U.1†)
      _ = U.1 * (Pi_safe * (U.1† * H * U.1 * O_dec) * (U.1† * U.1) * Pi_safe) * U.1† := by
        simp only [mul_assoc]
      _ = U.1 * (Pi_safe * (U.1† * H * U.1 * O_dec) * Pi_safe) * U.1† := by
        rw [hU_star_self, mul_one]
  · calc U.1 * Pi_safe * U.1† * (U.1 * O_dec * U.1† * H) * (U.1 * Pi_safe * U.1†)
      _ = U.1 * (Pi_safe * (U.1† * U.1) * (O_dec * (U.1† * H * U.1)) * Pi_safe) * U.1† := by
        simp only [mul_assoc]
      _ = U.1 * (Pi_safe * (O_dec * (U.1† * H * U.1)) * Pi_safe) * U.1† := by
        rw [hU_star_self, mul_one]

/-- **QAC-Dressed Perturbed KMS Memory Lifetime & Drift Synthesis
(`indexed_dressed_perturbed_kms_memory_lifetime_and_drift_bound`)**:
Given a QAC unitary $U$, defines $\Pi_{\mathrm{safe}}^{\mathrm{dress}} := U \Pi_{\mathrm{safe}} U^\dagger$
and $O_{\mathrm{dec}}^{\mathrm{dress}} := U O_{\mathrm{dec}} U^\dagger$, proves that they inherit
the star-projection, self-adjointness, involution, norm-$\le 1$, and dressed-$H_0$ commutation
properties, and establishes the KMS drift-plus-Dirichlet trajectory bound under the dressed Gibbs
failure probability bound `gibbsFailureProb (sys.H0 + V.V_tot) hH_pert β (1 - Pi_safe_dress) ≤ p_fail_dress`
(as provided by `dressed_syndrome_pinched_and_variational_thermal_barrier`). -/
theorem indexed_dressed_perturbed_kms_memory_lifetime_and_drift_bound
    {D L : ℕ} {Site : BoxD D L → Type}
    [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)] [∀ x, Nonempty (Site x)]
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (sys : IndexedCommutingProjectorHamiltonian D L Site ι)
    (V : QuasiLocalPerturbation D L Site)
    (hH_pert : IsSelfAdjoint (sys.H0 + V.totalPerturbation))
    (β : ℝ)
    (U : unitary (ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site))
    (bath : Finset (BathChannel D L Site))
    (O_dec Pi_safe : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site)
    (hO_sa : IsSelfAdjoint O_dec) (hO_sq : O_dec * O_dec = 1)
    (h_comm_H0 : Commute sys.H0 O_dec)
    (hPi : IsStarProjection Pi_safe)
    (h_bath_dress : ∀ ch ∈ bath, 0 ≤ ch.γ ∧
      (U.1 * Pi_safe * U.1†) *
        (ch.L * (U.1 * O_dec * U.1†) - (U.1 * O_dec * U.1†) * ch.L) *
        (U.1 * Pi_safe * U.1†) = 0)
    {p_fail_dress : ℝ}
    (hp_le_dress :
      gibbsFailureProb (sys.H0 + V.totalPerturbation) hH_pert β (1 - U.1 * Pi_safe * U.1†) ≤ p_fail_dress) :
    let Pi_safe_dress := U.1 * Pi_safe * U.1†
    let O_dec_dress := U.1 * O_dec * U.1†
    let C_coh_dress := opCommutator (sys.H0 + V.totalPerturbation) O_dec_dress
    IsStarProjection Pi_safe_dress ∧
    IsSelfAdjoint O_dec_dress ∧
    O_dec_dress * O_dec_dress = 1 ∧
    ‖O_dec_dress‖ ≤ 1 ∧
    Commute (U.1 * sys.H0 * U.1†) O_dec_dress ∧
    ‖Pi_safe_dress * C_coh_dress * Pi_safe_dress‖ ≤
      ‖Pi_safe * opCommutator (U.1† * (sys.H0 + V.totalPerturbation) * U.1) O_dec * Pi_safe‖ ∧
    opKMSNorm (sys.H0 + V.totalPerturbation) hH_pert β C_coh_dress ≤
      ‖Pi_safe_dress * C_coh_dress * Pi_safe_dress‖ +
        2 * ‖C_coh_dress‖ * (p_fail_dress ^ (1 / 4 : ℝ)) ∧
    (∀ (O_t : ℝ → (ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site)) (t : ℝ),
      0 ≤ t →
      SatisfiesKMSLindbladODE (sys.H0 + V.totalPerturbation) hH_pert β bath O_dec_dress O_t t →
      opKMSNorm (sys.H0 + V.totalPerturbation) hH_pert β (O_t t - O_dec_dress) ≤
        kmsDriftDirichletBound
          (‖Pi_safe_dress * C_coh_dress * Pi_safe_dress‖ +
            2 * ‖C_coh_dress‖ * (p_fail_dress ^ (1 / 4 : ℝ)))
          (16 * (∑ ch ∈ bath, ch.γ * ‖ch.L‖ ^ 2) * (p_fail_dress ^ (1 / 2 : ℝ)))
          t) := by
  intro Pi_safe_dress O_dec_dress C_coh_dress
  have hPi_dress : IsStarProjection Pi_safe_dress := isStarProjection_unitary_conj U hPi
  have hO_dress_sa : IsSelfAdjoint O_dec_dress := isSelfAdjoint_unitary_conj U hO_sa
  have hO_dress_sq : O_dec_dress * O_dec_dress = 1 := sq_eq_one_unitary_conj U hO_sq
  have hO_dress_norm : ‖O_dec_dress‖ ≤ 1 :=
    norm_le_one_of_isSelfAdjoint_sq_eq_one hO_dress_sa hO_dress_sq
  have h_comm_dress : Commute (U.1 * sys.H0 * U.1†) O_dec_dress :=
    commute_unitary_conj U h_comm_H0
  have h_cov :
      ‖Pi_safe_dress * C_coh_dress * Pi_safe_dress‖ ≤
        ‖Pi_safe * opCommutator (U.1† * (sys.H0 + V.totalPerturbation) * U.1) O_dec * Pi_safe‖ := by
    rw [dressed_sandwich_opCommutator_eq U (sys.H0 + V.totalPerturbation) O_dec Pi_safe]
    exact norm_unitary_conj_le U _
  have h_kms_dress :
      opKMSNorm (sys.H0 + V.totalPerturbation) hH_pert β C_coh_dress ≤
        ‖Pi_safe_dress * C_coh_dress * Pi_safe_dress‖ +
          2 * ‖C_coh_dress‖ * (p_fail_dress ^ (1 / 4 : ℝ)) :=
    opKMSNorm_le_two_mul_norm_add_sandwich_norm (sys.H0 + V.totalPerturbation) hH_pert β hPi_dress hp_le_dress
  have hp_nonneg : 0 ≤ p_fail_dress :=
    le_trans (hilbertTrace_gibbsDensityOp_mul_proj_nonneg
      (opEigenbasis (sys.H0 + V.totalPerturbation) hH_pert) (opEigenvalues (sys.H0 + V.totalPerturbation) hH_pert) β
      (opEigenbasis_orthonormal (sys.H0 + V.totalPerturbation) hH_pert)
      (hilbertTrace_eq_sum_opEigenbasis (sys.H0 + V.totalPerturbation) hH_pert) hPi_dress.one_sub) hp_le_dress
  refine ⟨hPi_dress, hO_dress_sa, hO_dress_sq, hO_dress_norm, h_comm_dress, h_cov, h_kms_dress,
    fun O_t t ht h_ode => ?_⟩
  exact opKMSNorm_le_kmsDriftDirichletBound_of_commutator_bound
    (sys.H0 + V.totalPerturbation) hH_pert β bath O_dec_dress Pi_safe_dress C_coh_dress
    hO_dress_sa hO_dress_norm rfl (by positivity) h_kms_dress
    hPi_dress h_bath_dress hp_le_dress O_t t ht h_ode

end
