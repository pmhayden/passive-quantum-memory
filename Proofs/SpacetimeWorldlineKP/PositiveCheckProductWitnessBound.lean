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

import Proofs.DressedThermalDuhamel.LocalGroundProjectorAnnihilation

/-!
# Positive Check-Product Witness Projectors and Unsafe Gibbs Trace Dominance

Defines positive check-product witness projectors (`positiveCheckWitnessProj`) and witness covers of the unsafe syndrome complement (`IsPositiveCheckWitnessCover`). Uses operator positivity of `gibbsBoltzmannOp` and commuting syndrome resolutions to bound the unsafe Gibbs trace by the sum of positive witness traces (`hilbertTrace_gibbsBoltzmannOp_unsafe_le_sum_positiveCheckWitnessProj`).

## References

* Part II, Section 3.1 (`subsec:weyl-witness-poisson`), Lemma 3.2 (`lem:positive-witness-bound`)
-/

noncomputable section

open scoped Classical BigOperators InnerProduct ComplexConjugate
open Filter Topology Asymptotics ContinuousLinearMap KMSPinchedGibbs PerturbedThermalBarrier

set_option linter.constructorNameAsVariable false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000

namespace SpacetimeWorldlineKP

/-- **Indexed Check-Commuting Perturbation Commutes with Syndrome Projectors
    (`indexed_check_commuting_perturbation_commutes_with_syndromeProjector`)**:
    Whenever an operator $M$ commutes with every check projector `sys.checkProj i` (`i : ι`),
    $M$ commutes with every `sys.syndromeProjector σ`, every `indexedBareFailureProjector sys S_safe`,
    and `sys.H0 + M` commutes with every `sys.syndromeProjector σ`. -/
theorem indexed_check_commuting_perturbation_commutes_with_syndromeProjector {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (sys : IndexedCommutingProjectorHamiltonian D L Site ι)
    (M : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site)
    (h_comm : ∀ i : ι, Commute M (sys.checkProj i)) :
    (∀ σ : ι → Bool, Commute M (sys.syndromeProjector σ)) ∧
    (∀ S_safe : Finset (ι → Bool), Commute M (indexedBareFailureProjector sys S_safe)) ∧
    (∀ σ : ι → Bool, Commute (sys.H0 + M) (sys.syndromeProjector σ)) := by
  have h_res := syndrome_resolution_indexed sys
  have h_syn : ∀ σ : ι → Bool, Commute M (sys.syndromeProjector σ) := by
    intro σ
    unfold IndexedCommutingProjectorHamiltonian.syndromeProjector
    apply Commute.list_prod_right
    intro P hP
    rcases List.mem_map.mp hP with ⟨i, _, rfl⟩
    by_cases hσ : σ i
    · simp [hσ, h_comm i]
    · simp [hσ, Commute.sub_right (Commute.one_right M) (h_comm i)]
  refine ⟨h_syn, fun S_safe => ?_, fun σ => ?_⟩
  · unfold indexedBareFailureProjector
    exact Commute.sum_right S_safe _ M fun σ _ => h_syn σ
  · exact Commute.add_left (h_res.2.2.2.2.2.2.2 σ) (h_syn σ)

/-- **Basis-Free Commuting Projection Eigenvalue & Quadratic Form Identity
    (`commute_opEigenbasis_quadForm_eq`)**:
    If $H$ is self-adjoint (`hH`), $P_{\mathrm{proj}}$ is a star projection (`hP_proj`), and $[H, P_{\mathrm{proj}}] = 0$, then for
    every canonical eigenstate $\psi_\omega = \mathrm{opEigenbasis}\ H\ hH\ \omega$:
    1. $H(P_{\mathrm{proj}} \psi_\omega) = E_\omega (P_{\mathrm{proj}} \psi_\omega)$;
    2. $\operatorname{Re}\langle P_{\mathrm{proj}} \psi_\omega, H (P_{\mathrm{proj}} \psi_\omega) \rangle = E_\omega \|P_{\mathrm{proj}} \psi_\omega\|^2$. -/
theorem commute_opEigenbasis_quadForm_eq {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    [∀ x, Nonempty (Site x)]
    (H P_proj : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site)
    (hH : IsSelfAdjoint H) (hP_proj : IsStarProjection P_proj) (h_comm : Commute H P_proj)
    (ω : ManyBodyConfig Site) :
    H (P_proj (opEigenbasis H hH ω)) =
      (opEigenvalues H hH ω : ℂ) • (P_proj (opEigenbasis H hH ω)) ∧
    RCLike.re (inner ℂ (P_proj (opEigenbasis H hH ω)) (H (P_proj (opEigenbasis H hH ω)))) =
      opEigenvalues H hH ω * ‖P_proj (opEigenbasis H hH ω)‖ ^ 2 ∧
    RCLike.re (inner ℂ (P_proj (opEigenbasis H hH ω)) (H (P_proj (opEigenbasis H hH ω)))) =
      opEigenvalues H hH ω *
        RCLike.re (inner ℂ (opEigenbasis H hH ω) (P_proj (opEigenbasis H hH ω))) := by
  have h_eig :
      H (P_proj (opEigenbasis H hH ω)) =
        (opEigenvalues H hH ω : ℂ) • (P_proj (opEigenbasis H hH ω)) := by
    calc H (P_proj (opEigenbasis H hH ω))
      _ = (H * P_proj) (opEigenbasis H hH ω) := rfl
      _ = (P_proj * H) (opEigenbasis H hH ω) := by rw [h_comm.eq]
      _ = P_proj (H (opEigenbasis H hH ω)) := rfl
      _ = P_proj ((opEigenvalues H hH ω : ℂ) • opEigenbasis H hH ω) := by
        rw [opEigenbasis_apply_H H hH ω]
      _ = (opEigenvalues H hH ω : ℂ) • (P_proj (opEigenbasis H hH ω)) := map_smul P_proj _ _
  have h_quad :
      RCLike.re (inner ℂ (P_proj (opEigenbasis H hH ω)) (H (P_proj (opEigenbasis H hH ω)))) =
        opEigenvalues H hH ω * ‖P_proj (opEigenbasis H hH ω)‖ ^ 2 := by
    rw [h_eig, inner_smul_right, re_ofReal_mul, inner_self_eq_norm_sq]
  refine ⟨h_eig, h_quad, ?_⟩
  rw [h_quad, ← isStarProjection_re_inner_eq_norm_sq hP_proj (opEigenbasis H hH ω)]

/-! ## 1. Positive Check-Product Witness Projector `positiveCheckWitnessProj` -/

/-- **Positive Check-Product Witness Projector (`positiveCheckWitnessProj`)**:
    For a commuting-projector Hamiltonian `sys` and a finite subset of checks `W : Finset ι`,
    $$\Pi_W := \prod_{c \in W} (1 - P_c)$$
    is the orthogonal projection onto states violating every check $c \in W$
    (Part II, Section 3.1 (`subsec:weyl-witness-poisson`), Lemma 3.2 (`lem:positive-witness-bound`), Equation `eq:positive-witness-dom`). -/
def positiveCheckWitnessProj {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (sys : IndexedCommutingProjectorHamiltonian D L Site ι)
    (W : Finset ι) :
    ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site :=
  ∑ σ ∈ Finset.univ.filter (fun σ : ι → Bool => ∀ c ∈ W, σ c = true),
    sys.syndromeProjector σ

/-- **Witness Cover Predicate (`IsPositiveCheckWitnessCover`)**:
    A finite family `W_family : Finset (Finset ι)` of check subsets covers the unsafe syndrome
    complement of `S_safe : Finset (ι → Bool)` if every unsafe syndrome $\sigma \notin S_{\mathrm{safe}}$
    violates all checks of at least one witness $W \in W_{\mathrm{family}}$. -/
def IsPositiveCheckWitnessCover {ι : Type} [Fintype ι] [DecidableEq ι]
    (S_safe : Finset (ι → Bool))
    (W_family : Finset (Finset ι)) : Prop :=
  ∀ σ : ι → Bool, σ ∉ S_safe → ∃ W ∈ W_family, ∀ c ∈ W, σ c = true

/-! ## 2. Algebraic & Syndrome-Basis Properties of `positiveCheckWitnessProj` -/

/-- **`positiveCheckWitnessProj` Is an Orthogonal Star-Projection (`isStarProjection_positiveCheckWitnessProj`)**:
    For every check subset $W \subseteq \iota$, $\Pi_W$ is self-adjoint and idempotent
    (`IsStarProjection (positiveCheckWitnessProj sys W)`), and commutes with `sys.H0` and every
    `sys.syndromeProjector σ`. -/
theorem isStarProjection_positiveCheckWitnessProj {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (sys : IndexedCommutingProjectorHamiltonian D L Site ι)
    (W : Finset ι) :
    IsStarProjection (positiveCheckWitnessProj sys W) ∧
    Commute sys.H0 (positiveCheckWitnessProj sys W) ∧
    ∀ σ : ι → Bool,
      positiveCheckWitnessProj sys W * sys.syndromeProjector σ =
        if (∀ c ∈ W, σ c = true) then sys.syndromeProjector σ else 0 := by
  have h_res := syndrome_resolution_indexed sys
  refine ⟨(indexedBareFailureProjector_props sys
      (Finset.univ.filter (fun σ : ι → Bool => ∀ c ∈ W, σ c = true))).1, ?_, ?_⟩
  · unfold positiveCheckWitnessProj
    exact Commute.sum_right _ _ _ (fun σ _ => h_res.2.2.2.2.2.2.2 σ)
  · intro σ
    unfold positiveCheckWitnessProj
    rw [Finset.sum_mul]
    by_cases hW : ∀ c ∈ W, σ c = true
    · rw [if_pos hW, Finset.sum_eq_single σ]
      · exact (h_res.2.1 σ).isIdempotentElem.eq
      · intro τ _ hne
        exact h_res.2.2.1 τ σ hne
      · intro h_not
        exact False.elim (h_not (Finset.mem_filter.mpr ⟨Finset.mem_univ σ, hW⟩))
    · rw [if_neg hW]
      refine Finset.sum_eq_zero fun τ hτ => ?_
      have hne : τ ≠ σ := by
        rintro rfl
        exact hW (Finset.mem_filter.mp hτ).2
      exact h_res.2.2.1 τ σ hne

private lemma re_inner_sum_syndromeProjector {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (sys : IndexedCommutingProjectorHamiltonian D L Site ι)
    (S : Finset (ι → Bool)) (ψ : ManyBodyHilbertSpace Site) :
    RCLike.re (inner ℂ ψ ((∑ σ ∈ S, sys.syndromeProjector σ) ψ)) =
      ∑ σ ∈ S, RCLike.re (inner ℂ ψ (sys.syndromeProjector σ ψ)) := by
  rw [ContinuousLinearMap.sum_apply, inner_sum, map_sum]

private lemma sum_sdiff_le_sum_witness_cover {ι : Type} [Fintype ι] [DecidableEq ι]
    {S_safe : Finset (ι → Bool)} {W_family : Finset (Finset ι)}
    (h_cover : IsPositiveCheckWitnessCover S_safe W_family)
    (a : (ι → Bool) → ℝ) (ha : ∀ σ : ι → Bool, 0 ≤ a σ) :
    (∑ σ ∈ Finset.univ \ S_safe, a σ) ≤
      ∑ W ∈ W_family,
        ∑ σ ∈ Finset.univ.filter (fun σ : ι → Bool => ∀ c ∈ W, σ c = true), a σ := by
  calc ∑ σ ∈ Finset.univ \ S_safe, a σ
    _ ≤ ∑ σ ∈ Finset.univ \ S_safe,
          ∑ W ∈ W_family, (if (∀ c ∈ W, σ c = true) then a σ else 0) := by
      refine Finset.sum_le_sum fun σ hσ => ?_
      obtain ⟨W₀, hW₀_mem, hW₀⟩ := h_cover σ (Finset.mem_sdiff.mp hσ).2
      calc a σ
        _ = if (∀ c ∈ W₀, σ c = true) then a σ else 0 := (if_pos hW₀).symm
        _ ≤ ∑ W ∈ W_family, (if (∀ c ∈ W, σ c = true) then a σ else 0) :=
          Finset.single_le_sum (f := fun W => if (∀ c ∈ W, σ c = true) then a σ else 0)
            (fun W _ => by (try dsimp only); split_ifs <;> [exact ha σ; exact le_rfl]) hW₀_mem
    _ ≤ ∑ σ : ι → Bool,
          ∑ W ∈ W_family, (if (∀ c ∈ W, σ c = true) then a σ else 0) :=
      Finset.sum_le_univ_sum_of_nonneg fun σ =>
        Finset.sum_nonneg fun W _ => by split_ifs <;> [exact ha σ; exact le_rfl]
    _ = ∑ W ∈ W_family,
          ∑ σ : ι → Bool, (if (∀ c ∈ W, σ c = true) then a σ else 0) := Finset.sum_comm
    _ = ∑ W ∈ W_family,
          ∑ σ ∈ Finset.univ.filter (fun σ : ι → Bool => ∀ c ∈ W, σ c = true), a σ := by
      refine Finset.sum_congr rfl fun W _ => ?_
      rw [Finset.sum_filter]

/-- **Quadratic-Form Loewner Dominance of Unsafe Complement by Positive Witness Projectors
    (`inner_unsafe_complement_le_sum_positiveCheckWitnessProj`)**:
    Under `IsPositiveCheckWitnessCover S_safe W_family`, for every state vector $\psi$,
    $$0 \le \operatorname{Re}\langle \psi, (1 - \Pi_{\mathrm{safe}}) \psi \rangle
      \le \sum_{W \in W_{\mathrm{family}}} \operatorname{Re}\langle \psi, \Pi_W \psi \rangle.$$ -/
theorem inner_unsafe_complement_le_sum_positiveCheckWitnessProj {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (sys : IndexedCommutingProjectorHamiltonian D L Site ι)
    {S_safe : Finset (ι → Bool)} {W_family : Finset (Finset ι)}
    (h_cover : IsPositiveCheckWitnessCover S_safe W_family)
    (ψ : ManyBodyHilbertSpace Site) :
    let Pi_safe := indexedBareFailureProjector sys S_safe
    0 ≤ RCLike.re (inner ℂ ψ ((1 - Pi_safe) ψ)) ∧
    RCLike.re (inner ℂ ψ ((1 - Pi_safe) ψ)) ≤
      ∑ W ∈ W_family, RCLike.re (inner ℂ ψ (positiveCheckWitnessProj sys W ψ)) := by
  intro Pi_safe
  have h_res := syndrome_resolution_indexed sys
  have h_sub : 1 - Pi_safe = ∑ σ ∈ Finset.univ \ S_safe, sys.syndromeProjector σ :=
    (indexedBareFailureProjector_props sys S_safe).2
  have ha_nonneg : ∀ σ : ι → Bool, 0 ≤ RCLike.re (inner ℂ ψ (sys.syndromeProjector σ ψ)) :=
    fun σ => (h_res.2.1 σ).re_inner_nonneg ψ
  refine ⟨?_, ?_⟩
  · rw [h_sub, re_inner_sum_syndromeProjector]
    exact Finset.sum_nonneg fun σ _ => ha_nonneg σ
  · rw [h_sub, re_inner_sum_syndromeProjector]
    have h_le := sum_sdiff_le_sum_witness_cover h_cover
      (fun σ => RCLike.re (inner ℂ ψ (sys.syndromeProjector σ ψ))) ha_nonneg
    refine h_le.trans (le_of_eq ?_)
    refine Finset.sum_congr rfl fun W _ => ?_
    unfold positiveCheckWitnessProj
    exact (re_inner_sum_syndromeProjector sys _ ψ).symm

/-! ## 3. Unpinched Gibbs Trace & Failure Probability Witness Bound (Part II, Lemma 3.2 (`lem:positive-witness-bound`)) -/

private lemma gibbsFailureProb_eq_inv_partitionZ_mul_boltzmann_trace {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    (H : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site)
    (hH : IsSelfAdjoint H) (β : ℝ)
    (M : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site) :
    gibbsFailureProb H hH β M =
      (gibbsPartitionZ (opEigenvalues H hH) β)⁻¹ *
        hilbertTrace (gibbsBoltzmannOp (opEigenbasis H hH) (opEigenvalues H hH) β * M) := by
  unfold gibbsFailureProb gibbsDensityOp
  rw [clm_smul_mul, ← Complex.ofReal_inv, KMSPinchedGibbs.hilbertTrace_smul_ofReal]

/-- **Unpinched Gibbs Trace & Failure Probability Witness Bound
    (`hilbertTrace_gibbsBoltzmannOp_unsafe_le_sum_positiveCheckWitnessProj`,
    Part II, Section 3.1 (`subsec:weyl-witness-poisson`), Lemma 3.2 (`lem:positive-witness-bound`), Equation `eq:trace-witness-sum`)**:
    For any self-adjoint Hamiltonian $H$ (`hH : IsSelfAdjoint H`), inverse temperature $\beta \in \mathbb{R}$,
    and witness cover `IsPositiveCheckWitnessCover S_safe W_family`, every term
    $\operatorname{Tr}(e^{-\beta H} \Pi_W)$ is real and non-negative, and the unpinched failure
    trace and Gibbs failure probability satisfy:
    $$\operatorname{Tr}\bigl(e^{-\beta H} (1 - \Pi_{\mathrm{safe}})\bigr)
      \le \sum_{W \in W_{\mathrm{family}}} \operatorname{Tr}\bigl(e^{-\beta H} \Pi_W\bigr),$$
    $$\mathrm{gibbsFailureProb}(H, hH, \beta, 1 - \Pi_{\mathrm{safe}})
      \le \sum_{W \in W_{\mathrm{family}}}
        \mathrm{gibbsFailureProb}(H, hH, \beta, \mathrm{positiveCheckWitnessProj}\;\mathrm{sys}\;W).$$ -/
theorem hilbertTrace_gibbsBoltzmannOp_unsafe_le_sum_positiveCheckWitnessProj {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    [∀ x, Nonempty (Site x)]
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (sys : IndexedCommutingProjectorHamiltonian D L Site ι)
    (H : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site)
    (hH : IsSelfAdjoint H) (β : ℝ)
    {S_safe : Finset (ι → Bool)} {W_family : Finset (Finset ι)}
    (h_cover : IsPositiveCheckWitnessCover S_safe W_family) :
    let Pi_safe := indexedBareFailureProjector sys S_safe
    (∀ W ∈ W_family,
      0 ≤ hilbertTrace (gibbsBoltzmannOp (opEigenbasis H hH) (opEigenvalues H hH) β *
        positiveCheckWitnessProj sys W)) ∧
    hilbertTrace (gibbsBoltzmannOp (opEigenbasis H hH) (opEigenvalues H hH) β * (1 - Pi_safe)) ≤
      ∑ W ∈ W_family,
        hilbertTrace (gibbsBoltzmannOp (opEigenbasis H hH) (opEigenvalues H hH) β *
          positiveCheckWitnessProj sys W) ∧
    gibbsFailureProb H hH β (1 - Pi_safe) ≤
      ∑ W ∈ W_family, gibbsFailureProb H hH β (positiveCheckWitnessProj sys W) := by
  intro Pi_safe
  let ψ_eig := opEigenbasis H hH
  let E_eig := opEigenvalues H hH
  have h_tr_le :
      hilbertTrace (gibbsBoltzmannOp ψ_eig E_eig β * (1 - Pi_safe)) ≤
        ∑ W ∈ W_family,
          hilbertTrace (gibbsBoltzmannOp ψ_eig E_eig β * positiveCheckWitnessProj sys W) := by
    rw [hilbertTrace_gibbsBoltzmannOp_mul_eq]
    calc ∑ ω : ManyBodyConfig Site,
          Real.exp (-β * E_eig ω) * RCLike.re (inner ℂ (ψ_eig ω) ((1 - Pi_safe) (ψ_eig ω)))
      _ ≤ ∑ ω : ManyBodyConfig Site,
            Real.exp (-β * E_eig ω) *
              (∑ W ∈ W_family,
                RCLike.re (inner ℂ (ψ_eig ω) (positiveCheckWitnessProj sys W (ψ_eig ω)))) := by
        refine Finset.sum_le_sum fun ω _ => ?_
        exact mul_le_mul_of_nonneg_left
          (inner_unsafe_complement_le_sum_positiveCheckWitnessProj sys h_cover (ψ_eig ω)).2
          (le_of_lt (Real.exp_pos _))
      _ = ∑ W ∈ W_family,
            ∑ ω : ManyBodyConfig Site,
              Real.exp (-β * E_eig ω) *
                RCLike.re (inner ℂ (ψ_eig ω) (positiveCheckWitnessProj sys W (ψ_eig ω))) := by
        simp_rw [Finset.mul_sum]
        exact Finset.sum_comm
      _ = ∑ W ∈ W_family,
            hilbertTrace (gibbsBoltzmannOp ψ_eig E_eig β * positiveCheckWitnessProj sys W) := by
        refine Finset.sum_congr rfl fun W _ => ?_
        exact (hilbertTrace_gibbsBoltzmannOp_mul_eq ψ_eig E_eig β
          (positiveCheckWitnessProj sys W)).symm
  refine ⟨?_, h_tr_le, ?_⟩
  · intro W _
    rw [hilbertTrace_gibbsBoltzmannOp_mul_eq]
    exact Finset.sum_nonneg fun ω _ =>
      mul_nonneg (le_of_lt (Real.exp_pos _))
        ((isStarProjection_positiveCheckWitnessProj sys W).1.re_inner_nonneg (ψ_eig ω))
  · rw [gibbsFailureProb_eq_inv_partitionZ_mul_boltzmann_trace]
    have h_rhs :
        (∑ W ∈ W_family, gibbsFailureProb H hH β (positiveCheckWitnessProj sys W)) =
          (gibbsPartitionZ E_eig β)⁻¹ *
            ∑ W ∈ W_family,
              hilbertTrace (gibbsBoltzmannOp ψ_eig E_eig β * positiveCheckWitnessProj sys W) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun W _ => ?_
      exact gibbsFailureProb_eq_inv_partitionZ_mul_boltzmann_trace H hH β
        (positiveCheckWitnessProj sys W)
    rw [h_rhs]
    exact mul_le_mul_of_nonneg_left h_tr_le
      (inv_nonneg.mpr (le_of_lt (gibbsPartitionZ_pos E_eig β)))

end SpacetimeWorldlineKP

end
