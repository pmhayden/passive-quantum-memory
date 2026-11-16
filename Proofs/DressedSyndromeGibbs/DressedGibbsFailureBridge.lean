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

import Proofs.SpectralAndGibbsLemmas
import Proofs.DressedSyndromeGibbs.DressedSectorTraceAndPeeling

open scoped Classical InnerProduct ComplexConjugate BigOperators
open Filter Topology Asymptotics ContinuousLinearMap KMSPinchedGibbs

noncomputable section

/-!
# Dressed Gibbs Partition Decomposition and Sector Boltzmann Peeling

Decomposes the Gibbs partition function and unsafe-subspace failure probability across QAC-dressed syndrome sectors (`indexed_dressed_gibbs_partition_and_failure_decomp`), proves syndrome-fiber cardinality invariance under unitary conjugation (`indexed_card_syndrome_fiber_eq_of_unitary_conj`), and establishes averaged sector Boltzmann peeling (`indexed_sector_boltzmann_sum_peel_of_avg_diff`).

## References

* Part II, Section 5.2 (`subsec:low-temp-crossover`), Theorem 5.3 (`thm:low-temperature-window-and-crossover`)
* Part II, Section 6.1 (`subsec:fourth-root-firewall`), Lemma 6.1 (`lem:kms-fourth-root`)
-/

namespace PerturbedThermalBarrier

/-! ## 1. Dressed Gibbs Partition Decomposition & Master Fourth-Root Bound -/

/-- Star-projection and complement expansion for `indexedBareFailureProjector sys S`. -/
lemma indexedBareFailureProjector_props {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (sys : IndexedCommutingProjectorHamiltonian D L Site ι)
    (S : Finset (ι → Bool)) :
    IsStarProjection (indexedBareFailureProjector sys S) ∧
    1 - indexedBareFailureProjector sys S =
      ∑ σ ∈ Finset.univ \ S, sys.syndromeProjector σ := by
  have h_res := syndrome_resolution_indexed sys
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · dsimp [indexedBareFailureProjector]
    rw [IsIdempotentElem, Finset.mul_sum]
    refine Finset.sum_congr rfl fun σ hσ => ?_
    rw [Finset.sum_mul, Finset.sum_eq_single σ]
    · exact (h_res.2.1 σ).isIdempotentElem.eq
    · intro τ _ hne; exact h_res.2.2.1 τ σ hne
    · intro h_not; exact False.elim (h_not hσ)
  · dsimp [indexedBareFailureProjector]
    apply isSelfAdjoint_finset_sum
    intro σ _; exact (h_res.2.1 σ).isSelfAdjoint
  · dsimp [indexedBareFailureProjector]
    have h_split := Finset.sum_sdiff (Finset.subset_univ S) (f := fun σ => sys.syndromeProjector σ)
    rw [h_res.2.2.2.1] at h_split
    exact sub_eq_of_eq_add h_split.symm

/-- Spectral expansion of `hilbertTrace (gibbsBoltzmannOp ψ_eig E_eig β * M)`. -/
lemma hilbertTrace_gibbsBoltzmannOp_mul_eq {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    (ψ_eig : ManyBodyConfig Site → ManyBodyHilbertSpace Site)
    (E_eig : ManyBodyConfig Site → ℝ) (β : ℝ)
    (M : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site) :
    hilbertTrace (gibbsBoltzmannOp ψ_eig E_eig β * M) =
      ∑ ω : ManyBodyConfig Site,
        Real.exp (-β * E_eig ω) * RCLike.re (inner ℂ (ψ_eig ω) (M (ψ_eig ω))) := by
  rw [hilbertTrace_mul_comm_aux, gibbsBoltzmannOp, Finset.mul_sum, hilbertTrace_sum]
  refine Finset.sum_congr rfl fun ω _ => ?_
  rw [clm_mul_smul, hilbertTrace_smul_ofReal, hilbertTrace_mul_rankOneKetBra]

/-- For any Hamiltonian $H$ with eigenbasis $\psi_{\mathrm{eig}}$ and eigenvalues $E_{\mathrm{eig}}$,
    the sum of dressed sector Boltzmann traces over all $\sigma : \iota \to \mathrm{Bool}$
    equals $\mathrm{gibbsPartitionZ}\ E_{\mathrm{eig}}\ \beta$. -/
theorem indexed_dressed_gibbs_partition_and_failure_decomp {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    [∀ x, Nonempty (Site x)]
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (sys : IndexedCommutingProjectorHamiltonian D L Site ι)
    (H : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site) (hH : IsSelfAdjoint H)
    (U : unitary (ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site))
    (S_safe : Finset (ι → Bool)) (β : ℝ) :
    let ψ_eig := opEigenbasis H hH
    let E_eig := opEigenvalues H hH
    let Pi_safe := indexedBareFailureProjector sys S_safe
    let Z_sec : (ι → Bool) → ℝ := fun σ =>
      hilbertTrace (gibbsBoltzmannOp ψ_eig E_eig β * indexedDressedSyndromeProjector sys U σ)
    (∀ σ : ι → Bool, 0 ≤ Z_sec σ) ∧
    (∑ σ : ι → Bool, Z_sec σ) = gibbsPartitionZ E_eig β ∧
    gibbsFailureProb H hH β (1 - U.1 * Pi_safe * U.1†) =
      (gibbsPartitionZ E_eig β)⁻¹ * ∑ σ ∈ Finset.univ \ S_safe, Z_sec σ := by
  intro ψ_eig E_eig Pi_safe Z_sec
  have h_onb := opEigenbasis_orthonormal H hH
  have h_res := indexed_dressed_syndrome_resolution sys U
  have hZ_nonneg : ∀ σ : ι → Bool, 0 ≤ Z_sec σ := by
    intro σ
    dsimp [Z_sec]
    rw [hilbertTrace_gibbsBoltzmannOp_mul_eq]
    exact Finset.sum_nonneg fun ω _ =>
      mul_nonneg (le_of_lt (Real.exp_pos _)) ((h_res.2.2.2.1 σ).re_inner_nonneg (ψ_eig ω))
  have hZ_sum : (∑ σ : ι → Bool, Z_sec σ) = gibbsPartitionZ E_eig β := by
    dsimp [Z_sec]
    rw [← hilbertTrace_sum, ← Finset.mul_sum, h_res.2.2.2.2.2.1,
      hilbertTrace_gibbsBoltzmannOp_mul_eq]
    unfold gibbsPartitionZ
    refine Finset.sum_congr rfl fun ω _ => ?_
    rw [ContinuousLinearMap.one_apply, h_onb ω ω, if_pos rfl, RCLike.one_re, mul_one]
  have h_fail_eq :
      gibbsFailureProb H hH β (1 - U.1 * Pi_safe * U.1†) =
        (gibbsPartitionZ E_eig β)⁻¹ * ∑ σ ∈ Finset.univ \ S_safe, Z_sec σ := by
    unfold gibbsFailureProb gibbsDensityOp
    have h_comp : 1 - U.1 * Pi_safe * U.1† =
        ∑ σ ∈ Finset.univ \ S_safe, indexedDressedSyndromeProjector sys U σ := by
      have h_sub_prop := (indexedBareFailureProjector_props sys S_safe).2
      have hU_mul : U.1 * U.1† = 1 := Unitary.coe_mul_star_self U
      calc 1 - U.1 * Pi_safe * U.1†
        _ = U.1 * (1 - Pi_safe) * U.1† := by
          rw [mul_sub, sub_mul, mul_one, hU_mul]
        _ = U.1 * (∑ σ ∈ Finset.univ \ S_safe, sys.syndromeProjector σ) * U.1† := by
          rw [h_sub_prop]
        _ = ∑ σ ∈ Finset.univ \ S_safe, indexedDressedSyndromeProjector sys U σ := by
          rw [Finset.mul_sum, Finset.sum_mul]; rfl
    rw [h_comp, clm_smul_mul, ← Complex.ofReal_inv, hilbertTrace_smul_ofReal,
      Finset.mul_sum, hilbertTrace_sum]
  exact ⟨hZ_nonneg, hZ_sum, h_fail_eq⟩

/-! ## 2. Syndrome-Fiber Multiplicity Invariance and Averaged Sector Boltzmann Peeling -/

/-- Unitary repair conjugation `E_K.1† * sys.syndromeProjector σ * E_K.1 = sys.syndromeProjector σ_ext`
    implies equal eigenstate fiber cardinalities $|F_\sigma| = |F_{\sigma_{\mathrm{ext}}}|$. -/
lemma indexed_card_syndrome_fiber_eq_of_unitary_conj {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (sys : IndexedCommutingProjectorHamiltonian D L Site ι)
    (U E_K : unitary (ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site))
    (ψ_eig : ManyBodyConfig Site → ManyBodyHilbertSpace Site)
    (σ_eig : ManyBodyConfig Site → (ι → Bool))
    (h_id : (∑ ω : ManyBodyConfig Site, rankOneKetBra (ψ_eig ω)) = 1)
    (h_eig_proj : ∀ ω : ManyBodyConfig Site,
      indexedDressedSyndromeProjector sys U (σ_eig ω) (ψ_eig ω) = ψ_eig ω ∧
      hilbertTrace (rankOneKetBra (ψ_eig ω)) = 1)
    {σ σ_ext : ι → Bool}
    (hEK : E_K.1† * sys.syndromeProjector σ * E_K.1 = sys.syndromeProjector σ_ext) :
    (Finset.univ.filter (fun ω : ManyBodyConfig Site => σ_eig ω = σ)).card =
      (Finset.univ.filter (fun ω : ManyBodyConfig Site => σ_eig ω = σ_ext)).card := by
  have h_res := indexed_dressed_syndrome_resolution sys U
  have h_card : ∀ τ : ι → Bool,
      hilbertTrace (sys.syndromeProjector τ) =
        ((Finset.univ.filter (fun ω : ManyBodyConfig Site => σ_eig ω = τ)).card : ℝ) := by
    intro τ
    rw [← h_res.2.2.2.2.2.2.2 τ,
      indexedDressedSyndromeProjector_eq_sum_ketBra sys U ψ_eig σ_eig h_id h_eig_proj τ,
      hilbertTrace_sum]
    have h_one : ∀ ω ∈ Finset.univ.filter (fun ω : ManyBodyConfig Site => σ_eig ω = τ),
        hilbertTrace (rankOneKetBra (ψ_eig ω)) = (1 : ℝ) := fun ω _ => (h_eig_proj ω).2
    rw [Finset.sum_congr rfl h_one, Finset.sum_const, nsmul_eq_mul, mul_one]
  have h_tr_eq : hilbertTrace (sys.syndromeProjector σ) =
      hilbertTrace (sys.syndromeProjector σ_ext) := by
    rw [← hEK, hilbertTrace_conj_unitary_adj E_K (sys.syndromeProjector σ)]
  rw [h_card σ, h_card σ_ext] at h_tr_eq
  exact Nat.cast_injective h_tr_eq

/-- Indexed sector Boltzmann sum peeling inequality from bare energy drop, trace-average collar shift,
    and sector eigenvalue splitting. -/
lemma indexed_sector_boltzmann_sum_peel_of_avg_diff {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (sys : IndexedCommutingProjectorHamiltonian D L Site ι)
    (σ_eig : ManyBodyConfig Site → (ι → Bool)) (E_eig : ManyBodyConfig Site → ℝ)
    {σ σ_ext : ι → Bool} {w : ℕ} {μ_σ μ_ext δ : ℝ}
    (hN_eq : (Finset.univ.filter (fun ω : ManyBodyConfig Site => σ_eig ω = σ)).card =
      (Finset.univ.filter (fun ω : ManyBodyConfig Site => σ_eig ω = σ_ext)).card)
    (h_wt_drop : sys.syndromeEnergy σ - sys.syndromeEnergy σ_ext ≥ (w : ℝ) - 4)
    (h_avg_diff : |μ_σ - μ_ext| ≤ (1 / 4 : ℝ) * ((w : ℝ) + 4))
    (h_split_σ : ∀ ω : ManyBodyConfig Site, σ_eig ω = σ →
      |E_eig ω - sys.syndromeEnergy σ - μ_σ| ≤ (1 / 2 : ℝ) * δ)
    (h_split_ext : ∀ ω : ManyBodyConfig Site, σ_eig ω = σ_ext →
      |E_eig ω - sys.syndromeEnergy σ_ext - μ_ext| ≤ (1 / 2 : ℝ) * δ)
    {β : ℝ} (hβ : β > 0) :
    (∑ ω ∈ Finset.univ.filter (fun ω : ManyBodyConfig Site => σ_eig ω = σ),
      Real.exp (-β * E_eig ω)) ≤
    Real.exp (-β * ((3 / 4 : ℝ) * (w : ℝ) - 5 - δ)) *
      (∑ ω ∈ Finset.univ.filter (fun ω : ManyBodyConfig Site => σ_eig ω = σ_ext),
        Real.exp (-β * E_eig ω)) := by
  let E_low_σ := sys.syndromeEnergy σ + μ_σ - (1 / 2 : ℝ) * δ
  let E_high_ext := sys.syndromeEnergy σ_ext + μ_ext + (1 / 2 : ℝ) * δ
  have h_gap : E_low_σ - E_high_ext ≥ (3 / 4 : ℝ) * (w : ℝ) - 5 - δ := by
    have h_mu := (abs_le.mp h_avg_diff).1
    dsimp [E_low_σ, E_high_ext]; linarith
  have h_upper_σ : ∀ ω ∈ Finset.univ.filter (fun ω : ManyBodyConfig Site => σ_eig ω = σ),
      Real.exp (-β * E_eig ω) ≤ Real.exp (-β * E_low_σ) := fun ω hω =>
    Real.exp_le_exp.mpr (by
      have := (abs_le.mp (h_split_σ ω (Finset.mem_filter.mp hω).2)).1
      dsimp [E_low_σ]; nlinarith)
  have h_lower_ext : ∀ ω ∈ Finset.univ.filter (fun ω : ManyBodyConfig Site => σ_eig ω = σ_ext),
      Real.exp (-β * E_high_ext) ≤ Real.exp (-β * E_eig ω) := fun ω hω =>
    Real.exp_le_exp.mpr (by
      have := (abs_le.mp (h_split_ext ω (Finset.mem_filter.mp hω).2)).2
      dsimp [E_high_ext]; nlinarith)
  have h_exp_gap :
      Real.exp (-β * E_low_σ) ≤
        Real.exp (-β * ((3 / 4 : ℝ) * (w : ℝ) - 5 - δ)) * Real.exp (-β * E_high_ext) := by
    rw [← Real.exp_add]; exact Real.exp_le_exp.mpr (by nlinarith)
  calc ∑ ω ∈ Finset.univ.filter (fun ω : ManyBodyConfig Site => σ_eig ω = σ),
        Real.exp (-β * E_eig ω)
    _ ≤ ∑ _ω ∈ Finset.univ.filter (fun ω : ManyBodyConfig Site => σ_eig ω = σ),
        Real.exp (-β * E_low_σ) := Finset.sum_le_sum h_upper_σ
    _ = ((Finset.univ.filter (fun ω : ManyBodyConfig Site => σ_eig ω = σ_ext)).card : ℝ) *
        Real.exp (-β * E_low_σ) := by rw [Finset.sum_const, nsmul_eq_mul, hN_eq]
    _ ≤ ((Finset.univ.filter (fun ω : ManyBodyConfig Site => σ_eig ω = σ_ext)).card : ℝ) *
        (Real.exp (-β * ((3 / 4 : ℝ) * (w : ℝ) - 5 - δ)) * Real.exp (-β * E_high_ext)) :=
      mul_le_mul_of_nonneg_left h_exp_gap (Nat.cast_nonneg _)
    _ = Real.exp (-β * ((3 / 4 : ℝ) * (w : ℝ) - 5 - δ)) *
        ∑ _ω ∈ Finset.univ.filter (fun ω : ManyBodyConfig Site => σ_eig ω = σ_ext),
          Real.exp (-β * E_high_ext) := by rw [Finset.sum_const, nsmul_eq_mul]; ring
    _ ≤ Real.exp (-β * ((3 / 4 : ℝ) * (w : ℝ) - 5 - δ)) *
        ∑ ω ∈ Finset.univ.filter (fun ω : ManyBodyConfig Site => σ_eig ω = σ_ext),
          Real.exp (-β * E_eig ω) :=
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum h_lower_ext) (le_of_lt (Real.exp_pos _))

end PerturbedThermalBarrier

end
