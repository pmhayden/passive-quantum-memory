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

import Proofs.DressedSyndromeGibbs.DressedSyndromeCollarTelescoping

open scoped Classical InnerProduct ComplexConjugate BigOperators
open Filter Topology Asymptotics ContinuousLinearMap KMSPinchedGibbs

noncomputable section

/-!
# Dressed Syndrome Ket-Bra Decomposition and Individual Sector Gibbs Bounds

Expands QAC-dressed syndrome projectors into orthonormal ket-bra sums (`indexedDressedSyndromeProjector_eq_sum_ketBra`), evaluates Boltzmann traces on dressed syndrome projectors (`hilbertTrace_gibbsBoltzmannOp_mul_indexedDressedSyndromeProjector`), and bounds individual dressed Gibbs syndrome sectors (`indexed_dressed_gibbs_sector_bound`).

## References

* Part II, Section 3.3 (`subsec:walsh-coset-peeling`), Lemma 3.7 (`lem:peierls-bogoliubov`)
* Part II, Section 5.2 (`subsec:low-temp-crossover`), Proposition 5.2 (`prop:bhm-relative-form-bound`)
* Part II, Section 5.2 (`subsec:low-temp-crossover`), Theorem 5.3 (`thm:low-temperature-window-and-crossover`)
-/

namespace PerturbedThermalBarrier

/-! ## 1. Sector Dimension Equality & Trace-Average Collar Comparison -/

/-- Norm of an eigenstate with unit rank-one trace: $\operatorname{Tr}(|\psi\rangle\langle\psi|) = 1 \implies \|\psi\| = 1$. -/
lemma norm_eq_one_of_hilbertTrace_rankOneKetBra {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    {ψ : ManyBodyHilbertSpace Site}
    (h_tr : hilbertTrace (rankOneKetBra ψ) = 1) :
    ‖ψ‖ = 1 := by
  have h1 := hilbertTrace_mul_rankOneKetBra
    (1 : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site) ψ
  rw [one_mul, ContinuousLinearMap.one_apply, inner_self_eq_norm_sq] at h1
  have h_sq : ‖ψ‖ ^ 2 = 1 := h1.symm.trans h_tr
  nlinarith [norm_nonneg ψ]

/-- Linearity of `hilbertTrace` over subtraction. -/
lemma hilbertTrace_sub {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    (A B : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site) :
    hilbertTrace (A - B) = hilbertTrace A - hilbertTrace B := by
  unfold hilbertTrace
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun ψ _ => ?_
  rw [ContinuousLinearMap.sub_apply, inner_sub_right, map_sub]

/-! ## 2. Indexed Weyl–Peierls Sector Trace Inequality (`indexed_dressed_gibbs_sector_bound`) -/

lemma isSelfAdjoint_indexedDressedSyndromeProjector {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (sys : IndexedCommutingProjectorHamiltonian D L Site ι)
    (U : unitary (ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site)) (σ : ι → Bool) :
    IsSelfAdjoint (indexedDressedSyndromeProjector sys U σ) :=
  ((indexed_dressed_syndrome_resolution sys U).2.2.2.1 σ).isSelfAdjoint

/-- Decomposition of `indexedDressedSyndromeProjector sys U σ` into rank-one eigenstate projectors. -/
lemma indexedDressedSyndromeProjector_eq_sum_ketBra {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (sys : IndexedCommutingProjectorHamiltonian D L Site ι)
    (U : unitary (ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site))
    (ψ_eig : ManyBodyConfig Site → ManyBodyHilbertSpace Site)
    (σ_eig : ManyBodyConfig Site → (ι → Bool))
    (h_id : (∑ ω : ManyBodyConfig Site, rankOneKetBra (ψ_eig ω)) = 1)
    (h_eig_proj : ∀ ω : ManyBodyConfig Site,
      indexedDressedSyndromeProjector sys U (σ_eig ω) (ψ_eig ω) = ψ_eig ω ∧
      hilbertTrace (rankOneKetBra (ψ_eig ω)) = 1)
    (σ : ι → Bool) :
    indexedDressedSyndromeProjector sys U σ =
      ∑ ω ∈ Finset.univ.filter (fun ω : ManyBodyConfig Site => σ_eig ω = σ),
        rankOneKetBra (ψ_eig ω) := by
  have h_res := indexed_dressed_syndrome_resolution sys U
  have hP_sa := isSelfAdjoint_indexedDressedSyndromeProjector sys U σ
  calc indexedDressedSyndromeProjector sys U σ
    _ = (∑ ω : ManyBodyConfig Site, rankOneKetBra (ψ_eig ω)) *
          indexedDressedSyndromeProjector sys U σ := by rw [h_id, one_mul]
    _ = ∑ ω : ManyBodyConfig Site,
          rankOneKetBra (ψ_eig ω) * indexedDressedSyndromeProjector sys U σ := Finset.sum_mul _ _ _
    _ = ∑ ω ∈ Finset.univ.filter (fun ω : ManyBodyConfig Site => σ_eig ω = σ),
          rankOneKetBra (ψ_eig ω) := by
      rw [Finset.sum_filter]
      refine Finset.sum_congr rfl fun ω _ => ?_
      by_cases h_eq : σ_eig ω = σ
      · subst h_eq; rw [if_pos rfl, rankOneKetBra_mul_eq_self_of_isSelfAdjoint hP_sa (h_eig_proj ω).1]
      · have h_orth : indexedDressedSyndromeProjector sys U σ (ψ_eig ω) = 0 := by
          rw [← (h_eig_proj ω).1]
          change (indexedDressedSyndromeProjector sys U σ *
            indexedDressedSyndromeProjector sys U (σ_eig ω)) (ψ_eig ω) = 0
          rw [h_res.2.2.2.2.1 σ (σ_eig ω) (Ne.symm h_eq), ContinuousLinearMap.zero_apply]
        rw [if_neg h_eq, rankOneKetBra_mul_eq_zero_of_isSelfAdjoint hP_sa h_orth]

/-- Trace of the unnormalized Boltzmann operator against `indexedDressedSyndromeProjector sys U σ`. -/
lemma hilbertTrace_gibbsBoltzmannOp_mul_indexedDressedSyndromeProjector {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (sys : IndexedCommutingProjectorHamiltonian D L Site ι)
    (U : unitary (ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site))
    (ψ_eig : ManyBodyConfig Site → ManyBodyHilbertSpace Site)
    (σ_eig : ManyBodyConfig Site → (ι → Bool))
    (E_eig : ManyBodyConfig Site → ℝ) (β : ℝ)
    (h_eig_proj : ∀ ω : ManyBodyConfig Site,
      indexedDressedSyndromeProjector sys U (σ_eig ω) (ψ_eig ω) = ψ_eig ω ∧
      hilbertTrace (rankOneKetBra (ψ_eig ω)) = 1)
    (σ : ι → Bool) :
    hilbertTrace (gibbsBoltzmannOp ψ_eig E_eig β * indexedDressedSyndromeProjector sys U σ) =
      ∑ ω ∈ Finset.univ.filter (fun ω : ManyBodyConfig Site => σ_eig ω = σ),
        Real.exp (-β * E_eig ω) := by
  have h_res := indexed_dressed_syndrome_resolution sys U
  have hP_sa := isSelfAdjoint_indexedDressedSyndromeProjector sys U σ
  unfold gibbsBoltzmannOp
  rw [Finset.sum_mul, hilbertTrace_sum, Finset.sum_filter]
  refine Finset.sum_congr rfl fun ω _ => ?_
  rw [clm_smul_mul, hilbertTrace_smul_ofReal]
  by_cases h_eq : σ_eig ω = σ
  · subst h_eq
    rw [if_pos rfl, rankOneKetBra_mul_eq_self_of_isSelfAdjoint hP_sa (h_eig_proj ω).1,
      (h_eig_proj ω).2, mul_one]
  · have h_orth : indexedDressedSyndromeProjector sys U σ (ψ_eig ω) = 0 := by
      rw [← (h_eig_proj ω).1]
      change (indexedDressedSyndromeProjector sys U σ *
        indexedDressedSyndromeProjector sys U (σ_eig ω)) (ψ_eig ω) = 0
      rw [h_res.2.2.2.2.1 σ (σ_eig ω) (Ne.symm h_eq), ContinuousLinearMap.zero_apply]
    rw [if_neg h_eq, rankOneKetBra_mul_eq_zero_of_isSelfAdjoint hP_sa h_orth,
      hilbertTrace_zero, mul_zero]

/-- **Indexed Weyl–Peierls Sector Trace Inequality (`indexed_dressed_gibbs_sector_bound`)**:
    Under `SatisfiesDressedEnergySandwich sys V U c_shift δ_split`, every excited syndrome $\sigma \ne 0$ satisfies:
    $\operatorname{Tr}(\exp(-\beta H) \widetilde{\Pi}_\sigma) \le
      \exp(-\beta c_{\mathrm{shift}} + \tfrac{1}{2}\beta \delta_{\mathrm{split}} - \tfrac{3}{4}\beta E_{\mathrm{syn}}(\sigma))
      \operatorname{Tr}(\Pi_\sigma)$. -/
theorem indexed_dressed_gibbs_sector_bound {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (sys : IndexedCommutingProjectorHamiltonian D L Site ι)
    (V : QuasiLocalPerturbation D L Site)
    (U : unitary (ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site))
    {c_shift δ_split : ℝ}
    (h_sand : SatisfiesDressedEnergySandwich sys V U c_shift δ_split)
    (ψ_eig : ManyBodyConfig Site → ManyBodyHilbertSpace Site)
    (σ_eig : ManyBodyConfig Site → (ι → Bool))
    (E_eig : ManyBodyConfig Site → ℝ)
    (h_id : (∑ ω : ManyBodyConfig Site, rankOneKetBra (ψ_eig ω)) = 1)
    (h_eig_H : ∀ ω : ManyBodyConfig Site,
      (sys.H0 + V.totalPerturbation) (ψ_eig ω) = (E_eig ω : ℂ) • ψ_eig ω)
    (h_eig_proj : ∀ ω : ManyBodyConfig Site,
      indexedDressedSyndromeProjector sys U (σ_eig ω) (ψ_eig ω) = ψ_eig ω ∧
      hilbertTrace (rankOneKetBra (ψ_eig ω)) = 1)
    {σ : ι → Bool} (hσ_ne : σ ≠ (fun _ => false)) {β : ℝ} (hβ : 0 ≤ β) :
    hilbertTrace (gibbsBoltzmannOp ψ_eig E_eig β * indexedDressedSyndromeProjector sys U σ) ≤
      Real.exp (-β * c_shift + (1 / 2 : ℝ) * β * δ_split - (3 / 4 : ℝ) * β * sys.syndromeEnergy σ) *
        hilbertTrace (sys.syndromeProjector σ) := by
  have h_res := indexed_dressed_syndrome_resolution sys U
  rw [hilbertTrace_gibbsBoltzmannOp_mul_indexedDressedSyndromeProjector sys U ψ_eig σ_eig E_eig β
    h_eig_proj σ]
  have h_card : hilbertTrace (sys.syndromeProjector σ) =
      ((Finset.univ.filter (fun ω : ManyBodyConfig Site => σ_eig ω = σ)).card : ℝ) := by
    rw [← h_res.2.2.2.2.2.2.2 σ,
      indexedDressedSyndromeProjector_eq_sum_ketBra sys U ψ_eig σ_eig h_id h_eig_proj σ,
      hilbertTrace_sum]
    have h_one : ∀ ω ∈ Finset.univ.filter (fun ω : ManyBodyConfig Site => σ_eig ω = σ),
        hilbertTrace (rankOneKetBra (ψ_eig ω)) = (1 : ℝ) := fun ω _ => (h_eig_proj ω).2
    rw [Finset.sum_congr rfl h_one, Finset.sum_const, nsmul_eq_mul, mul_one]
  have h_term : ∀ ω ∈ Finset.univ.filter (fun ω : ManyBodyConfig Site => σ_eig ω = σ),
      Real.exp (-β * E_eig ω) ≤
        Real.exp (-β * c_shift + (1 / 2 : ℝ) * β * δ_split -
          (3 / 4 : ℝ) * β * sys.syndromeEnergy σ) := by
    intro ω hω
    have hϕ : indexedDressedSyndromeProjector sys U σ (ψ_eig ω) = ψ_eig ω := by
      rw [← (Finset.mem_filter.mp hω).2]; exact (h_eig_proj ω).1
    have h_norm : ‖ψ_eig ω‖ = 1 := norm_eq_one_of_hilbertTrace_rankOneKetBra (h_eig_proj ω).2
    have h_sec := (dressed_sector_energy_sandwich_of_ne_zero sys V U h_sand hσ_ne hϕ).2.2.1
    have h_re_H : RCLike.re (inner ℂ (ψ_eig ω) ((sys.H0 + V.totalPerturbation - (c_shift : ℂ) • 1) (ψ_eig ω))) =
        E_eig ω - c_shift := by
      rw [ContinuousLinearMap.sub_apply, h_eig_H ω, ContinuousLinearMap.smul_apply,
        ContinuousLinearMap.one_apply, inner_sub_right, map_sub, inner_smul_right, inner_smul_right,
        re_ofReal_mul, re_ofReal_mul, inner_self_eq_norm_sq, h_norm, one_pow, mul_one, mul_one]
    rw [h_re_H, h_norm, one_pow, mul_one] at h_sec
    exact Real.exp_le_exp.mpr (by nlinarith)
  calc ∑ ω ∈ Finset.univ.filter (fun ω : ManyBodyConfig Site => σ_eig ω = σ),
        Real.exp (-β * E_eig ω)
    _ ≤ ∑ _ω ∈ Finset.univ.filter (fun ω : ManyBodyConfig Site => σ_eig ω = σ),
        Real.exp (-β * c_shift + (1 / 2 : ℝ) * β * δ_split -
          (3 / 4 : ℝ) * β * sys.syndromeEnergy σ) := Finset.sum_le_sum h_term
    _ = Real.exp (-β * c_shift + (1 / 2 : ℝ) * β * δ_split -
          (3 / 4 : ℝ) * β * sys.syndromeEnergy σ) *
        hilbertTrace (sys.syndromeProjector σ) := by
      rw [h_card, Finset.sum_const, nsmul_eq_mul, mul_comm]

end PerturbedThermalBarrier

end
