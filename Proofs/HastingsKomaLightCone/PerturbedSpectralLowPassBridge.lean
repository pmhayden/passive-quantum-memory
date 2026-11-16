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

import Proofs.HastingsKomaLightCone.BandLimitedFilterWeightExists

open scoped Classical InnerProduct ComplexConjugate BigOperators
open Filter Topology Asymptotics ContinuousLinearMap MeasureTheory
open KMSPinchedGibbs PerturbedThermalBarrier WeldedHierarchy WeldedHierarchy.BDLDecoder
open InhomogeneousMemoryChallenge

noncomputable section

set_option maxRecDepth 200000
set_option maxHeartbeats 800000

/-!
# Perturbed Ground-Space Spectral Projector and Low-Pass Annihilation

Constructs orthonormal eigenbasis rank-one projectors `rankOneEigenvectorProj` (`hamiltonian_mul_rankOneEigenvectorProj`) and the exact perturbed low-energy spectral projector `perturbedGroundSpectralProj`. Proves self-adjoint idempotence, Hamiltonian commutation, unperturbed agreement at zero coupling, and exact off-diagonal annihilation of `bochnerFilteredOp` whenever the perturbed spectral gap is at least one-half.

## References

* Part I, Section 6.2 (`subsec:bochner-lr`), Equation (67) (`eq:wBP-fourier-props`)
* Part I, Section 6.3 (`subsec:qac-block-diag`), Proposition 6.4 (`prop:qac-block-diagonalization`), Equation (77) (`eq:rotated-H-block-decomp`)
* Bravyi–Hastings (2011), Communications in Mathematical Physics 307, 609–627
-/

/-! ## 1. Rank-One Eigenprojectors & Spectral Band Sums -/

/-- Rank-one orthogonal projection $|\psi_i\rangle\langle\psi_i|$ onto the $i$-th eigenvector
    of `sortedEigenbasis H hH`. -/
def rankOneEigenvectorProj {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    (H : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site)
    (hH : IsSelfAdjoint H)
    (i : Fin (Module.finrank ℂ (ManyBodyHilbertSpace Site))) :
    ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site :=
  rankOneKetBra (sortedEigenbasis H hH i)

/-- Action of `rankOneEigenvectorProj H hH i` on a basis state `sortedEigenbasis H hH j`. -/
lemma rankOneEigenvectorProj_apply_eigenbasis {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    (H : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site)
    (hH : IsSelfAdjoint H)
    (i j : Fin (Module.finrank ℂ (ManyBodyHilbertSpace Site))) :
    rankOneEigenvectorProj H hH i (sortedEigenbasis H hH j) =
      if i = j then sortedEigenbasis H hH j else 0 := by
  let b := sortedEigenbasis H hH
  dsimp [rankOneEigenvectorProj]
  rw [rankOneKetBra_apply]
  split_ifs with hij
  · subst hij; rw [b.inner_eq_one, one_smul]
  · rw [b.inner_eq_zero hij, zero_smul]

/-- Action of a finite spectral sum $\sum_{i \in S} |\psi_i\rangle\langle\psi_i|$ on
    `sortedEigenbasis H hH j`. -/
lemma sum_rankOneEigenvectorProj_apply_eigenbasis {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    (H : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site)
    (hH : IsSelfAdjoint H)
    (S : Finset (Fin (Module.finrank ℂ (ManyBodyHilbertSpace Site))))
    (j : Fin (Module.finrank ℂ (ManyBodyHilbertSpace Site))) :
    (∑ i ∈ S, rankOneEigenvectorProj H hH i) (sortedEigenbasis H hH j) =
      if j ∈ S then sortedEigenbasis H hH j else 0 := by
  rw [ContinuousLinearMap.sum_apply]
  split_ifs with hj
  · rw [Finset.sum_eq_single j]
    · rw [rankOneEigenvectorProj_apply_eigenbasis, if_pos rfl]
    · intro i _ hij
      rw [rankOneEigenvectorProj_apply_eigenbasis, if_neg hij]
    · intro hj_not; exact False.elim (hj_not hj)
  · refine Finset.sum_eq_zero fun i hi => ?_
    have hij : i ≠ j := fun h => hj (h ▸ hi)
    rw [rankOneEigenvectorProj_apply_eigenbasis, if_neg hij]

/-- Resolution of the identity $\sum_i |\psi_i\rangle\langle\psi_i| = 1$. -/
theorem sum_rankOneEigenvectorProj_eq_one {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    (H : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site)
    (hH : IsSelfAdjoint H) :
    (∑ i : Fin (Module.finrank ℂ (ManyBodyHilbertSpace Site)),
      rankOneEigenvectorProj H hH i) = 1 := by
  apply ext_of_orthonormalBasis_eq (sortedEigenbasis H hH)
  intro j
  rw [sum_rankOneEigenvectorProj_apply_eigenbasis, if_pos (Finset.mem_univ j),
    ContinuousLinearMap.one_apply]

/-- Any spectral sub-band sum $\sum_{i \in S} |\psi_i\rangle\langle\psi_i|$ is an orthogonal
    star projection. -/
theorem isStarProjection_sum_rankOneEigenvectorProj {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    (H : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site)
    (hH : IsSelfAdjoint H)
    (S : Finset (Fin (Module.finrank ℂ (ManyBodyHilbertSpace Site)))) :
    IsStarProjection (∑ i ∈ S, rankOneEigenvectorProj H hH i) := by
  refine ⟨?_, ?_⟩
  · rw [IsIdempotentElem]
    apply ext_of_orthonormalBasis_eq (sortedEigenbasis H hH)
    intro j
    rw [ContinuousLinearMap.mul_apply, sum_rankOneEigenvectorProj_apply_eigenbasis]
    split_ifs with hj
    · rw [sum_rankOneEigenvectorProj_apply_eigenbasis, if_pos hj]
    · rw [map_zero]
  · exact isSelfAdjoint_finset_sum S _
      (fun i _ => isSelfAdjoint_rankOneKetBra (sortedEigenbasis H hH i))

/-- Left eigenoperator identity $H |\psi_i\rangle\langle\psi_i| = \lambda_i |\psi_i\rangle\langle\psi_i|$. -/
theorem hamiltonian_mul_rankOneEigenvectorProj {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    (H : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site)
    (hH : IsSelfAdjoint H)
    (i : Fin (Module.finrank ℂ (ManyBodyHilbertSpace Site))) :
    H * rankOneEigenvectorProj H hH i =
      (sortedEigenvalues H hH i : ℂ) • rankOneEigenvectorProj H hH i := by
  apply ContinuousLinearMap.ext
  intro ψ
  dsimp only [rankOneEigenvectorProj]
  rw [ContinuousLinearMap.mul_apply, ContinuousLinearMap.smul_apply,
    rankOneKetBra_apply, map_smul, sortedEigenbasis_apply_H_bhm H hH i, smul_comm]

/-- Right eigenoperator identity $|\psi_i\rangle\langle\psi_i| H = \lambda_i |\psi_i\rangle\langle\psi_i|$. -/
theorem rankOneEigenvectorProj_mul_H {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    (H : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site)
    (hH : IsSelfAdjoint H)
    (i : Fin (Module.finrank ℂ (ManyBodyHilbertSpace Site))) :
    rankOneEigenvectorProj H hH i * H =
      (sortedEigenvalues H hH i : ℂ) • rankOneEigenvectorProj H hH i := by
  apply ContinuousLinearMap.ext
  intro ψ
  dsimp only [rankOneEigenvectorProj]
  rw [ContinuousLinearMap.mul_apply, ContinuousLinearMap.smul_apply,
    rankOneKetBra_apply, rankOneKetBra_apply, sortedEigenbasis_inner_apply_H H hH i ψ,
    mul_smul]

/-- Any spectral sub-band sum $\sum_{i \in S} |\psi_i\rangle\langle\psi_i|$ commutes with $H$. -/
theorem commute_H_sum_rankOneEigenvectorProj {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    (H : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site)
    (hH : IsSelfAdjoint H)
    (S : Finset (Fin (Module.finrank ℂ (ManyBodyHilbertSpace Site)))) :
    Commute H (∑ i ∈ S, rankOneEigenvectorProj H hH i) := by
  rw [commute_iff_eq, Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [hamiltonian_mul_rankOneEigenvectorProj, rankOneEigenvectorProj_mul_H]

/-! ## 2. Perturbed Low-Energy Spectral Projector `perturbedGroundSpectralProj` -/

/-- Index finset $\{i \mid i < d_{\mathrm{gs}}\}$ of the lowest `sys.groundDegeneracy` eigenvalues. -/
def groundBandFinset {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (sys : IndexedCommutingProjectorHamiltonian D L Site ι) :
    Finset (Fin (Module.finrank ℂ (ManyBodyHilbertSpace Site))) :=
  Finset.univ.filter (fun i => i.1 < sys.groundDegeneracy)

/-- Index finset $\{j \mid d_{\mathrm{gs}} \le j\}$ of the excited eigenvalues. -/
def excitedBandFinset {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (sys : IndexedCommutingProjectorHamiltonian D L Site ι) :
    Finset (Fin (Module.finrank ℂ (ManyBodyHilbertSpace Site))) :=
  Finset.univ.filter (fun j => sys.groundDegeneracy ≤ j.1)

/-- **Perturbed Ground-Band Spectral Projector (`perturbedGroundSpectralProj`)**:
    Projects onto the span of the first `sys.groundDegeneracy` eigenvectors of
    $H_s = H_0 + (s V)_{\mathrm{tot}}$ in `sortedEigenbasis`. -/
def perturbedGroundSpectralProj {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (sys : IndexedCommutingProjectorHamiltonian D L Site ι)
    (V : QuasiLocalPerturbation D L Site) (s : ℝ) :
    ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site :=
  let H_s := sys.H0 + (scaleQuasiLocalPerturbation s V).totalPerturbation
  let hHs := isSelfAdjoint_indexedH0_add_V_tot_bhm sys (scaleQuasiLocalPerturbation s V)
  ∑ i ∈ groundBandFinset sys, rankOneEigenvectorProj H_s hHs i

/-- `perturbedGroundSpectralProj sys V s` is a star projection. -/
theorem isStarProjection_perturbedGroundSpectralProj {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (sys : IndexedCommutingProjectorHamiltonian D L Site ι)
    (V : QuasiLocalPerturbation D L Site) (s : ℝ) :
    IsStarProjection (perturbedGroundSpectralProj sys V s) :=
  isStarProjection_sum_rankOneEigenvectorProj _ _ (groundBandFinset sys)

/-- `H_s = sys.H0 + (scaleQuasiLocalPerturbation s V).V_tot` commutes with
    `perturbedGroundSpectralProj sys V s`. -/
theorem commute_perturbedGroundSpectralProj {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (sys : IndexedCommutingProjectorHamiltonian D L Site ι)
    (V : QuasiLocalPerturbation D L Site) (s : ℝ) :
    Commute (sys.H0 + (scaleQuasiLocalPerturbation s V).totalPerturbation)
      (perturbedGroundSpectralProj sys V s) :=
  commute_H_sum_rankOneEigenvectorProj _ _ (groundBandFinset sys)

/-- Complementary excited-band expansion:
    `1 - perturbedGroundSpectralProj sys V s = ∑ j ∈ excitedBandFinset sys, rankOneEigenvectorProj H_s hHs j`. -/
theorem one_sub_perturbedGroundSpectralProj_eq_sum_excitedBandFinset {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (sys : IndexedCommutingProjectorHamiltonian D L Site ι)
    (V : QuasiLocalPerturbation D L Site) (s : ℝ) :
    let H_s := sys.H0 + (scaleQuasiLocalPerturbation s V).totalPerturbation
    let hHs := isSelfAdjoint_indexedH0_add_V_tot_bhm sys (scaleQuasiLocalPerturbation s V)
    1 - perturbedGroundSpectralProj sys V s =
      ∑ j ∈ excitedBandFinset sys, rankOneEigenvectorProj H_s hHs j := by
  intro H_s hHs
  apply ext_of_orthonormalBasis_eq (sortedEigenbasis H_s hHs)
  intro k
  rw [ContinuousLinearMap.sub_apply, ContinuousLinearMap.one_apply]
  dsimp only [perturbedGroundSpectralProj]
  rw [sum_rankOneEigenvectorProj_apply_eigenbasis,
    sum_rankOneEigenvectorProj_apply_eigenbasis]
  simp only [groundBandFinset, excitedBandFinset, Finset.mem_filter, Finset.mem_univ, true_and]
  by_cases hk : k.1 < sys.groundDegeneracy
  · have h_not_le : ¬ sys.groundDegeneracy ≤ k.1 := not_le.mpr hk
    rw [if_pos hk, if_neg h_not_le, sub_self]
  · have h_le : sys.groundDegeneracy ≤ k.1 := not_lt.mp hk
    rw [if_neg hk, if_pos h_le, sub_zero]

/-- At $s = 0$, the perturbed low-energy spectral projector equals `sys.P0`. -/
theorem perturbedGroundSpectralProj_zero_eq_P0 {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (sys : IndexedCommutingProjectorHamiltonian D L Site ι)
    (V : QuasiLocalPerturbation D L Site) :
    perturbedGroundSpectralProj sys V 0 = sys.P0 := by
  have h_H0 : sys.H0 + (scaleQuasiLocalPerturbation 0 V).totalPerturbation = sys.H0 := by
    rw [scaleQuasiLocalPerturbation_zero_V_tot, add_zero]
  have h_sum_eq :
      perturbedGroundSpectralProj sys V 0 =
        ∑ i ∈ groundBandFinset sys,
          rankOneEigenvectorProj sys.H0 sys.isSelfAdjoint_H0 i := by
    unfold perturbedGroundSpectralProj
    (try dsimp only)
    congr 1; funext i; congr 1
  rw [h_sum_eq]
  let b0 := sortedEigenbasis sys.H0 sys.isSelfAdjoint_H0
  rcases sys.sortedEigenbasis_H0_properties sys.weight_ge_one with ⟨_, h_low, h_high⟩
  apply ext_of_orthonormalBasis_eq b0
  intro j
  rw [sum_rankOneEigenvectorProj_apply_eigenbasis]
  simp only [groundBandFinset, Finset.mem_filter, Finset.mem_univ, true_and]
  by_cases hj : j.1 < sys.groundDegeneracy
  · rw [if_pos hj, (h_low j hj).2]
  · rw [if_neg hj, (h_high j (not_lt.mp hj)).2]

/-- Conjugation relationship between `perturbedGroundSpectralProj sys V s` and `sys.P0` via
    `spectralAlignmentUnitary sys (scaleQuasiLocalPerturbation s V)`. -/
theorem perturbedGroundSpectralProj_eq_spectralAlignmentUnitary_conj_P0 {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (sys : IndexedCommutingProjectorHamiltonian D L Site ι)
    (V : QuasiLocalPerturbation D L Site) (s : ℝ) :
    let V_s := scaleQuasiLocalPerturbation s V
    let U_spec := spectralAlignmentUnitary sys V_s
    perturbedGroundSpectralProj sys V s = U_spec.1 * sys.P0 * U_spec.1† ∧
    U_spec.1† * perturbedGroundSpectralProj sys V s * U_spec.1 = sys.P0 := by
  intro V_s U_spec
  let H_s := sys.H0 + V_s.totalPerturbation
  let hHs := isSelfAdjoint_indexedH0_add_V_tot_bhm sys V_s
  let b0 := sortedEigenbasis sys.H0 sys.isSelfAdjoint_H0
  let bH := sortedEigenbasis H_s hHs
  rcases sys.sortedEigenbasis_H0_properties sys.weight_ge_one with ⟨_, h_low, h_high⟩
  have h1 : perturbedGroundSpectralProj sys V s = U_spec.1 * sys.P0 * U_spec.1† := by
    apply ext_of_orthonormalBasis_eq bH
    intro j
    dsimp [perturbedGroundSpectralProj]
    rw [sum_rankOneEigenvectorProj_apply_eigenbasis]
    change (if j ∈ groundBandFinset sys then bH j else 0) =
      (orthonormalBasisIntertwiner b0 bH).1
        (sys.P0 (((orthonormalBasisIntertwiner b0 bH).1†) (bH j)))
    rw [orthonormalBasisIntertwiner_adj_apply b0 bH j]
    simp only [groundBandFinset, Finset.mem_filter, Finset.mem_univ, true_and]
    by_cases hj : j.1 < sys.groundDegeneracy
    · rw [if_pos hj, (h_low j hj).2, orthonormalBasisIntertwiner_apply b0 bH j]
    · rw [if_neg hj, (h_high j (not_lt.mp hj)).2, map_zero]
  refine ⟨h1, ?_⟩
  have h_u_adj : U_spec.1† * U_spec.1 = 1 := Unitary.coe_star_mul_self U_spec
  rw [h1]
  calc U_spec.1† * (U_spec.1 * sys.P0 * U_spec.1†) * U_spec.1
    _ = (U_spec.1† * U_spec.1) * sys.P0 * (U_spec.1† * U_spec.1) := by noncomm_ring
    _ = 1 * sys.P0 * 1 := by rw [h_u_adj]
    _ = sys.P0 := by rw [one_mul, mul_one]

/-! ## 3. Exact Off-Diagonal Bandpass Annihilation -/

/-- Pointwise-in-$t$ evaluation of $Q_L (\mathrm{heisenbergFlow}\ H'\ t\ X) Q_R$ when
    $Q_L H' = E_L Q_L$ and $H' Q_R = E_R Q_R$. -/
lemma eigenproj_mul_heisenbergFlow_mul_eigenproj {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    {H' Q_L Q_R : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site}
    {E_L E_R : ℝ}
    (hQL : Q_L * H' = (E_L : ℂ) • Q_L)
    (hQR : H' * Q_R = (E_R : ℂ) • Q_R)
    (X : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site) (t : ℝ) :
    Q_L * heisenbergFlow H' t X * Q_R =
      Complex.exp (Complex.I * ((E_L - E_R : ℝ) : ℂ) * (t : ℂ)) • (Q_L * X * Q_R) := by
  have hL_U : Q_L * timeEvolutionOp H' t =
      NormedSpace.exp (((Complex.I * (t : ℂ)) * (E_L : ℂ)) •
        (1 : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site)) * Q_L := by
    change Q_L * NormedSpace.exp ((Complex.I * (t : ℂ)) • H') = _
    rw [clm_proj_mul_exp_smul hQL (Complex.I * (t : ℂ)),
      (commute_exp_smul_one ((Complex.I * (t : ℂ)) * (E_L : ℂ)) Q_L).eq]
  have hU_R : timeEvolutionOp H' (-t) * Q_R =
      Q_R * NormedSpace.exp (((-(Complex.I * (t : ℂ))) * (E_R : ℂ)) •
        (1 : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site)) := by
    rw [timeEvolutionOp_neg_eq, clm_exp_smul_mul_proj hQR (-(Complex.I * (t : ℂ))),
      (commute_exp_smul_one ((-(Complex.I * (t : ℂ))) * (E_R : ℂ)) Q_R).eq]
  dsimp [heisenbergFlow]
  rw [monoid_sandwich_rew hL_U hU_R, clm_exp_smul_one, clm_exp_smul_one,
    clm_smul_one_sandwich, ← Complex.exp_add]
  have h_exp :
      (Complex.I * (t : ℂ)) * (E_L : ℂ) + (-(Complex.I * (t : ℂ))) * (E_R : ℂ) =
        Complex.I * ((E_L - E_R : ℝ) : ℂ) * (t : ℂ) := by
    push_cast; ring
  rw [h_exp]

/-- For any pair of eigenprojectors $Q_L, Q_R$ of $H'$ with $|E_L - E_R| \ge 1/2$, any integrable
    weight $w_{\mathrm{BL}}$ whose Fourier transform vanishes for $|\omega| \ge 1/2$ annihilates
    the $(Q_L, Q_R)$ block of `bochnerFilteredOp H' w_BL X`. -/
theorem eigenproj_mul_bochnerFilteredOp_mul_eigenproj_eq_zero {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    {H' Q_L Q_R : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site}
    {E_L E_R : ℝ} {w_BL : ℝ → ℂ}
    (hH' : IsSelfAdjoint H')
    (hw_int : Integrable w_BL)
    (hw_zero : ∀ ω : ℝ, (1 / 2 : ℝ) ≤ |ω| →
      (∫ t : ℝ, w_BL t * Complex.exp (Complex.I * (ω : ℂ) * (t : ℂ))) = 0)
    (hQL : Q_L * H' = (E_L : ℂ) • Q_L)
    (hQR : H' * Q_R = (E_R : ℂ) • Q_R)
    (h_gap : (1 / 2 : ℝ) ≤ |E_L - E_R|)
    (X : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site) :
    Q_L * bochnerFilteredOp H' w_BL X * Q_R = 0 := by
  unfold bochnerFilteredOp
  rw [clm_sandwich_integral_smul Q_L Q_R w_BL (fun t => heisenbergFlow H' t X)
    (integrable_smul_heisenbergFlow_of_integrable hH' hw_int X)]
  have h_pt : (fun t : ℝ => w_BL t • (Q_L * heisenbergFlow H' t X * Q_R)) =
      (fun t : ℝ =>
        (w_BL t * Complex.exp (Complex.I * ((E_L - E_R : ℝ) : ℂ) * (t : ℂ))) •
          (Q_L * X * Q_R)) := by
    funext t
    rw [eigenproj_mul_heisenbergFlow_mul_eigenproj hQL hQR X t, smul_smul]
  rw [h_pt, integral_smul_const, hw_zero (E_L - E_R) h_gap, zero_smul]

/-- Whenever `bhmPerturbedGap ≤ indexedSpectralGap sys V s`, every ground-band index
    `i ∈ groundBandFinset sys` and excited-band index `j ∈ excitedBandFinset sys` satisfy
    `(1 / 2 : ℝ) ≤ |λ_i(H_s) - λ_j(H_s)|` and `(1 / 2 : ℝ) ≤ |λ_j(H_s) - λ_i(H_s)|`. -/
lemma half_le_abs_sortedEigenvalues_sub_of_bhmPerturbedGap_le {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (sys : IndexedCommutingProjectorHamiltonian D L Site ι)
    (V : QuasiLocalPerturbation D L Site) (s : ℝ)
    (h_gap : bhmPerturbedGap ≤ indexedSpectralGap sys V s)
    {i j : Fin (Module.finrank ℂ (ManyBodyHilbertSpace Site))}
    (hi : i ∈ groundBandFinset sys) (hj : j ∈ excitedBandFinset sys) :
    let H_s := sys.H0 + (scaleQuasiLocalPerturbation s V).totalPerturbation
    let hHs := isSelfAdjoint_indexedH0_add_V_tot_bhm sys (scaleQuasiLocalPerturbation s V)
    (1 / 2 : ℝ) ≤ |sortedEigenvalues H_s hHs i - sortedEigenvalues H_s hHs j| ∧
    (1 / 2 : ℝ) ≤ |sortedEigenvalues H_s hHs j - sortedEigenvalues H_s hHs i| := by
  intro H_s hHs
  have hi_lt : i.1 < sys.groundDegeneracy := (Finset.mem_filter.mp hi).2
  have hj_ge : sys.groundDegeneracy ≤ j.1 := (Finset.mem_filter.mp hj).2
  have h_le_ij := le_trans h_gap (indexedSpectralGap_le_indexedEigenvalueGap sys V hi_lt hj_ge s)
  dsimp [indexedEigenvalueGap, bhmPerturbedGap] at h_le_ij
  have h_ji : (1 / 2 : ℝ) ≤ |sortedEigenvalues H_s hHs j - sortedEigenvalues H_s hHs i| :=
    le_trans h_le_ij (le_abs_self _)
  have h_ij : (1 / 2 : ℝ) ≤ |sortedEigenvalues H_s hHs i - sortedEigenvalues H_s hHs j| := by
    rw [abs_sub_comm]; exact h_ji
  exact ⟨h_ij, h_ji⟩

/-- Right off-diagonal block vanishing:
    `P_s * bochnerFilteredOp H_s w_BL X * (1 - P_s) = 0`. -/
theorem perturbedGroundSpectralProj_mul_bochnerFilteredOp_mul_one_sub_eq_zero {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (sys : IndexedCommutingProjectorHamiltonian D L Site ι)
    (V : QuasiLocalPerturbation D L Site) (s : ℝ)
    {w_BL : ℝ → ℂ} (hw_int : Integrable w_BL)
    (hw_zero : ∀ ω : ℝ, (1 / 2 : ℝ) ≤ |ω| →
      (∫ t : ℝ, w_BL t * Complex.exp (Complex.I * (ω : ℂ) * (t : ℂ))) = 0)
    (h_gap : bhmPerturbedGap ≤ indexedSpectralGap sys V s)
    (X : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site) :
    let P_s := perturbedGroundSpectralProj sys V s
    let H_s := sys.H0 + (scaleQuasiLocalPerturbation s V).totalPerturbation
    P_s * bochnerFilteredOp H_s w_BL X * (1 - P_s) = 0 := by
  intro P_s H_s
  let hHs := isSelfAdjoint_indexedH0_add_V_tot_bhm sys (scaleQuasiLocalPerturbation s V)
  rw [one_sub_perturbedGroundSpectralProj_eq_sum_excitedBandFinset sys V s]
  dsimp [P_s, perturbedGroundSpectralProj]
  rw [Finset.sum_mul, Finset.sum_mul]
  refine Finset.sum_eq_zero fun i hi => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_eq_zero fun j hj => ?_
  exact eigenproj_mul_bochnerFilteredOp_mul_eigenproj_eq_zero hHs hw_int hw_zero
    (rankOneEigenvectorProj_mul_H H_s hHs i)
    (hamiltonian_mul_rankOneEigenvectorProj H_s hHs j)
    (half_le_abs_sortedEigenvalues_sub_of_bhmPerturbedGap_le sys V s h_gap hi hj).1 X

/-- Left off-diagonal block vanishing:
    `(1 - P_s) * bochnerFilteredOp H_s w_BL X * P_s = 0`. -/
theorem one_sub_perturbedGroundSpectralProj_mul_bochnerFilteredOp_mul_eq_zero {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (sys : IndexedCommutingProjectorHamiltonian D L Site ι)
    (V : QuasiLocalPerturbation D L Site) (s : ℝ)
    {w_BL : ℝ → ℂ} (hw_int : Integrable w_BL)
    (hw_zero : ∀ ω : ℝ, (1 / 2 : ℝ) ≤ |ω| →
      (∫ t : ℝ, w_BL t * Complex.exp (Complex.I * (ω : ℂ) * (t : ℂ))) = 0)
    (h_gap : bhmPerturbedGap ≤ indexedSpectralGap sys V s)
    (X : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site) :
    let P_s := perturbedGroundSpectralProj sys V s
    let H_s := sys.H0 + (scaleQuasiLocalPerturbation s V).totalPerturbation
    (1 - P_s) * bochnerFilteredOp H_s w_BL X * P_s = 0 := by
  intro P_s H_s
  let hHs := isSelfAdjoint_indexedH0_add_V_tot_bhm sys (scaleQuasiLocalPerturbation s V)
  rw [one_sub_perturbedGroundSpectralProj_eq_sum_excitedBandFinset sys V s]
  dsimp [P_s, perturbedGroundSpectralProj]
  rw [Finset.sum_mul, Finset.sum_mul]
  refine Finset.sum_eq_zero fun j hj => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_eq_zero fun i hi => ?_
  exact eigenproj_mul_bochnerFilteredOp_mul_eigenproj_eq_zero hHs hw_int hw_zero
    (rankOneEigenvectorProj_mul_H H_s hHs j)
    (hamiltonian_mul_rankOneEigenvectorProj H_s hHs i)
    (half_le_abs_sortedEigenvalues_sub_of_bhmPerturbedGap_le sys V s h_gap hi hj).2 X

/-- **Exact Off-Diagonal Bandpass Annihilation
    (`twoBlockOffDiagProj_perturbedGroundSpectralProj_bochnerFilteredOp_eq_zero`)**:
    Whenever `bhmPerturbedGap ≤ indexedSpectralGap sys V s` and `w_BL : ℝ → ℂ` is integrable
    with Fourier transform vanishing for all `|ω| ≥ 1/2`, the off-diagonal block projection
    `twoBlockOffDiagProj (perturbedGroundSpectralProj sys V s) (bochnerFilteredOp H_s w_BL X)`
    vanishes identically (`= 0`) for every operator `X`. -/
theorem twoBlockOffDiagProj_perturbedGroundSpectralProj_bochnerFilteredOp_eq_zero {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (sys : IndexedCommutingProjectorHamiltonian D L Site ι)
    (V : QuasiLocalPerturbation D L Site) (s : ℝ)
    {w_BL : ℝ → ℂ} (hw_int : Integrable w_BL)
    (hw_zero : ∀ ω : ℝ, (1 / 2 : ℝ) ≤ |ω| →
      (∫ t : ℝ, w_BL t * Complex.exp (Complex.I * (ω : ℂ) * (t : ℂ))) = 0)
    (h_gap : bhmPerturbedGap ≤ indexedSpectralGap sys V s)
    (X : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site) :
    twoBlockOffDiagProj (perturbedGroundSpectralProj sys V s)
      (bochnerFilteredOp (sys.H0 + (scaleQuasiLocalPerturbation s V).totalPerturbation) w_BL X) = 0 := by
  unfold twoBlockOffDiagProj
  rw [perturbedGroundSpectralProj_mul_bochnerFilteredOp_mul_one_sub_eq_zero
      sys V s hw_int hw_zero h_gap X,
    one_sub_perturbedGroundSpectralProj_mul_bochnerFilteredOp_mul_eq_zero
      sys V s hw_int hw_zero h_gap X,
    add_zero]

/-- Exact block-commutation `Commute (bochnerFilteredOp H_s w_BL X) (perturbedGroundSpectralProj sys V s)`
    whenever `bhmPerturbedGap ≤ indexedSpectralGap sys V s` and `w_BL` is low-pass. -/
theorem commute_bochnerFilteredOp_perturbedGroundSpectralProj {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (sys : IndexedCommutingProjectorHamiltonian D L Site ι)
    (V : QuasiLocalPerturbation D L Site) (s : ℝ)
    {w_BL : ℝ → ℂ} (hw_int : Integrable w_BL)
    (hw_zero : ∀ ω : ℝ, (1 / 2 : ℝ) ≤ |ω| →
      (∫ t : ℝ, w_BL t * Complex.exp (Complex.I * (ω : ℂ) * (t : ℂ))) = 0)
    (h_gap : bhmPerturbedGap ≤ indexedSpectralGap sys V s)
    (X : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site) :
    Commute (bochnerFilteredOp (sys.H0 + (scaleQuasiLocalPerturbation s V).totalPerturbation) w_BL X)
      (perturbedGroundSpectralProj sys V s) :=
  (ring_spectral_decomp_of_offDiag_zero
    (isStarProjection_perturbedGroundSpectralProj sys V s).isIdempotentElem.eq
    (perturbedGroundSpectralProj_mul_bochnerFilteredOp_mul_one_sub_eq_zero
      sys V s hw_int hw_zero h_gap X)
    (one_sub_perturbedGroundSpectralProj_mul_bochnerFilteredOp_mul_eq_zero
      sys V s hw_int hw_zero h_gap X)).2

end
