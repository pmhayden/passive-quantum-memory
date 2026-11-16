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

import Defs.LocalHamiltonian
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Normed.Algebra.Exponential
import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.Analysis.Normed.Operator.CompleteCodomain
import Mathlib.Analysis.Normed.Operator.NormedSpace
import Mathlib.Analysis.Normed.Ring.Lemmas
import Mathlib.Topology.Algebra.InfiniteSum.Basic

/-!
# Spectral Gibbs States, Canonical KMS Inner Products, and KMS-Symmetric Lindblad Generators

Defines spectral-theorem eigenbases and eigenvalues (`opEigenbasis`, `opEigenvalues`), partition functions (`gibbsPartitionZ`), Gibbs density operators and failure probabilities (`gibbsDensityOp`, `gibbsFailureProb`), and fractional powers (`gibbsSqrtOp`, `gibbsInvSqrtOp`). Formalizes the KMS inner product and norm (`kmsInnerReal`, `kmsNorm`, `opKMSNorm`) together with coherent Hamiltonian drift, KMS dissipative forms (`kmsDissipativeForm`, `IsKMSSymmetricDissipativeGenerator`), and KMS-symmetric Lindblad and GKLS Davies generators and semigroup trajectories (`BathChannel`, `IsCubeRangeBath`, `opKMSLindbladGenerator`, `SatisfiesKMSLindbladODE`, `SingleSiteThermalCoupling`, `opDaviesThermalGenerator`, `kmsDriftDirichletBound`).

## References

* Part I, Section 5.4 (`subsec:safe-decoded-observables`), Proposition 5.7 (`prop:safe-subspace-immunity`), Section 5.5 (`subsec:unperturbed-kms-lifetime`), Theorem 5.8 (`thm:unperturbed-kms-lifetime`)
* Part II, Section 2 (`subsec:setup`), Definition 2.6 (`def:kms-lindblad`), Section 6 (`sec:lindblad`), Lemma 6.1 (`lem:kms-fourth-root`), Section 6.2 (`subsec:kms-gronwall`), Theorem 6.2 (`thm:kms-gronwall-bare`)
-/

noncomputable section

open scoped Classical InnerProduct ComplexConjugate BigOperators
open ContinuousLinearMap

/-!
## 1. Finite-Dimensional Spectral Diagonalization of Self-Adjoint Hamiltonians
-/

/-- The $i$-th basis vector of `sortedEigenbasis H hH` is an eigenvector of $H$ with eigenvalue `sortedEigenvalues H hH i`. -/
lemma sortedEigenbasis_apply_H {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    (H : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site) (hH : IsSelfAdjoint H)
    (i : Fin (Module.finrank ℂ (ManyBodyHilbertSpace Site))) :
    H (sortedEigenbasis H hH i) = (sortedEigenvalues H hH i : ℂ) • sortedEigenbasis H hH i := by
  let hSymm : H.toLinearMap.IsSymmetric :=
    (LinearMap.isSymmetric_iff_isSelfAdjoint H.toLinearMap).mpr
      ((ContinuousLinearMap.isSelfAdjoint_toLinearMap_iff H).mpr hH)
  dsimp [sortedEigenbasis, sortedEigenvalues, finRevEquiv]
  rw [OrthonormalBasis.reindex_apply]; exact hSymm.apply_eigenvectorBasis rfl i.rev

/-- Canonical orthonormal eigenbasis of any self-adjoint operator $H$, indexed by `ManyBodyConfig Site`. -/
def opEigenbasis {D L : ℕ} {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    (H : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site) (hH : IsSelfAdjoint H) :
    ManyBodyConfig Site → ManyBodyHilbertSpace Site :=
  fun ω => sortedEigenbasis H hH (configFinEquiv Site ω)

/-- Canonical real eigenvalues of any self-adjoint operator $H$, indexed by `ManyBodyConfig Site`. -/
def opEigenvalues {D L : ℕ} {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    (H : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site) (hH : IsSelfAdjoint H) :
    ManyBodyConfig Site → ℝ :=
  fun ω => sortedEigenvalues H hH (configFinEquiv Site ω)

/-- Eigenvector equation $H \psi_\omega = E_\omega \psi_\omega$ for `opEigenbasis H hH`. -/
lemma opEigenbasis_apply_H {D L : ℕ} {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    (H : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site) (hH : IsSelfAdjoint H) (ω : ManyBodyConfig Site) :
    H (opEigenbasis H hH ω) = (opEigenvalues H hH ω : ℂ) • opEigenbasis H hH ω :=
  sortedEigenbasis_apply_H H hH (configFinEquiv Site ω)

/-- The sum of two self-adjoint continuous linear operators on a complex Hilbert space is self-adjoint. -/
lemma isSelfAdjoint_add {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [CompleteSpace E] {A B : E →L[ℂ] E} (hA : IsSelfAdjoint A) (hB : IsSelfAdjoint B) :
    IsSelfAdjoint (A + B) := hA.add hB

/-! ## 2. Gibbs Partition Function, Density Operator, and Fractional Powers -/

/-- Canonical partition function $Z_\beta := \sum_{\omega} \exp(-\beta E(\omega))$ of an eigenenergy spectrum $E$. -/
def gibbsPartitionZ {D L : ℕ} {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    (E_eig : ManyBodyConfig Site → ℝ) (β : ℝ) : ℝ := ∑ ω : ManyBodyConfig Site, Real.exp (-β * E_eig ω)

/-- Strict positivity $0 < Z_\beta$ of the Gibbs partition function on a nonempty configuration space. -/
lemma gibbsPartitionZ_pos {D L : ℕ} {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    [∀ x, Nonempty (Site x)] (E_eig : ManyBodyConfig Site → ℝ) (β : ℝ) :
    0 < gibbsPartitionZ E_eig β := by
  unfold gibbsPartitionZ; exact Finset.sum_pos (fun ω _ => Real.exp_pos (-β * E_eig ω)) Finset.univ_nonempty

/-- Normalized Gibbs eigenvalue probability $p_\beta(\omega) := Z_\beta^{-1} \exp(-\beta E(\omega))$. -/
def gibbsProb {D L : ℕ} {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    (E_eig : ManyBodyConfig Site → ℝ) (β : ℝ) (ω : ManyBodyConfig Site) : ℝ :=
  (gibbsPartitionZ E_eig β)⁻¹ * Real.exp (-β * E_eig ω)

/-- Strict positivity of `gibbsProb E_eig β ω`. -/
lemma gibbsProb_pos {D L : ℕ} {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    [∀ x, Nonempty (Site x)] (E_eig : ManyBodyConfig Site → ℝ) (β : ℝ) (ω : ManyBodyConfig Site) :
    0 < gibbsProb E_eig β ω := by dsimp [gibbsProb]; have hZ := gibbsPartitionZ_pos E_eig β; positivity

/-- Non-negativity of `gibbsProb E_eig β ω`. -/
lemma gibbsProb_nonneg {D L : ℕ} {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    [∀ x, Nonempty (Site x)] (E_eig : ManyBodyConfig Site → ℝ) (β : ℝ) (ω : ManyBodyConfig Site) :
    0 ≤ gibbsProb E_eig β ω := le_of_lt (gibbsProb_pos E_eig β ω)

/-- Normalization of the Gibbs probability distribution: $\sum_\omega p_\beta(\omega) = 1$. -/
lemma sum_gibbsProb_eq_one {D L : ℕ} {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    [∀ x, Nonempty (Site x)] (E_eig : ManyBodyConfig Site → ℝ) (β : ℝ) :
    (∑ ω : ManyBodyConfig Site, gibbsProb E_eig β ω) = 1 := by
  dsimp [gibbsProb]; rw [← Finset.mul_sum]; exact inv_mul_cancel₀ (ne_of_gt (gibbsPartitionZ_pos E_eig β))

/-- Square root of the Gibbs probability: $\sqrt{p_\beta(\omega)} = Z_\beta^{-1/2} \exp(-\beta E(\omega)/2)$. -/
lemma sqrt_gibbsProb_eq {D L : ℕ} {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    [∀ x, Nonempty (Site x)] (E_eig : ManyBodyConfig Site → ℝ) (β : ℝ) (ω : ManyBodyConfig Site) :
    Real.sqrt (gibbsProb E_eig β ω) =
      (Real.sqrt (gibbsPartitionZ E_eig β))⁻¹ * Real.exp (-β * E_eig ω / 2) := by
  have hZ_pos : 0 < gibbsPartitionZ E_eig β := gibbsPartitionZ_pos E_eig β
  have hZ_sq : (Real.sqrt (gibbsPartitionZ E_eig β)) ^ 2 = gibbsPartitionZ E_eig β := Real.sq_sqrt (le_of_lt hZ_pos)
  have hexp_sq : (Real.exp (-β * E_eig ω / 2)) ^ 2 = Real.exp (-β * E_eig ω) := by rw [sq, ← Real.exp_add]; ring_nf
  have h_eq : gibbsProb E_eig β ω =
      ((Real.sqrt (gibbsPartitionZ E_eig β))⁻¹ * Real.exp (-β * E_eig ω / 2)) ^ 2 := by
    dsimp [gibbsProb]; rw [mul_pow, inv_pow, hZ_sq, hexp_sq]
  rw [h_eq, Real.sqrt_sq (by positivity)]

/-- Unnormalized Boltzmann operator $\exp(-\beta H) = \sum_\omega \exp(-\beta E(\omega)) |\psi_\omega\rangle\langle\psi_\omega|$. -/
def gibbsBoltzmannOp {D L : ℕ} {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    (ψ_eig : ManyBodyConfig Site → ManyBodyHilbertSpace Site) (E_eig : ManyBodyConfig Site → ℝ) (β : ℝ) :
    ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site :=
  ∑ ω : ManyBodyConfig Site, (Real.exp (-β * E_eig ω) : ℂ) • rankOneKetBra (ψ_eig ω)

/-- Normalized Gibbs equilibrium density operator $\rho_\beta := Z_\beta^{-1} \exp(-\beta H)$. -/
def gibbsDensityOp {D L : ℕ} {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    (ψ_eig : ManyBodyConfig Site → ManyBodyHilbertSpace Site) (E_eig : ManyBodyConfig Site → ℝ) (β : ℝ) :
    ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site :=
  ((gibbsPartitionZ E_eig β : ℂ)⁻¹) • gibbsBoltzmannOp ψ_eig E_eig β

/-- Positive square root $\rho_\beta^{1/2} := Z_\beta^{-1/2} \sum_\omega \exp(-\beta E(\omega)/2) |\psi_\omega\rangle\langle\psi_\omega|$. -/
def gibbsSqrtOp {D L : ℕ} {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    (ψ_eig : ManyBodyConfig Site → ManyBodyHilbertSpace Site) (E_eig : ManyBodyConfig Site → ℝ) (β : ℝ) :
    ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site :=
  (((Real.sqrt (gibbsPartitionZ E_eig β)) : ℂ)⁻¹) •
    ∑ ω : ManyBodyConfig Site, (Real.exp (-β * E_eig ω / 2) : ℂ) • rankOneKetBra (ψ_eig ω)

/-- Inverse positive square root $\rho_\beta^{-1/2} := Z_\beta^{1/2} \sum_\omega \exp(+\beta E(\omega)/2) |\psi_\omega\rangle\langle\psi_\omega|$. -/
def gibbsInvSqrtOp {D L : ℕ} {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    (ψ_eig : ManyBodyConfig Site → ManyBodyHilbertSpace Site) (E_eig : ManyBodyConfig Site → ℝ) (β : ℝ) :
    ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site :=
  ((Real.sqrt (gibbsPartitionZ E_eig β)) : ℂ) •
    ∑ ω : ManyBodyConfig Site, (Real.exp (β * E_eig ω / 2) : ℂ) • rankOneKetBra (ψ_eig ω)

/-!
## 3. KMS Inner Product, Norms, Coherent Drift, Dirichlet Form & Lindblad Generator
-/

/-- KMS modular sandwich map $\Gamma_\beta(X) := \rho_\beta^{1/2} X \rho_\beta^{1/2}$. -/
def kmsSandwich {D L : ℕ} {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    (ψ_eig : ManyBodyConfig Site → ManyBodyHilbertSpace Site) (E_eig : ManyBodyConfig Site → ℝ) (β : ℝ)
    (X : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site) :
    ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site :=
  gibbsSqrtOp ψ_eig E_eig β * X * gibbsSqrtOp ψ_eig E_eig β

/-- Inverse KMS modular sandwich map $\Gamma_\beta^{-1}(X) := \rho_\beta^{-1/2} X \rho_\beta^{-1/2}$. -/
def kmsInvSandwich {D L : ℕ} {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    (ψ_eig : ManyBodyConfig Site → ManyBodyHilbertSpace Site) (E_eig : ManyBodyConfig Site → ℝ) (β : ℝ)
    (X : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site) :
    ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site :=
  gibbsInvSqrtOp ψ_eig E_eig β * X * gibbsInvSqrtOp ψ_eig E_eig β

/-- Real part of the Kubo–Martin–Schwinger (KMS) inner product $\operatorname{Re}\langle A, B\rangle_{\mathrm{KMS}}$. -/
def kmsInnerReal {D L : ℕ} {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    (ψ_eig : ManyBodyConfig Site → ManyBodyHilbertSpace Site) (E_eig : ManyBodyConfig Site → ℝ) (β : ℝ)
    (A B : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site) : ℝ :=
  hilbertTrace (gibbsSqrtOp ψ_eig E_eig β * A† * gibbsSqrtOp ψ_eig E_eig β * B)

/-- Squared KMS norm $\|A\|_{\mathrm{KMS}}^2 := \langle A, A\rangle_{\mathrm{KMS}}$. -/
def kmsNormSq {D L : ℕ} {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    (ψ_eig : ManyBodyConfig Site → ManyBodyHilbertSpace Site) (E_eig : ManyBodyConfig Site → ℝ) (β : ℝ)
    (A : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site) : ℝ :=
  kmsInnerReal ψ_eig E_eig β A A

/-- KMS norm $\|A\|_{\mathrm{KMS}} := \sqrt{\|A\|_{\mathrm{KMS}}^2}$. -/
def kmsNorm {D L : ℕ} {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    (ψ_eig : ManyBodyConfig Site → ManyBodyHilbertSpace Site) (E_eig : ManyBodyConfig Site → ℝ) (β : ℝ)
    (A : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site) : ℝ :=
  Real.sqrt (kmsNormSq ψ_eig E_eig β A)

/-- Coherent KMS drift rate $\Gamma_{\mathrm{coh}}(O) := \|[H_0 + V_{\mathrm{tot}}, O]\|_{\mathrm{KMS}}$ for `CommutingProjectorHamiltonian`. -/
def kmsCoherentDrift {D L : ℕ} {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    (sys : CommutingProjectorHamiltonian D L Site) (V : LocalPerturbation D L Site)
    (ψ_eig : ManyBodyConfig Site → ManyBodyHilbertSpace Site) (E_eig : ManyBodyConfig Site → ℝ) (β : ℝ)
    (O : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site) : ℝ :=
  kmsNorm ψ_eig E_eig β (opCommutator (sys.H0 + V.totalPerturbation) O)

/-- Quasi-local KMS dissipative Dirichlet form $\Gamma_{\mathrm{diss}}(O) = \mathcal{E}_{\mathrm{KMS}}(O)$. -/
def kmsDirichletForm {D L : ℕ} {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    {BathIdx : Type} [Fintype BathIdx]
    (ψ_eig : ManyBodyConfig Site → ManyBodyHilbertSpace Site) (E_eig : ManyBodyConfig Site → ℝ) (β : ℝ)
    (L_jump : BoxD D L → BathIdx → (ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site))
    (O : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site) : ℝ :=
  (1 / 2 : ℝ) * ∑ q : BoxD D L, ∑ α : BathIdx, kmsNormSq ψ_eig E_eig β (opCommutator (L_jump q α) O)

/-!
## 4. Canonical Auto-Diagonalized KMS Wrappers & Semigroup Trajectory
-/

/-- Canonical Gibbs decoding failure probability
    $\operatorname{Tr}(\rho_{\beta, H} P_{\mathrm{fail}})$ for a self-adjoint Hamiltonian $H$. -/
def gibbsFailureProb {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    (H : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site)
    (hH : IsSelfAdjoint H) (β : ℝ)
    (P_fail : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site) : ℝ :=
  hilbertTrace (gibbsDensityOp (opEigenbasis H hH) (opEigenvalues H hH) β * P_fail)

/-- Canonical KMS squared norm $\|A\|_{\mathrm{KMS}, \beta, H}^2$ for a self-adjoint Hamiltonian $H$. -/
def opKMSNormSq {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    (H : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site)
    (hH : IsSelfAdjoint H) (β : ℝ)
    (A : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site) : ℝ :=
  kmsNormSq (opEigenbasis H hH) (opEigenvalues H hH) β A

/-- Canonical KMS norm $\|A\|_{\mathrm{KMS}, \beta, H}$ for a self-adjoint Hamiltonian $H$. -/
def opKMSNorm {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    (H : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site)
    (hH : IsSelfAdjoint H) (β : ℝ)
    (A : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site) : ℝ :=
  kmsNorm (opEigenbasis H hH) (opEigenvalues H hH) β A

/-- Elementary bath channel $(L, \gamma, \mathrm{support})$ with jump operator $L \in \mathcal{B}(\mathcal{H})$
    and non-negative coupling rate $\gamma \ge 0$. -/
structure BathChannel (D L_box : ℕ) (Site : BoxD D L_box → Type)
    [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)] where
  L : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site
  γ : ℝ
  support : Finset (BoxD D L_box)

/-- Jump channel family of cube range $R_{\mathrm{bath}}$ on `BoxD D L_box`: every channel has
    $\gamma \ge 0$ and jump operator supported on an open-box cube $W \in \mathcal{S}(r)$ of side
    $1 \le r \le \min(R_{\mathrm{bath}}, L_{\mathrm{box}})$
    (Part I, Section 5.5 (`subsec:unperturbed-kms-lifetime`);
    Part II, Section 2, Definition 2.6 (`def:kms-lindblad`)). -/
def IsCubeRangeBath (D L_box R_bath : ℕ) [NeZero L_box]
    {Site : BoxD D L_box → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    (bath : Finset (BathChannel D L_box Site)) : Prop :=
  ∀ ch ∈ bath, 0 ≤ ch.γ ∧
    ∃ r ∈ Finset.Icc 1 (min R_bath L_box), ∃ W ∈ boxCubes D L_box r,
      ch.support = W ∧ IsSupportedOn Site W ch.L

/-- Adjoint-symmetric bath channel family: admits an involution $\mathrm{ch} \mapsto \overline{\mathrm{ch}}$
    preserving coupling rates $\gamma_{\overline{\mathrm{ch}}} = \gamma_{\mathrm{ch}}$ and mapping
    jump operators to their adjoints $L_{\overline{\mathrm{ch}}} = L_{\mathrm{ch}}^\dagger$
    (Part I, Section 5.5 (`subsec:unperturbed-kms-lifetime`);
    Part II, Section 2, Definition 2.6 (`def:kms-lindblad`)). -/
def IsAdjointSymmetricBath {D L_box : ℕ}
    {Site : BoxD D L_box → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    (bath : Finset (BathChannel D L_box Site)) : Prop :=
  ∃ inv : bath → bath,
    (∀ ch : bath, inv (inv ch) = ch) ∧
    (∀ ch : bath, (inv ch).1.γ = ch.1.γ ∧ (inv ch).1.L = (ch.1.L)†)

/-- Continuous linear left-right multiplication superoperator $X \mapsto A X B$ on $\mathcal{B}(E)$. -/
def clmSandwichOp {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    (A B : E →L[ℂ] E) : (E →L[ℂ] E) →L[ℂ] (E →L[ℂ] E) :=
  (ContinuousLinearMap.mul ℂ (E →L[ℂ] E) A).comp
    ((ContinuousLinearMap.mul ℂ (E →L[ℂ] E)).flip B)

@[simp] lemma clmSandwichOp_apply {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [CompleteSpace E] (A B X : E →L[ℂ] E) :
    clmSandwichOp A B X = A * X * B := by
  dsimp [clmSandwichOp]; simp [mul_assoc]

/-- Continuous linear commutator superoperator $X \mapsto [A, X] = A X - X A$ on $\mathcal{B}(E)$. -/
def opCommutatorCLM {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    (A : E →L[ℂ] E) : (E →L[ℂ] E) →L[ℂ] (E →L[ℂ] E) :=
  ContinuousLinearMap.mul ℂ (E →L[ℂ] E) A - (ContinuousLinearMap.mul ℂ (E →L[ℂ] E)).flip A

@[simp] lemma opCommutatorCLM_apply {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [CompleteSpace E] (A X : E →L[ℂ] E) :
    opCommutatorCLM A X = opCommutator A X := rfl

/-- Shortcut topological-ring instance on the superoperator Banach algebra
    `(E →L[ℂ] E) →L[ℂ] (E →L[ℂ] E)` (defeq to Mathlib's `ContinuousLinearMap.toNormedRing`). -/
instance instSuperopIsTopologicalRing {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [CompleteSpace E] : IsTopologicalRing ((E →L[ℂ] E) →L[ℂ] (E →L[ℂ] E)) :=
  letI : NormedRing ((E →L[ℂ] E) →L[ℂ] (E →L[ℂ] E)) := ContinuousLinearMap.toNormedRing
  inferInstance

/-- Canonical KMS Lindblad generator $\mathcal{L}_{\beta, H, \mathrm{bath}}^*(X)$ for a finite collection of `BathChannel`s. -/
def opKMSLindbladGenerator {D L_box : ℕ}
    {Site : BoxD D L_box → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    (H : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site)
    (hH : IsSelfAdjoint H) (β : ℝ)
    (bath : Finset (BathChannel D L_box Site))
    (X : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site) :
    ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site :=
  let ψ_eig := opEigenbasis H hH
  let E_eig := opEigenvalues H hH
  Complex.I • opCommutator H X -
    (1 / 2 : ℂ) • ∑ ch ∈ bath,
      (ch.γ : ℂ) • kmsInvSandwich ψ_eig E_eig β
        (opCommutator (ch.L†) (kmsSandwich ψ_eig E_eig β (opCommutator ch.L X)))

/-- Continuous linear dissipative superoperator $\mathcal{L}_{\beta,\mathrm{diss}}^*$ of `opKMSLindbladGenerator`. -/
def opKMSLindbladDissipator {D L_box : ℕ}
    {Site : BoxD D L_box → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    (H : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site)
    (hH : IsSelfAdjoint H) (β : ℝ)
    (bath : Finset (BathChannel D L_box Site)) :
    (ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site) →L[ℂ]
      (ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site) :=
  let ψ_eig := opEigenbasis H hH
  let E_eig := opEigenvalues H hH
  let S_half := gibbsSqrtOp ψ_eig E_eig β
  let S_inv := gibbsInvSqrtOp ψ_eig E_eig β
  ((-1 / 2 : ℂ) • ∑ ch ∈ bath,
    (ch.γ : ℂ) •
      ((clmSandwichOp S_inv S_inv).comp
        ((opCommutatorCLM (ch.L†)).comp
          ((clmSandwichOp S_half S_half).comp (opCommutatorCLM ch.L)))))

/-- Continuous linear map wrapper for `opKMSLindbladGenerator` enabling `NormedSpace.exp`. -/
def opKMSLindbladGeneratorCLM {D L_box : ℕ}
    {Site : BoxD D L_box → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    (H : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site)
    (hH : IsSelfAdjoint H) (β : ℝ)
    (bath : Finset (BathChannel D L_box Site)) :
    (ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site) →L[ℂ]
      (ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site) :=
  Complex.I • opCommutatorCLM H + opKMSLindbladDissipator H hH β bath

@[simp] lemma opKMSLindbladGeneratorCLM_apply {D L_box : ℕ}
    {Site : BoxD D L_box → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    (H : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site)
    (hH : IsSelfAdjoint H) (β : ℝ)
    (bath : Finset (BathChannel D L_box Site))
    (X : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site) :
    opKMSLindbladGeneratorCLM H hH β bath X = opKMSLindbladGenerator H hH β bath X := by
  dsimp [opKMSLindbladGeneratorCLM, opKMSLindbladDissipator, opKMSLindbladGenerator,
    kmsInvSandwich, kmsSandwich]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.sum_apply, ContinuousLinearMap.comp_apply,
    clmSandwichOp_apply, opCommutatorCLM_apply]
  rw [sub_eq_add_neg, ← neg_smul, neg_div]

/-- Matrix-exponential Heisenberg semigroup $e^{t \mathcal{L}_{\beta, H, \mathrm{bath}}^*}$ on $\mathcal{B}(\mathcal{H})$. -/
def opKMSLindbladSemigroup {D L_box : ℕ}
    {Site : BoxD D L_box → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    (H : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site)
    (hH : IsSelfAdjoint H) (β : ℝ)
    (bath : Finset (BathChannel D L_box Site)) (t : ℝ) :
    (ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site) →L[ℂ]
      (ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site) :=
  NormedSpace.exp ((t : ℂ) • opKMSLindbladGeneratorCLM H hH β bath)

/-- KMS Heisenberg–Lindblad ODE trajectory predicate on $[0, t]$ for a self-adjoint Hamiltonian $H$. -/
def SatisfiesKMSLindbladODE {D L_box : ℕ}
    {Site : BoxD D L_box → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    (H : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site)
    (hH : IsSelfAdjoint H) (β : ℝ)
    (bath : Finset (BathChannel D L_box Site))
    (O_dec : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site)
    (O_t : ℝ → (ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site))
    (t : ℝ) : Prop :=
  let ψ_eig := opEigenbasis H hH
  let E_eig := opEigenvalues H hH
  O_t 0 = O_dec ∧
  (∀ s ∈ Set.Icc 0 t, IsSelfAdjoint (O_t s)) ∧
  ∃ f' : ℝ → ℝ,
    (∀ s ∈ Set.Icc 0 t,
      HasDerivAt (fun u => kmsNormSq ψ_eig E_eig β (O_t u - O_dec)) (f' s) s) ∧
    (∀ s ∈ Set.Icc 0 t,
      (1 / 2 : ℝ) * f' s =
        kmsInnerReal ψ_eig E_eig β (O_t s - O_dec)
          (opKMSLindbladGenerator H hH β bath (O_t s)))

/-- Universal KMS semigroup drift-plus-Dirichlet upper bound
    $t\,\Gamma_{\mathrm{coh}}(O) + \sqrt{\frac{t}{2}\,\Gamma_{\mathrm{diss}}(O)}$
    (Part II, Section 6.2 (`subsec:kms-gronwall`), Theorem 6.2 (`thm:kms-gronwall-bare`),
    Equation (90) (`eq:gronwall-sqrt-drift`); Theorem 6.5 (`thm:main-D`), Equation (100) (`eq:main-D-decay`)). -/
def kmsDriftDirichletBound (Γ_coh Γ_diss t : ℝ) : ℝ :=
  t * Γ_coh + Real.sqrt ((t / 2) * Γ_diss)

/-!
## 5. Operator Positivity, Complete Positivity, KMS Dissipative Generators & GKLS Davies Baths
-/

/-- Positive semidefinite operator predicate $X = X^\dagger \wedge \forall \psi,\, 0 \le \operatorname{Re}\langle \psi, X \psi\rangle$. -/
def IsPositiveOp {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    (X : E →L[ℂ] E) : Prop :=
  IsSelfAdjoint X ∧ ∀ ψ : E, 0 ≤ RCLike.re (inner ℂ ψ (X ψ))

/-- Positivity-preserving superoperator predicate on $\mathcal{B}(E)$. -/
def IsPositivityPreservingMap {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [CompleteSpace E] (Φ : (E →L[ℂ] E) →L[ℂ] (E →L[ℂ] E)) : Prop :=
  ∀ X : E →L[ℂ] E, IsPositiveOp X → IsPositiveOp (Φ X)

/-- Adjoint-preserving ($\dagger$-preserving) superoperator predicate on $\mathcal{B}(E)$. -/
def IsStarPreservingMap {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [CompleteSpace E] (Φ : (E →L[ℂ] E) →L[ℂ] (E →L[ℂ] E)) : Prop :=
  ∀ X : E →L[ℂ] E, (Φ X)† = Φ (X†)

/-- $i$-th block coordinate projection $\pi_i : E^{\oplus n} \to_L[\mathbb{C}] E$ on `PiLp 2 (fun _ : Fin n => E)`. -/
def ancillaBlockProj {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    (n : ℕ) (i : Fin n) : PiLp 2 (fun _ : Fin n => E) →L[ℂ] E :=
  PiLp.proj 2 (fun _ : Fin n => E) i

/-- Block-matrix ancilla amplification $(\Phi \otimes \mathrm{id}_{M_n})(M)$ on $E^{\oplus n} \cong E \otimes \mathbb{C}^n$. -/
def ancillaLiftMap {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    (n : ℕ) (Φ : (E →L[ℂ] E) →L[ℂ] (E →L[ℂ] E))
    (M : PiLp 2 (fun _ : Fin n => E) →L[ℂ] PiLp 2 (fun _ : Fin n => E)) :
    PiLp 2 (fun _ : Fin n => E) →L[ℂ] PiLp 2 (fun _ : Fin n => E) :=
  ∑ i : Fin n, ∑ j : Fin n,
    ((ancillaBlockProj (E := E) n i)†).comp
      ((Φ ((ancillaBlockProj (E := E) n i).comp (M.comp ((ancillaBlockProj (E := E) n j)†)))).comp
        (ancillaBlockProj (E := E) n j))

/-- Complete positivity predicate: $(\Phi \otimes \mathrm{id}_{M_n})(M) \ge 0$ for every $n \in \mathbb{N}$
    and every positive operator $M \ge 0$ on $E^{\oplus n}$. -/
def IsCompletelyPositiveMap {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [CompleteSpace E] (Φ : (E →L[ℂ] E) →L[ℂ] (E →L[ℂ] E)) : Prop :=
  ∀ (n : ℕ) (M : PiLp 2 (fun _ : Fin n => E) →L[ℂ] PiLp 2 (fun _ : Fin n => E)),
    IsPositiveOp M → IsPositiveOp (ancillaLiftMap n Φ M)

/-- Heisenberg-picture dual of a CPTP quantum channel: unital, $\dagger$-preserving, and completely positive. -/
def IsCPUnitalStarMap {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [CompleteSpace E] (Φ : (E →L[ℂ] E) →L[ℂ] (E →L[ℂ] E)) : Prop :=
  Φ 1 = 1 ∧ IsStarPreservingMap Φ ∧ IsCompletelyPositiveMap Φ

/-- Symmetric bilinear KMS dissipative form
    $\mathcal{E}_\beta(A, B) := -\langle A, \mathcal{L}_{\beta,\mathrm{diss}}^*(B)\rangle_{\mathrm{KMS},\beta}$
    (Part II, Section 2, Definition 2.6 (`def:kms-lindblad`)). -/
def kmsDissipativeForm {D L_box : ℕ}
    {Site : BoxD D L_box → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    (H : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site)
    (hH : IsSelfAdjoint H) (β : ℝ)
    (L_diss : (ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site) →L[ℂ]
      (ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site))
    (A B : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site) : ℝ :=
  -kmsInnerReal (opEigenbasis H hH) (opEigenvalues H hH) β A (L_diss B)

/-- General KMS-symmetric dissipative generator predicate on $\mathcal{L}_{\beta,\mathrm{diss}}^*$
    (Part II, Section 2, Definition 2.6 (`def:kms-lindblad`) and Section 6.2, Theorem 6.2 (`thm:kms-gronwall-bare`)). -/
def IsKMSSymmetricDissipativeGenerator {D L_box : ℕ}
    {Site : BoxD D L_box → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    (H : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site)
    (hH : IsSelfAdjoint H) (β : ℝ)
    (L_diss : (ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site) →L[ℂ]
      (ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site)) : Prop :=
  let ψ_eig := opEigenbasis H hH
  let E_eig := opEigenvalues H hH
  L_diss 1 = 0 ∧
  (∀ A B, kmsInnerReal ψ_eig E_eig β A (L_diss B) = kmsInnerReal ψ_eig E_eig β (L_diss A) B) ∧
  (∀ A, 0 ≤ -kmsInnerReal ψ_eig E_eig β A (L_diss A))

/-- KMS-dissipative Heisenberg ODE trajectory predicate on $[0, t]$ for a self-adjoint Hamiltonian $H$
    and dissipative superoperator `L_diss` (Part II, Section 2, Definition 2.6 (`def:kms-lindblad`)). -/
def SatisfiesKMSDissipativeODE {D L_box : ℕ}
    {Site : BoxD D L_box → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    (H : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site)
    (hH : IsSelfAdjoint H) (β : ℝ)
    (L_diss : (ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site) →L[ℂ]
      (ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site))
    (O_dec : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site)
    (O_t : ℝ → (ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site))
    (t : ℝ) : Prop :=
  let ψ_eig := opEigenbasis H hH
  let E_eig := opEigenvalues H hH
  O_t 0 = O_dec ∧
  (∀ s ∈ Set.Icc 0 t, IsSelfAdjoint (O_t s)) ∧
  ∃ f' : ℝ → ℝ,
    (∀ s ∈ Set.Icc 0 t,
      HasDerivAt (fun u => kmsNormSq ψ_eig E_eig β (O_t u - O_dec)) (f' s) s) ∧
    (∀ s ∈ Set.Icc 0 t,
      (1 / 2 : ℝ) * f' s =
        kmsInnerReal ψ_eig E_eig β (O_t s - O_dec)
          (Complex.I • opCommutator H (O_t s) + L_diss (O_t s)))

/-- Single-site Hermitian system–bath coupling $(v, S, h_{\mathrm{spec}})$ obeying KMS detailed balance
    $h_{\mathrm{spec}}(-\omega) = e^{-\beta \omega} h_{\mathrm{spec}}(\omega) \ge 0$ ($\omega \in \mathbb{Z}$)
    (Part I, Section 5.5 (`subsec:unperturbed-kms-lifetime`), Theorem 5.8(ii); Part II, Theorem 6.5(1)). -/
structure SingleSiteThermalCoupling (D L_box : ℕ) (Site : BoxD D L_box → Type)
    [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)] (β : ℝ) where
  v : BoxD D L_box
  S : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site
  h_spec : ℤ → ℝ
  isSelfAdjoint_S : IsSelfAdjoint S
  isSupported_S : IsSupportedOn Site {v} S
  kms_detailed_balance : ∀ ω : ℤ,
    0 ≤ h_spec ω ∧ h_spec (-ω) = Real.exp (-β * (ω : ℝ)) * h_spec ω

/-- Orthogonal spectral projection $P_E(H) := \sum_{\tau : E_\tau = E} |\psi_\tau\rangle\langle\psi_\tau|$
    onto the eigenspace $\ker(H - E I)$ of a self-adjoint operator $H$. -/
def spectralEigenspaceProj {D L_box : ℕ}
    {Site : BoxD D L_box → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    (H : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site)
    (hH : IsSelfAdjoint H) (E : ℝ) :
    ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site :=
  ∑ τ ∈ Finset.univ.filter (fun τ : ManyBodyConfig Site => opEigenvalues H hH τ = E),
    rankOneKetBra (opEigenbasis H hH τ)

/-- Bohr-frequency eigenoperator $A_\omega := \sum_{E \in \mathbb{Z}_{\ge 0}} P_{E - \omega}(H_0)\, S\, P_E(H_0)$
    for an `IndexedCommutingProjectorHamiltonian` $H_0$ at integer Bohr frequency $\omega \in \mathbb{Z}$
    (Part I, Section 5.5 (`subsec:unperturbed-kms-lifetime`), Theorem 5.8(ii)). -/
def bohrEigenop {D L_box : ℕ}
    {Site : BoxD D L_box → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (sys : IndexedCommutingProjectorHamiltonian D L_box Site ι)
    (S : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site)
    (ω : ℤ) :
    ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site :=
  ∑ E ∈ Finset.Icc (0 : ℤ) (Fintype.card ι : ℤ),
    if 0 ≤ E - ω ∧ E - ω ≤ (Fintype.card ι : ℤ) then
      spectralEigenspaceProj sys.H0 sys.isSelfAdjoint_H0 ((E - ω : ℤ) : ℝ) * S *
        spectralEigenspaceProj sys.H0 sys.isSelfAdjoint_H0 (E : ℝ)
    else 0

lemma bohrEigenop_eq_zero_of_not_mem_Icc {D L_box : ℕ}
    {Site : BoxD D L_box → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (sys : IndexedCommutingProjectorHamiltonian D L_box Site ι)
    (S : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site)
    {ω : ℤ} (hω : ω ∉ Finset.Icc (-(Fintype.card ι : ℤ)) (Fintype.card ι : ℤ)) :
    bohrEigenop sys S ω = 0 := by
  unfold bohrEigenop
  refine Finset.sum_eq_zero fun E hE => ?_
  rw [Finset.mem_Icc] at hE hω
  exact if_neg (by omega)

/-- Heisenberg-picture GKLS Davies thermal generator $\mathcal{L}_{\beta,\mathrm{Davies}}^*(X)$
    (Part I, Section 5.5 (`subsec:unperturbed-kms-lifetime`), Theorem 5.8(ii); Part II, Theorem 6.5(1)). -/
def opDaviesThermalGenerator {D L_box : ℕ}
    {Site : BoxD D L_box → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (sys : IndexedCommutingProjectorHamiltonian D L_box Site ι)
    (β : ℝ)
    (couplings : Finset (SingleSiteThermalCoupling D L_box Site β))
    (X : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site) :
    ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site :=
  Complex.I • opCommutator sys.H0 X +
    ∑ c ∈ couplings, ∑' ω : ℤ,
      let A_ω := bohrEigenop sys c.S ω
      (c.h_spec ω : ℂ) •
        (A_ω† * X * A_ω - (1 / 2 : ℂ) • (A_ω† * A_ω * X + X * (A_ω† * A_ω)))

/-- Continuous linear map wrapper for `opDaviesThermalGenerator` enabling `NormedSpace.exp`. -/
def opDaviesThermalGeneratorCLM {D L_box : ℕ}
    {Site : BoxD D L_box → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (sys : IndexedCommutingProjectorHamiltonian D L_box Site ι)
    (β : ℝ)
    (couplings : Finset (SingleSiteThermalCoupling D L_box Site β)) :
    (ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site) →L[ℂ]
      (ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site) :=
  Complex.I • opCommutatorCLM sys.H0 +
    ∑ c ∈ couplings, ∑ ω ∈ Finset.Icc (-(Fintype.card ι : ℤ)) (Fintype.card ι : ℤ),
      let A_ω := bohrEigenop sys c.S ω
      (c.h_spec ω : ℂ) •
        (clmSandwichOp (A_ω†) A_ω -
          (1 / 2 : ℂ) • (clmSandwichOp (A_ω† * A_ω) 1 + clmSandwichOp 1 (A_ω† * A_ω)))

@[simp] lemma opDaviesThermalGeneratorCLM_apply {D L_box : ℕ}
    {Site : BoxD D L_box → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (sys : IndexedCommutingProjectorHamiltonian D L_box Site ι)
    (β : ℝ)
    (couplings : Finset (SingleSiteThermalCoupling D L_box Site β))
    (X : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site) :
    opDaviesThermalGeneratorCLM sys β couplings X = opDaviesThermalGenerator sys β couplings X := by
  dsimp [opDaviesThermalGeneratorCLM, opDaviesThermalGenerator]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.sub_apply,
    ContinuousLinearMap.smul_apply, ContinuousLinearMap.sum_apply,
    opCommutatorCLM_apply, clmSandwichOp_apply, mul_one, one_mul]
  congr 1
  refine Finset.sum_congr rfl fun c _ => (tsum_eq_sum fun ω hω => ?_).symm
  have hA0 : bohrEigenop sys c.S ω = 0 := bohrEigenop_eq_zero_of_not_mem_Icc sys c.S hω
  simp [hA0]

/-- Matrix-exponential Heisenberg GKLS Davies semigroup $e^{t \mathcal{L}_{\beta,\mathrm{Davies}}^*}$. -/
def opDaviesThermalSemigroup {D L_box : ℕ}
    {Site : BoxD D L_box → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (sys : IndexedCommutingProjectorHamiltonian D L_box Site ι)
    (β : ℝ)
    (couplings : Finset (SingleSiteThermalCoupling D L_box Site β))
    (t : ℝ) :
    (ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site) →L[ℂ]
      (ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site) :=
  NormedSpace.exp ((t : ℂ) • opDaviesThermalGeneratorCLM sys β couplings)

/-- GKLS Davies thermal ODE trajectory predicate on $[0, t]$ at $V = 0$
    (Part I, Section 5.5 (`subsec:unperturbed-kms-lifetime`), Theorem 5.8(ii)). -/
def SatisfiesDaviesThermalODE {D L_box : ℕ}
    {Site : BoxD D L_box → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (sys : IndexedCommutingProjectorHamiltonian D L_box Site ι)
    (β : ℝ)
    (couplings : Finset (SingleSiteThermalCoupling D L_box Site β))
    (O_dec : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site)
    (O_t : ℝ → (ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site))
    (t : ℝ) : Prop :=
  let ψ_eig := opEigenbasis sys.H0 sys.isSelfAdjoint_H0
  let E_eig := opEigenvalues sys.H0 sys.isSelfAdjoint_H0
  O_t 0 = O_dec ∧
  (∀ s ∈ Set.Icc 0 t, IsSelfAdjoint (O_t s)) ∧
  ∃ f' : ℝ → ℝ,
    (∀ s ∈ Set.Icc 0 t,
      HasDerivAt (fun u => kmsNormSq ψ_eig E_eig β (O_t u - O_dec)) (f' s) s) ∧
    (∀ s ∈ Set.Icc 0 t,
      (1 / 2 : ℝ) * f' s =
        kmsInnerReal ψ_eig E_eig β (O_t s - O_dec)
          (opDaviesThermalGenerator sys β couplings (O_t s)))

/-!
## 6. Spectral Expansion, Orthonormality, and Trace Cyclicity Lemmas
-/

/-- Real part of a real-scalar multiple of a complex number: $\operatorname{Re}(r \cdot z) = r \operatorname{Re}(z)$. -/
lemma re_ofReal_mul (r : ℝ) (z : ℂ) : RCLike.re ((r : ℂ) * z) = r * RCLike.re z := by simp [RCLike.mul_re]

/-- Evaluation of `rankOneKetBra φ` on a vector `ψ`: `(rankOneKetBra φ) ψ = ⟪φ, ψ⟫ • φ`. -/
lemma rankOneKetBra_apply {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] (φ ψ : H) :
    rankOneKetBra φ ψ = inner ℂ φ ψ • φ := rfl

/-- Action of `gibbsSqrtOp ψ_eig E_eig β` on any vector `φ`. -/
lemma gibbsSqrtOp_apply {D L : ℕ} {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    [∀ x, Nonempty (Site x)] (ψ_eig : ManyBodyConfig Site → ManyBodyHilbertSpace Site)
    (E_eig : ManyBodyConfig Site → ℝ) (β : ℝ) (φ : ManyBodyHilbertSpace Site) :
    gibbsSqrtOp ψ_eig E_eig β φ =
      ∑ ω : ManyBodyConfig Site, ((Real.sqrt (gibbsProb E_eig β ω) : ℂ) * inner ℂ (ψ_eig ω) φ) • ψ_eig ω := by
  unfold gibbsSqrtOp; rw [ContinuousLinearMap.smul_apply, ContinuousLinearMap.sum_apply, Finset.smul_sum]
  refine Finset.sum_congr rfl fun ω _ => ?_
  rw [ContinuousLinearMap.smul_apply, rankOneKetBra_apply, smul_smul, smul_smul, sqrt_gibbsProb_eq]
  congr 1; push_cast; ring

/-- Action of `gibbsDensityOp ψ_eig E_eig β` on any vector `φ`. -/
lemma gibbsDensityOp_apply {D L : ℕ} {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    (ψ_eig : ManyBodyConfig Site → ManyBodyHilbertSpace Site) (E_eig : ManyBodyConfig Site → ℝ) (β : ℝ)
    (φ : ManyBodyHilbertSpace Site) :
    gibbsDensityOp ψ_eig E_eig β φ =
      ∑ ω : ManyBodyConfig Site, ((gibbsProb E_eig β ω : ℂ) * inner ℂ (ψ_eig ω) φ) • ψ_eig ω := by
  unfold gibbsDensityOp gibbsBoltzmannOp gibbsProb
  rw [ContinuousLinearMap.smul_apply, ContinuousLinearMap.sum_apply, Finset.smul_sum]
  refine Finset.sum_congr rfl fun ω _ => ?_
  rw [ContinuousLinearMap.smul_apply, rankOneKetBra_apply, smul_smul, smul_smul]
  congr 1; push_cast; ring

/-- Matrix element of `gibbsSqrtOp ψ_eig E_eig β` against an eigenbasis state `ψ_eig ω` on the left. -/
lemma inner_eigenbasis_gibbsSqrtOp_apply {D L : ℕ} {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    [∀ x, Nonempty (Site x)] (ψ_eig : ManyBodyConfig Site → ManyBodyHilbertSpace Site)
    (E_eig : ManyBodyConfig Site → ℝ) (β : ℝ)
    (h_onb : ∀ ω₁ ω₂ : ManyBodyConfig Site, inner ℂ (ψ_eig ω₁) (ψ_eig ω₂) = if ω₁ = ω₂ then (1 : ℂ) else 0)
    (ω : ManyBodyConfig Site) (φ : ManyBodyHilbertSpace Site) :
    inner ℂ (ψ_eig ω) (gibbsSqrtOp ψ_eig E_eig β φ) =
      (Real.sqrt (gibbsProb E_eig β ω) : ℂ) * inner ℂ (ψ_eig ω) φ := by
  rw [gibbsSqrtOp_apply, inner_sum, Finset.sum_eq_single ω]
  · rw [inner_smul_right, h_onb ω ω, if_pos rfl, mul_one]
  · intro ω' _ hne; rw [inner_smul_right, h_onb ω ω', if_neg (Ne.symm hne), mul_zero]
  · intro h_not_mem; exact False.elim (h_not_mem (Finset.mem_univ ω))

/-- Spectral trace expansion of `gibbsDensityOp ψ_eig E_eig β * M` in the orthonormal eigenbasis `ψ_eig`. -/
lemma hilbertTrace_gibbsDensityOp_mul_eq {D L : ℕ} {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    (ψ_eig : ManyBodyConfig Site → ManyBodyHilbertSpace Site) (E_eig : ManyBodyConfig Site → ℝ) (β : ℝ)
    (h_onb : ∀ ω₁ ω₂ : ManyBodyConfig Site, inner ℂ (ψ_eig ω₁) (ψ_eig ω₂) = if ω₁ = ω₂ then (1 : ℂ) else 0)
    (h_tr_basis : ∀ X : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site,
      hilbertTrace X = ∑ ω : ManyBodyConfig Site, RCLike.re (inner ℂ (ψ_eig ω) (X (ψ_eig ω))))
    (M : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site) :
    hilbertTrace (gibbsDensityOp ψ_eig E_eig β * M) =
      ∑ ω : ManyBodyConfig Site, gibbsProb E_eig β ω * RCLike.re (inner ℂ (ψ_eig ω) (M (ψ_eig ω))) := by
  rw [h_tr_basis]; refine Finset.sum_congr rfl fun ω _ => ?_
  change RCLike.re (inner ℂ (ψ_eig ω) (gibbsDensityOp ψ_eig E_eig β (M (ψ_eig ω)))) = _
  rw [gibbsDensityOp_apply, inner_sum, Finset.sum_eq_single ω]
  · rw [inner_smul_right, h_onb ω ω, if_pos rfl, mul_one, re_ofReal_mul]
  · intro ω' _ hne; rw [inner_smul_right, h_onb ω ω', if_neg (Ne.symm hne), mul_zero]
  · intro h_not_mem; exact False.elim (h_not_mem (Finset.mem_univ ω))

/-- Spectral expansion of `kmsInnerReal ψ_eig E_eig β A B` in the orthonormal eigenbasis `ψ_eig`. -/
lemma kmsInnerReal_eq_spectral_sum {D L : ℕ} {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    [∀ x, Nonempty (Site x)] (ψ_eig : ManyBodyConfig Site → ManyBodyHilbertSpace Site)
    (E_eig : ManyBodyConfig Site → ℝ) (β : ℝ)
    (h_onb : ∀ ω₁ ω₂ : ManyBodyConfig Site, inner ℂ (ψ_eig ω₁) (ψ_eig ω₂) = if ω₁ = ω₂ then (1 : ℂ) else 0)
    (h_tr_basis : ∀ X : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site,
      hilbertTrace X = ∑ ω : ManyBodyConfig Site, RCLike.re (inner ℂ (ψ_eig ω) (X (ψ_eig ω))))
    (A B : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site) :
    kmsInnerReal ψ_eig E_eig β A B =
      ∑ ω₁ : ManyBodyConfig Site, ∑ ω₂ : ManyBodyConfig Site,
        Real.sqrt (gibbsProb E_eig β ω₁) * Real.sqrt (gibbsProb E_eig β ω₂) *
          RCLike.re (starRingEnd ℂ (inner ℂ (ψ_eig ω₂) (A (ψ_eig ω₁))) * inner ℂ (ψ_eig ω₂) (B (ψ_eig ω₁))) := by
  unfold kmsInnerReal; rw [h_tr_basis]; refine Finset.sum_congr rfl fun ω₁ _ => ?_
  let ρ_half := gibbsSqrtOp ψ_eig E_eig β
  change RCLike.re (inner ℂ (ψ_eig ω₁) (ρ_half ((A†) (ρ_half (B (ψ_eig ω₁)))))) = _
  rw [inner_eigenbasis_gibbsSqrtOp_apply ψ_eig E_eig β h_onb ω₁, ContinuousLinearMap.adjoint_inner_right]
  rw [gibbsSqrtOp_apply, inner_sum, Finset.mul_sum, map_sum]; refine Finset.sum_congr rfl fun ω₂ _ => ?_
  rw [inner_smul_right]
  have h_conj : inner ℂ (A (ψ_eig ω₁)) (ψ_eig ω₂) = starRingEnd ℂ (inner ℂ (ψ_eig ω₂) (A (ψ_eig ω₁))) := by rw [inner_conj_symm]
  rw [h_conj]
  set r₁ : ℝ := Real.sqrt (gibbsProb E_eig β ω₁); set r₂ : ℝ := Real.sqrt (gibbsProb E_eig β ω₂)
  set zA : ℂ := starRingEnd ℂ (inner ℂ (ψ_eig ω₂) (A (ψ_eig ω₁))); set zB : ℂ := inner ℂ (ψ_eig ω₂) (B (ψ_eig ω₁))
  have h_prod : (r₁ : ℂ) * (((r₂ : ℂ) * zB) * zA) = ((r₁ * r₂ : ℝ) : ℂ) * (zA * zB) := by push_cast; ring
  rw [h_prod, re_ofReal_mul]

/-- Spectral expansion of `kmsNormSq ψ_eig E_eig β A` as a sum of non-negative terms. -/
lemma kmsNormSq_eq_spectral_sum {D L : ℕ} {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    [∀ x, Nonempty (Site x)] (ψ_eig : ManyBodyConfig Site → ManyBodyHilbertSpace Site)
    (E_eig : ManyBodyConfig Site → ℝ) (β : ℝ)
    (h_onb : ∀ ω₁ ω₂ : ManyBodyConfig Site, inner ℂ (ψ_eig ω₁) (ψ_eig ω₂) = if ω₁ = ω₂ then (1 : ℂ) else 0)
    (h_tr_basis : ∀ X : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site,
      hilbertTrace X = ∑ ω : ManyBodyConfig Site, RCLike.re (inner ℂ (ψ_eig ω) (X (ψ_eig ω))))
    (A : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site) :
    kmsNormSq ψ_eig E_eig β A =
      ∑ ω₁ : ManyBodyConfig Site, ∑ ω₂ : ManyBodyConfig Site,
        Real.sqrt (gibbsProb E_eig β ω₁) * Real.sqrt (gibbsProb E_eig β ω₂) *
          ‖inner ℂ (ψ_eig ω₂) (A (ψ_eig ω₁))‖ ^ 2 := by
  dsimp [kmsNormSq]; rw [kmsInnerReal_eq_spectral_sum ψ_eig E_eig β h_onb h_tr_basis A A]
  refine Finset.sum_congr rfl fun ω₁ _ => Finset.sum_congr rfl fun ω₂ _ => ?_
  set z : ℂ := inner ℂ (ψ_eig ω₂) (A (ψ_eig ω₁))
  have h_norm : starRingEnd ℂ z * z = ((‖z‖ ^ 2 : ℝ) : ℂ) := by rw [mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq]
  rw [h_norm]; rfl

/-- Non-negativity of the squared KMS norm `kmsNormSq ψ_eig E_eig β A`. -/
lemma kmsNormSq_nonneg {D L : ℕ} {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    [∀ x, Nonempty (Site x)] (ψ_eig : ManyBodyConfig Site → ManyBodyHilbertSpace Site)
    (E_eig : ManyBodyConfig Site → ℝ) (β : ℝ)
    (h_onb : ∀ ω₁ ω₂ : ManyBodyConfig Site, inner ℂ (ψ_eig ω₁) (ψ_eig ω₂) = if ω₁ = ω₂ then (1 : ℂ) else 0)
    (h_tr_basis : ∀ X : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site,
      hilbertTrace X = ∑ ω : ManyBodyConfig Site, RCLike.re (inner ℂ (ψ_eig ω) (X (ψ_eig ω))))
    (A : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site) :
    0 ≤ kmsNormSq ψ_eig E_eig β A := by
  rw [kmsNormSq_eq_spectral_sum ψ_eig E_eig β h_onb h_tr_basis A]
  exact Finset.sum_nonneg fun ω₁ _ => Finset.sum_nonneg fun ω₂ _ => by positivity

/-- Adjoint invariance of the squared KMS norm: $\|A^\dagger\|_{\mathrm{KMS}}^2 = \|A\|_{\mathrm{KMS}}^2$. -/
lemma kmsNormSq_adjoint {D L : ℕ} {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    [∀ x, Nonempty (Site x)] (ψ_eig : ManyBodyConfig Site → ManyBodyHilbertSpace Site)
    (E_eig : ManyBodyConfig Site → ℝ) (β : ℝ)
    (h_onb : ∀ ω₁ ω₂ : ManyBodyConfig Site, inner ℂ (ψ_eig ω₁) (ψ_eig ω₂) = if ω₁ = ω₂ then (1 : ℂ) else 0)
    (h_tr_basis : ∀ X : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site,
      hilbertTrace X = ∑ ω : ManyBodyConfig Site, RCLike.re (inner ℂ (ψ_eig ω) (X (ψ_eig ω))))
    (A : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site) :
    kmsNormSq ψ_eig E_eig β (A†) = kmsNormSq ψ_eig E_eig β A := by
  rw [kmsNormSq_eq_spectral_sum ψ_eig E_eig β h_onb h_tr_basis (A†),
    kmsNormSq_eq_spectral_sum ψ_eig E_eig β h_onb h_tr_basis A, Finset.sum_comm]
  refine Finset.sum_congr rfl fun ω₁ _ => Finset.sum_congr rfl fun ω₂ _ => ?_
  have h_norm : ‖inner ℂ (ψ_eig ω₁) ((A†) (ψ_eig ω₂))‖ = ‖inner ℂ (ψ_eig ω₂) (A (ψ_eig ω₁))‖ := by
    rw [ContinuousLinearMap.adjoint_inner_right, norm_inner_symm]
  rw [h_norm]; ring

/-- Rank-one ket-bra multiplication for an orthonormal family `ψ_eig`. -/
lemma onb_ketBra_mul_ketBra {D L : ℕ} {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    (ψ_eig : ManyBodyConfig Site → ManyBodyHilbertSpace Site)
    (h_onb : ∀ ω₁ ω₂ : ManyBodyConfig Site, inner ℂ (ψ_eig ω₁) (ψ_eig ω₂) = if ω₁ = ω₂ then (1 : ℂ) else 0)
    (ω₁ ω₂ : ManyBodyConfig Site) :
    rankOneKetBra (ψ_eig ω₁) * rankOneKetBra (ψ_eig ω₂) =
      if ω₁ = ω₂ then rankOneKetBra (ψ_eig ω₁) else 0 := by
  apply ContinuousLinearMap.ext; intro φ
  change rankOneKetBra (ψ_eig ω₁) (rankOneKetBra (ψ_eig ω₂) φ) = _
  rw [rankOneKetBra_apply, rankOneKetBra_apply, inner_smul_right, h_onb ω₁ ω₂]
  split_ifs with h
  · subst h; rw [mul_one, rankOneKetBra_apply]
  · rw [mul_zero, zero_smul, ContinuousLinearMap.zero_apply]

/-- Resolution of the identity $\sum_\omega |\psi_\omega\rangle\langle\psi_\omega| = 1$ for an orthonormal basis. -/
lemma onb_sum_ketBra_eq_one {D L : ℕ} {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    (ψ_eig : ManyBodyConfig Site → ManyBodyHilbertSpace Site)
    (h_onb : ∀ ω₁ ω₂ : ManyBodyConfig Site, inner ℂ (ψ_eig ω₁) (ψ_eig ω₂) = if ω₁ = ω₂ then (1 : ℂ) else 0)
    (h_parseval : ∀ φ : ManyBodyHilbertSpace Site, (∑ ω : ManyBodyConfig Site, ‖inner ℂ (ψ_eig ω) φ‖ ^ 2) = ‖φ‖ ^ 2) :
    (∑ ω : ManyBodyConfig Site, rankOneKetBra (ψ_eig ω)) = 1 := by
  apply ContinuousLinearMap.ext; intro φ
  let v := (∑ ω : ManyBodyConfig Site, rankOneKetBra (ψ_eig ω)) φ - φ
  have hv_inner : ∀ ω₀ : ManyBodyConfig Site, inner ℂ (ψ_eig ω₀) v = 0 := by
    intro ω₀; dsimp [v]; rw [inner_sub_right, ContinuousLinearMap.sum_apply, inner_sum]
    have h_sum : (∑ ω : ManyBodyConfig Site, inner ℂ (ψ_eig ω₀) (rankOneKetBra (ψ_eig ω) φ)) = inner ℂ (ψ_eig ω₀) φ := by
      rw [Finset.sum_eq_single ω₀]
      · rw [rankOneKetBra_apply, inner_smul_right, h_onb ω₀ ω₀, if_pos rfl, mul_one]
      · intro ω _ hne; rw [rankOneKetBra_apply, inner_smul_right, h_onb ω₀ ω, if_neg (Ne.symm hne), mul_zero]
      · intro h_not_mem; exact False.elim (h_not_mem (Finset.mem_univ ω₀))
    rw [h_sum, sub_self]
  have hv_norm_sq : ‖v‖ ^ 2 = 0 := by
    rw [← h_parseval v]; refine Finset.sum_eq_zero fun ω₀ _ => ?_; rw [hv_inner ω₀, norm_zero, sq, zero_mul]
  exact sub_eq_zero.mp (norm_eq_zero.mp (sq_eq_zero_iff.mp hv_norm_sq))

private lemma inner_basisVecGlobal_left_aux {D L : ℕ} {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    (σ : ManyBodyConfig Site) (v : ManyBodyHilbertSpace Site) :
    inner ℂ (basisVecGlobal Site σ) v = v.ofLp σ := by
  simp [basisVecGlobal, PiLp.inner_apply, apply_ite conj, mul_comm]

private lemma eq_sum_basisVecGlobal_aux {D L : ℕ} {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    (v : ManyBodyHilbertSpace Site) :
    v = ∑ τ : ManyBodyConfig Site, (v.ofLp τ) • basisVecGlobal Site τ := by
  ext σ; simp [basisVecGlobal, WithLp.ofLp_sum]

/-- Unconditional cyclicity of `hilbertTrace`: $\operatorname{Tr}(A B) = \operatorname{Tr}(B A)$. -/
lemma hilbertTrace_mul_comm_aux {D L : ℕ} {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    (A B : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site) :
    hilbertTrace (A * B) = hilbertTrace (B * A) := by
  unfold hilbertTrace
  have h_expand : ∀ (C D_op : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site) (ψ : ManyBodyConfig Site),
      inner ℂ (basisVecGlobal Site ψ) ((C * D_op) (basisVecGlobal Site ψ)) =
        ∑ τ : ManyBodyConfig Site, (D_op (basisVecGlobal Site ψ)).ofLp τ * (C (basisVecGlobal Site τ)).ofLp ψ := by
    intro C D_op ψ; rw [inner_basisVecGlobal_left_aux]
    change (C (D_op (basisVecGlobal Site ψ))).ofLp ψ = _
    conv_lhs => rw [eq_sum_basisVecGlobal_aux (D_op (basisVecGlobal Site ψ))]
    rw [map_sum]; simp [WithLp.ofLp_sum, Finset.sum_apply]
  simp_rw [h_expand A B, h_expand B A, map_sum]; rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun τ _ => Finset.sum_congr rfl fun ψ _ => ?_; rw [mul_comm]

/-- Linearity of `hilbertTrace` over finite sums. -/
lemma hilbertTrace_sum {D L : ℕ} {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    {α : Type*} (s : Finset α) (f : α → (ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site)) :
    hilbertTrace (∑ a ∈ s, f a) = ∑ a ∈ s, hilbertTrace (f a) := by
  unfold hilbertTrace; rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun ψ _ => ?_; rw [ContinuousLinearMap.sum_apply, inner_sum, map_sum]

/-- Trace of `X * rankOneKetBra φ` equals $\operatorname{Re}\langle \varphi, X \varphi \rangle$. -/
lemma hilbertTrace_mul_rankOneKetBra {D L : ℕ} {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    (X : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site) (φ : ManyBodyHilbertSpace Site) :
    hilbertTrace (X * rankOneKetBra φ) = RCLike.re (inner ℂ φ (X φ)) := by
  unfold hilbertTrace
  have h_term : ∀ ψ : ManyBodyConfig Site,
      inner ℂ (basisVecGlobal Site ψ) ((X * rankOneKetBra φ) (basisVecGlobal Site ψ)) =
        inner ℂ φ (((X φ).ofLp ψ) • basisVecGlobal Site ψ) := by
    intro ψ; change inner ℂ (basisVecGlobal Site ψ) (X (rankOneKetBra φ (basisVecGlobal Site ψ))) = _
    rw [rankOneKetBra_apply, map_smul, inner_smul_right, inner_smul_right, inner_basisVecGlobal_left_aux ψ (X φ), mul_comm]
  simp_rw [h_term]; rw [← map_sum, ← inner_sum, ← eq_sum_basisVecGlobal_aux (X φ)]

private def opOrthonormalBasis {D L : ℕ} {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    (H : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site) (hH : IsSelfAdjoint H) :
    OrthonormalBasis (ManyBodyConfig Site) ℂ (ManyBodyHilbertSpace Site) :=
  (sortedEigenbasis H hH).reindex (configFinEquiv Site).symm

private lemma opOrthonormalBasis_apply {D L : ℕ} {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    (H : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site) (hH : IsSelfAdjoint H) (ω : ManyBodyConfig Site) :
    opOrthonormalBasis H hH ω = opEigenbasis H hH ω := by
  dsimp [opOrthonormalBasis, opEigenbasis]; rw [OrthonormalBasis.reindex_apply, Equiv.symm_symm]

/-- `opEigenbasis H hH` is an orthonormal family on `ManyBodyHilbertSpace Site`. -/
lemma opEigenbasis_orthonormal {D L : ℕ} {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    (H : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site) (hH : IsSelfAdjoint H) (ω₁ ω₂ : ManyBodyConfig Site) :
    inner ℂ (opEigenbasis H hH ω₁) (opEigenbasis H hH ω₂) = if ω₁ = ω₂ then (1 : ℂ) else 0 := by
  rw [← opOrthonormalBasis_apply H hH ω₁, ← opOrthonormalBasis_apply H hH ω₂]
  exact orthonormal_iff_ite.mp (opOrthonormalBasis H hH).orthonormal ω₁ ω₂

/-- Parseval's identity for `opEigenbasis H hH` on `ManyBodyHilbertSpace Site`. -/
lemma opEigenbasis_parseval {D L : ℕ} {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    (H : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site) (hH : IsSelfAdjoint H) (φ : ManyBodyHilbertSpace Site) :
    (∑ ω : ManyBodyConfig Site, ‖inner ℂ (opEigenbasis H hH ω) φ‖ ^ 2) = ‖φ‖ ^ 2 := by
  simp_rw [← opOrthonormalBasis_apply H hH]; exact (opOrthonormalBasis H hH).sum_sq_norm_inner_right φ

/-- Basis-invariance of `hilbertTrace` with respect to `opEigenbasis H hH`. -/
lemma hilbertTrace_eq_sum_opEigenbasis {D L : ℕ} {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    (H : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site) (hH : IsSelfAdjoint H)
    (X : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site) :
    hilbertTrace X = ∑ ω : ManyBodyConfig Site, RCLike.re (inner ℂ (opEigenbasis H hH ω) (X (opEigenbasis H hH ω))) := by
  have h_id := onb_sum_ketBra_eq_one (opEigenbasis H hH) (opEigenbasis_orthonormal H hH) (opEigenbasis_parseval H hH)
  calc hilbertTrace X
    _ = hilbertTrace (X * 1) := by rw [mul_one]
    _ = hilbertTrace (X * ∑ ω : ManyBodyConfig Site, rankOneKetBra (opEigenbasis H hH ω)) := by rw [h_id]
    _ = ∑ ω : ManyBodyConfig Site, hilbertTrace (X * rankOneKetBra (opEigenbasis H hH ω)) := by rw [Finset.mul_sum, hilbertTrace_sum]
    _ = ∑ ω : ManyBodyConfig Site, RCLike.re (inner ℂ (opEigenbasis H hH ω) (X (opEigenbasis H hH ω))) := by
      refine Finset.sum_congr rfl fun ω _ => hilbertTrace_mul_rankOneKetBra X (opEigenbasis H hH ω)

/-- Left/right eigenvalue identities and trace cyclicity for `rankOneKetBra (opEigenbasis H hH ω)`. -/
lemma opEigenbasis_ketBra_props {D L : ℕ} {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    (H : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site) (hH : IsSelfAdjoint H) (ω : ManyBodyConfig Site) :
    H * rankOneKetBra (opEigenbasis H hH ω) = (opEigenvalues H hH ω : ℂ) • rankOneKetBra (opEigenbasis H hH ω) ∧
    rankOneKetBra (opEigenbasis H hH ω) * H = (opEigenvalues H hH ω : ℂ) • rankOneKetBra (opEigenbasis H hH ω) ∧
    ∀ A : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site,
      hilbertTrace (rankOneKetBra (opEigenbasis H hH ω) * A) = hilbertTrace (A * rankOneKetBra (opEigenbasis H hH ω)) := by
  refine ⟨?_, ?_, fun A => hilbertTrace_mul_comm_aux _ A⟩
  · apply ContinuousLinearMap.ext; intro φ
    change H (rankOneKetBra (opEigenbasis H hH ω) φ) = _
    rw [rankOneKetBra_apply, map_smul, opEigenbasis_apply_H H hH ω,
      ContinuousLinearMap.smul_apply, rankOneKetBra_apply, smul_smul, smul_smul, mul_comm]
  · have hH_adj : H† = H := ContinuousLinearMap.isSelfAdjoint_iff'.mp hH
    apply ContinuousLinearMap.ext; intro φ
    change rankOneKetBra (opEigenbasis H hH ω) (H φ) = _
    rw [rankOneKetBra_apply, ← ContinuousLinearMap.adjoint_inner_left, hH_adj,
      opEigenbasis_apply_H H hH ω, inner_smul_left, Complex.conj_ofReal,
      ContinuousLinearMap.smul_apply, rankOneKetBra_apply, smul_smul]

end
