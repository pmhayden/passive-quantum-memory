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

import Defs.BHMStability
import Defs.KMSAndGibbs
import Defs.PolymerGas

/-!
# Bare Syndrome Projectors, Decoded Logical Observables, and Two-Sided Safe-Subspace Immunity

Defines bare check-syndrome and decoder-failure projectors (`SyndromeConfig`, `bareSyndromeProjector`, `bareFailureProjector`, `IndexedSyndromeConfig`, `indexedBareFailureProjector`), the dressed free-energy barrier expression (`dressedThermalFreeEnergyBarrier`), and bare homology-decoded logical observables (`bareDecodedLogicalOp`). Formalizes two-sided safe-subspace operator immunity (`SatisfiesTwoSidedOperatorImmunity`), local coboundary discrepancy invariance (`PreservesDecoderDiscrepancy`), and the regularized KMS Grönwall comparison function (`kmsCompFunc`).

## References

* Part I, Section 5.4 (`subsec:safe-decoded-observables`), Definition 5.6 (`def:safe-decoded-observables`), Proposition 5.7 (`prop:safe-subspace-immunity`), Section 5.5 (`subsec:unperturbed-kms-lifetime`), Theorem 5.8 (`thm:unperturbed-kms-lifetime`)
* Part II, Section 2 (`subsec:setup`), Definition 2.5 (`def:syndrome-safe`), Section 6 (`sec:lindblad`), Lemma 6.1 (`lem:kms-fourth-root`), Section 6.2 (`subsec:kms-gronwall`), Theorem 6.2 (`thm:kms-gronwall-bare`)
-/

noncomputable section

open scoped Classical InnerProduct ComplexConjugate BigOperators
open Filter Topology Asymptotics ContinuousLinearMap

/-!
## 1. Bare Syndrome and Decoder-Failure Projectors
-/

/-- Binary check-syndrome configuration $\sigma : \mathcal{S}(2) \to \mathrm{Bool}$ on open-box cubes. -/
abbrev SyndromeConfig (D L : ℕ) : Type :=
  Finset (BoxD D L) → Bool

/-- Simultaneous bare syndrome sector projector
    $\Pi_\sigma := \prod_{K \in \mathcal{S}(2)} (\text{if }\sigma(K)\text{ then }Q_K\text{ else }(I - Q_K))$. -/
def bareSyndromeProjector {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    (sys : CommutingProjectorHamiltonian D L Site) (σ : SyndromeConfig D L) :
    ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site :=
  (((boxCubes D L 2).toList.map (fun K => if σ K then sys.Q K else 1 - sys.Q K))).prod

/-- Total bare decoder-failure projector $\Pi_{\mathrm{fail}} := \sum_{\sigma \in \mathcal{F}_{\mathrm{fail}}} \Pi_\sigma$. -/
def bareFailureProjector {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    (sys : CommutingProjectorHamiltonian D L Site)
    (F_fail : Finset (SyndromeConfig D L)) :
    ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site :=
  ∑ σ ∈ F_fail, bareSyndromeProjector sys σ

/-- Dressed macroscopic free-energy barrier $\Delta F_m^{\mathrm{dress}}(\beta) := c'_F (\frac{3}{4}\beta - \beta_c) |\Lambda|^\eta - C_0$. -/
def dressedThermalFreeEnergyBarrier (c_F' β β_c N_Q η C_0 : ℝ) : ℝ :=
  c_F' * ((3 / 4 : ℝ) * β - β_c) * (N_Q ^ η) - C_0

/-!
## 2. Bare Decoded Logical Observables and Two-Sided Safe-Subspace Immunity
-/

/-- Bare homology-decoded logical observable
    $O_{\mathrm{dec}}^{(0)} := \overline{L} \sum_{\sigma \in S_{\mathrm{real}}} (-1)^{\psi_{\mathrm{dec}}(\sigma)} \Pi_\sigma$
    (Part I, Definition 5.6 (`def:safe-decoded-observables`), Equation (54) (`eq:decoded-observables-def`);
    Part II, Definition 2.5 (`def:syndrome-safe`)). -/
def bareDecodedLogicalOp {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    (sys : CommutingProjectorHamiltonian D L Site)
    (S_real : Finset (SyndromeConfig D L))
    (L_bare : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site)
    (ψ_dec : SyndromeConfig D L → Bool) :
    ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site :=
  L_bare * ∑ σ ∈ S_real,
    ((if ψ_dec σ then (-1 : ℂ) else (1 : ℂ)) • bareSyndromeProjector sys σ)

/-- **Two-Sided Safe-Subspace Operator Immunity Identity (Part I, Proposition 5.7 (`prop:safe-subspace-immunity`), Equation (55) (`eq:safe-subspace-immunity`); Part II, Section 6 (`sec:lindblad`), Lemma 6.1 (`lem:kms-fourth-root`), Equation (89) (`eq:commutator-unsafe-decomposition`))**:
    1. $(I - \Pi_{\mathrm{fail}})[A, O](I - \Pi_{\mathrm{fail}}) = 0$;
    2. $[A, O] = \Pi_{\mathrm{fail}}[A, O] + (I - \Pi_{\mathrm{fail}})[A, O]\Pi_{\mathrm{fail}}$. -/
def SatisfiesTwoSidedOperatorImmunity {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    (sys : CommutingProjectorHamiltonian D L Site)
    (F_fail : Finset (SyndromeConfig D L))
    (O A : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site) : Prop :=
  let P_fail := bareFailureProjector sys F_fail
  let comm := opCommutator A O
  (1 - P_fail) * comm * (1 - P_fail) = 0 ∧
  comm = P_fail * comm + (1 - P_fail) * comm * P_fail

/-- **Local Coboundary Discrepancy Invariance Outside $F_{\mathrm{fail}}$
    (Part I, Proposition 5.3 (`prop:cluster-decoder-witness`), Equation (43) (`eq:local-pairing-invariance`),
    and Proposition 5.7 (`prop:safe-subspace-immunity`))**. -/
def PreservesDecoderDiscrepancy {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    (sys : CommutingProjectorHamiltonian D L Site)
    (S_real F_fail : Finset (SyndromeConfig D L))
    (L_bare : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site)
    (ψ_dec : SyndromeConfig D L → Bool)
    (A : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site) : Prop :=
  ∃ b_L : Bool,
    L_bare * A = ((if b_L then (-1 : ℂ) else (1 : ℂ)) • A) * L_bare ∧
    ∀ σ₁ ∈ S_real \ F_fail, ∀ σ₂ ∈ S_real \ F_fail,
      bareSyndromeProjector sys σ₁ * A * bareSyndromeProjector sys σ₂ = 0 ∨
      Bool.xor (ψ_dec σ₁) (ψ_dec σ₂) = b_L

/-!
## 3. Indexed Check-Syndrome Counterparts
-/

/-- Binary syndrome configuration $\sigma : \iota \to \mathrm{Bool}$ for an arbitrary check index type `ι`. -/
abbrev IndexedSyndromeConfig (ι : Type) : Type := ι → Bool

/-- Total bare decoder-failure projector $\Pi_{\mathrm{fail}} = \sum_{\sigma \in F_{\mathrm{fail}}} \Pi_{\mathrm{syn}}(\sigma)$
    for an `IndexedCommutingProjectorHamiltonian`. -/
def indexedBareFailureProjector {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (sys : IndexedCommutingProjectorHamiltonian D L Site ι)
    (F_fail : Finset (IndexedSyndromeConfig ι)) :
    ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site :=
  ∑ σ ∈ F_fail, sys.syndromeProjector σ

/-!
## 4. KMS Grönwall Comparison Function
-/

/-- **KMS ODE Comparison Function $g_\delta(s) := (\Gamma_{\mathrm{coh}} s + \sqrt{\frac{1}{2}\Gamma_{\mathrm{diss}} s + \delta^2})^2$ (Part II, Section 6.2 (`subsec:kms-gronwall`), Theorem 6.2 (`thm:kms-gronwall-bare`), Equation (90) (`eq:gronwall-sqrt-drift`))**. -/
def kmsCompFunc (Γ_coh Γ_diss δ s : ℝ) : ℝ :=
  (Γ_coh * s + Real.sqrt ((1 / 2 : ℝ) * Γ_diss * s + δ ^ 2)) ^ 2

end
