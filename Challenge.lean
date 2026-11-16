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

import Defs.BoxLattice
import Defs.ManyBodyHilbert
import Defs.LocalHamiltonian
import Defs.KMSAndGibbs
import Defs.SuperpolyDecay
import Defs.FlowAndFilter

/-!
# Main Theorems: Thermally and Perturbatively Stable 3D Passive Quantum Memory

States the standalone top-level problem predicates and the two main existence theorems (`part1_thermally_and_perturbatively_stable_memory` and `part2_fixed_temp_perturbative_thermal_and_kms_stability`) for a 3D open-box commuting-projector quantum memory. Formalizes safe decoded logical observables (`HasSafeDecodedLogicalObservables`), unperturbed Gibbs and KMS-Lindblad thermal self-correction (`SatisfiesUnperturbedThermalAndKMSStability`), zero-temperature perturbative spectral and Heisenberg stability (`SatisfiesZeroTempPerturbativeMemoryStability`), and fixed-temperature perturbative thermal and KMS-Lindblad memory lifetimes (`SatisfiesFixedTempPerturbativeThermalAndKMSStability`).

## References

* Part I, Section 5.4 (`subsec:safe-decoded-observables`), Definition 5.6 (`def:safe-decoded-observables`), Section 5.5 (`subsec:unperturbed-kms-lifetime`), Theorem 5.8 (`thm:unperturbed-kms-lifetime`)
* Part I, Section 7.3 (`subsec:zero-temp-dressed-memory`), Theorem 7.4 (`thm:zero-temp-dressed-memory`)
* Part I, Section 7.4 (`subsec:main-theorem-synthesis`), Theorem 7.5 (`thm:main`)
* Part II, Section 6.3 (`subsec:main-theorems`), Theorem 6.3 (`thm:main-A`), Theorem 6.4 (`thm:main-B`), Theorem 6.5 (`thm:main-D`)
-/

noncomputable section

open scoped Classical BigOperators InnerProduct ComplexConjugate
open ContinuousLinearMap

namespace PassiveQuantumMemory

/-!
## 1. Local Notation for 3D Open-Box Hilbert Spaces, Operators, Hamiltonians, Perturbations, and Baths

- `ℋ[L, Site0]` : many-body Hilbert space $\mathcal{H}_{L,\mathrm{Site}_0} = \bigotimes_{v \in \mathrm{Box3D}(L)} \mathbb{C}^{\mathrm{Site}_0}$
- `ℬ[L, Site0]` : bounded linear operators $\mathcal{B}(\mathcal{H}_{L,\mathrm{Site}_0})$
- `ℋ_CP[L, Site0, N_checks]` : 3D commuting-projector Hamiltonian on $\mathrm{Box3D}(L)$ with unit-cell alphabet $\mathrm{Site}_0$ and $N_{\mathrm{checks}}$ checks
- `𝒱_pert[L, Site0]` : quasi-local perturbation on $\mathcal{H}_{L,\mathrm{Site}_0}$
- `ℬ_bath[L, Site0]` : Markovian bath jump channel on $\mathcal{H}_{L,\mathrm{Site}_0}$
-/

local notation "ℋ[" L ", " Site0 "]" => ManyBodyHilbertSpace (UniformSite3D L Site0)
local notation "ℬ[" L ", " Site0 "]" => ℋ[L, Site0] →L[ℂ] ℋ[L, Site0]
local notation "ℋ_CP[" L ", " Site0 ", " N_checks "]" =>
  IndexedCommutingProjectorHamiltonian 3 L (UniformSite3D L Site0) (Fin N_checks)
local notation "𝒱_pert[" L ", " Site0 "]" => QuasiLocalPerturbation 3 L (UniformSite3D L Site0)
local notation "ℬ_bath[" L ", " Site0 "]" => BathChannel 3 L (UniformSite3D L Site0)

/-!
## 2. Helper Predicates for Thermally and Perturbatively Stable Commuting-Projector Memories
-/

/-- **Strictly Increasing Open-Box Scale Sequence (`IsStrictlyIncreasingBoxSequence`)**:
    $L_k \ge k + 2$ and $L_k < L_{k+1}$ for all $k \in \mathbb{N}$. -/
abbrev IsStrictlyIncreasingBoxSequence (L : ℕ → ℕ) : Prop :=
  ∀ k : ℕ, k + 2 ≤ L k ∧ L k < L (k + 1)

/-- **Decoded Logical Observables and Macroscopic Safe-Subspace Logical Immunity
    (`HasSafeDecodedLogicalObservables`)**:
    The frustration-free ground space $P_0$ is non-trivial (`sys.P0 ≠ 0 ∧ sys.P0 ≠ 1` with
    `2 ≤ sys.groundDegeneracy`), and there exist an orthogonal safe-subspace projector
    $\Pi_{\mathrm{safe}}$ commuting with $H_0$ and all check projectors `sys.checkProj i`
    (containing the ground space $P_0$) and Hermitian unitary decoded logical observables
    $O_{\mathrm{dec}}^Z, O_{\mathrm{dec}}^X$ commuting with $H_0$, $P_0$, $\Pi_{\mathrm{safe}}$, and
    all check projectors `sys.checkProj i` such that:
    1. $O_{\mathrm{dec}}^Z$ and $O_{\mathrm{dec}}^X$ preserve $\Pi_{\mathrm{safe}}$ and anticommute
       nontrivially on $\Pi_{\mathrm{safe}}$ (and hence on $P_0 \le \Pi_{\mathrm{safe}}$);
    2. **Macroscopic cube safe-subspace logical immunity**: for every site $v \in \mathrm{Box3D}(L)$
       and every operator $M_A$ supported on a cube $A \in \mathcal{S}(r)$ of side
       $1 \le r \le \min(R_{\mathrm{imm}}, L)$,
       $\Pi_{\mathrm{safe}} [M_A, O_{\mathrm{dec}}^{Z/X}] \Pi_{\mathrm{safe}} = 0$. -/
abbrev HasSafeDecodedLogicalObservables
    {L N_checks : ℕ} [NeZero L]
    {Site0 : Type} [Fintype Site0] [DecidableEq Site0]
    (sys : ℋ_CP[L, Site0, N_checks])
    (Pi_safe O_dec_Z O_dec_X : ℬ[L, Site0])
    (R_imm : ℕ) : Prop :=
  -- Nontrivial frustration-free ground space of degeneracy ≥ 2 (encoding ≥ 1 logical qubit)
  sys.P0 ≠ 0 ∧ sys.P0 ≠ 1 ∧ 2 ≤ sys.groundDegeneracy ∧
  -- Safe-subspace projector properties
  IsStarProjection Pi_safe ∧ Pi_safe ≠ 0 ∧ Pi_safe ≠ 1 ∧
  Commute sys.H0 Pi_safe ∧ sys.P0 * Pi_safe = sys.P0 ∧
  -- Decoded logical Z and X observables: Hermitian, unitary involutions commuting with H0, P0, and Pi_safe
  IsSelfAdjoint O_dec_Z ∧ O_dec_Z * O_dec_Z = 1 ∧ ‖O_dec_Z‖ ≤ 1 ∧
  Commute sys.H0 O_dec_Z ∧ Commute sys.P0 O_dec_Z ∧ Commute Pi_safe O_dec_Z ∧
  IsSelfAdjoint O_dec_X ∧ O_dec_X * O_dec_X = 1 ∧ ‖O_dec_X‖ ≤ 1 ∧
  Commute sys.H0 O_dec_X ∧ Commute sys.P0 O_dec_X ∧ Commute Pi_safe O_dec_X ∧
  -- Check-by-check syndrome commutativity of Pi_safe, O_dec_Z, and O_dec_X
  (∀ i : Fin N_checks,
    Commute (sys.checkProj i) Pi_safe ∧
    Commute (sys.checkProj i) O_dec_Z ∧
    Commute (sys.checkProj i) O_dec_X) ∧
  -- Nontrivial anticommutation on the safe subspace (and ground space)
  Pi_safe * O_dec_Z * O_dec_X * Pi_safe = -(Pi_safe * O_dec_X * O_dec_Z * Pi_safe) ∧
  O_dec_Z * sys.P0 ≠ 0 ∧ O_dec_X * sys.P0 ≠ 0 ∧
  -- Safe-subspace single-site logical immunity
  (∀ (v : Box3D L) (A_v : ℬ[L, Site0]),
    IsSupportedOn (UniformSite3D L Site0) {v} A_v →
    Pi_safe * (A_v * O_dec_Z - O_dec_Z * A_v) * Pi_safe = 0 ∧
    Pi_safe * (A_v * O_dec_X - O_dec_X * A_v) * Pi_safe = 0) ∧
  -- Macroscopic cube safe-subspace logical immunity up to side R_imm
  (∀ r ∈ Finset.Icc 1 (min R_imm L), ∀ A ∈ boxCubes 3 L r, ∀ M_A : ℬ[L, Site0],
    IsSupportedOn (UniformSite3D L Site0) A M_A →
    Pi_safe * (M_A * O_dec_Z - O_dec_Z * M_A) * Pi_safe = 0 ∧
    Pi_safe * (M_A * O_dec_X - O_dec_X * M_A) * Pi_safe = 0)

/-- **Quasi-Local Dressing Unitary (`IsQuasiLocalUnitary`)**:
    A unitary operator `U_dress` on $\mathcal{H}_{L,\mathrm{Site}_0}$ is quasi-local with spatial
    tail profile `g_dress : ℕ → ℝ` if conjugating any single-site operator $A_v$ supported at site
    $v \in \mathrm{Box3D}(L)$ remains concentrated in the ball `boxBall v r` of radius $r$ around $v$
    up to an approximation error bounded by $\|A_v\| \, g_{\mathrm{dress}}(r)$:
    $$\|U_{\mathrm{dress}}^\dagger A_v U_{\mathrm{dress}} -
      \mathbb{E}_{B(v, r)}(U_{\mathrm{dress}}^\dagger A_v U_{\mathrm{dress}})\|
      \le \|A_v\| \, g_{\mathrm{dress}}(r).$$ -/
abbrev IsQuasiLocalUnitary {L : ℕ}
    {Site0 : Type} [Fintype Site0] [DecidableEq Site0]
    (U_dress : unitary ℬ[L, Site0]) (g_dress : ℕ → ℝ) : Prop :=
  ∀ (v : Box3D L) (A_v : ℬ[L, Site0]),
    IsSupportedOn (UniformSite3D L Site0) {v} A_v →
    ∀ r : ℕ,
      ‖U_dress.1† * A_v * U_dress.1 -
        condExp (UniformSite3D L Site0) (boxBall v r) (U_dress.1† * A_v * U_dress.1)‖ ≤
        ‖A_v‖ * g_dress r

/-- **Finite-Range Perturbation Bound (`HasFiniteRangeBound V R_pert J`)**:
    Every interaction term $V_{r,A}$ of cube side length $1 \le r \le R_{\mathrm{pert}}$ has
    operator norm $\|V_{r,A}\| \le J$, and all interaction terms of range $r > R_{\mathrm{pert}}$
    vanish ($V_{r,A} = 0$). -/
abbrev HasFiniteRangeBound
    {L : ℕ} {Site0 : Type} [Fintype Site0] [DecidableEq Site0]
    (V : 𝒱_pert[L, Site0]) (R_pert : ℕ) (J : ℝ) : Prop :=
  ∀ r ∈ Finset.Icc 1 L, ∀ A ∈ boxCubes 3 L r,
    (r ≤ R_pert → ‖V.term r A‖ ≤ J) ∧
    (R_pert < r → V.term r A = 0)

/-- **Macroscopic Equilibrium Peierls Free-Energy Barrier and Stretched-Exponential KMS / GKLS
    Davies Memory Lifetime (`SatisfiesUnperturbedThermalAndKMSStability`)**
    (Part I, Theorem 5.8(i)–(ii) (`thm:unperturbed-kms-lifetime`); Part II, Theorem 6.5(1) (`thm:main-D`)). -/
abbrev SatisfiesUnperturbedThermalAndKMSStability
    {L N_checks : ℕ} [NeZero L]
    {Site0 : Type} [Fintype Site0] [DecidableEq Site0]
    (sys : ℋ_CP[L, Site0, N_checks])
    (Pi_safe O_dec_Z O_dec_X : ℬ[L, Site0])
    (R_imm w_0 : ℕ)
    (β_c c_F η : ℝ) : Prop :=
  ∀ β : ℝ, β > β_c →
    let ΔF := c_F * (β - β_c) * (((L ^ 3 : ℕ) : ℝ) ^ η)
    -- (iii) Macroscopic equilibrium Peierls free-energy barrier
    gibbsFailureProb sys.H0 sys.isSelfAdjoint_H0 β (1 - Pi_safe) ≤ Real.exp (-ΔF) ∧
    -- (iv.a) Cube-range KMS double-commutator bath lifetime + semigroup ODE existence
    (∀ (bath : Finset ℬ_bath[L, Site0]) (O_0 : ℬ[L, Site0]),
      (O_0 = O_dec_Z ∨ O_0 = O_dec_X) →
      IsCubeRangeBath 3 L R_imm bath →
      (IsAdjointSymmetricBath bath →
        ∀ t : ℝ, 0 ≤ t →
          SatisfiesKMSLindbladODE sys.H0 sys.isSelfAdjoint_H0 β bath O_0
            (fun s => opKMSLindbladSemigroup sys.H0 sys.isSelfAdjoint_H0 β bath s O_0) t) ∧
      (∀ (O_t : ℝ → ℬ[L, Site0]) (t : ℝ),
        0 ≤ t →
        SatisfiesKMSLindbladODE sys.H0 sys.isSelfAdjoint_H0 β bath O_0 O_t t →
        opKMSNormSq sys.H0 sys.isSelfAdjoint_H0 β (O_t t - O_0) ≤
          8 * (∑ ch ∈ bath, ch.γ * ‖ch.L‖ ^ 2) * (Real.exp (-ΔF)) ^ (1 / 2 : ℝ) * t)) ∧
    -- (iv.b) Exact CPTP GKLS Davies thermal bath lifetime at V = 0
    (∀ (couplings : Finset (SingleSiteThermalCoupling 3 L (UniformSite3D L Site0) β))
      (O_0 : ℬ[L, Site0]),
      (O_0 = O_dec_Z ∨ O_0 = O_dec_X) →
      (∀ t : ℝ, 0 ≤ t →
        IsCPUnitalStarMap (opDaviesThermalSemigroup sys β couplings t) ∧
        (∀ X : ℬ[L, Site0],
          hilbertTrace (gibbsDensityOp (opEigenbasis sys.H0 sys.isSelfAdjoint_H0)
            (opEigenvalues sys.H0 sys.isSelfAdjoint_H0) β *
              opDaviesThermalSemigroup sys β couplings t X) =
          hilbertTrace (gibbsDensityOp (opEigenbasis sys.H0 sys.isSelfAdjoint_H0)
            (opEigenvalues sys.H0 sys.isSelfAdjoint_H0) β * X)) ∧
        SatisfiesDaviesThermalODE sys β couplings O_0
          (fun s => opDaviesThermalSemigroup sys β couplings s O_0) t) ∧
      (∀ (O_t : ℝ → ℬ[L, Site0]) (t : ℝ),
        0 ≤ t →
        SatisfiesDaviesThermalODE sys β couplings O_0 O_t t →
        opKMSNormSq sys.H0 sys.isSelfAdjoint_H0 β (O_t t - O_0) ≤
          8 * (∑ c ∈ couplings, ∑ ω ∈ Finset.Icc (-(w_0 : ℤ)) (w_0 : ℤ),
            Real.exp (-β * (ω : ℝ) / 2) * c.h_spec ω * ‖bohrEigenop sys c.S ω‖ ^ 2) *
            (Real.exp (-ΔF)) ^ (1 / 2 : ℝ) * t ∧
        opKMSNormSq sys.H0 sys.isSelfAdjoint_H0 β (O_t t - O_0) ≤
          8 * (∑ c ∈ couplings, ∑ ω ∈ Finset.Icc (-(w_0 : ℤ)) (w_0 : ℤ),
            Real.exp (-β * (ω : ℝ) / 2) * c.h_spec ω * ‖c.S‖ ^ 2) *
            (Real.exp (-ΔF)) ^ (1 / 2 : ℝ) * t))

/-- **Zero-Temperature Perturbative Full-Spectrum, Safe-Subspace, and Dynamical Memory Stability
    (`SatisfiesZeroTempPerturbativeMemoryStability`)**. -/
abbrev SatisfiesZeroTempPerturbativeMemoryStability
    {L N_checks : ℕ} [NeZero L]
    {Site0 : Type} [Fintype Site0] [DecidableEq Site0]
    (sys : ℋ_CP[L, Site0, N_checks])
    (Pi_safe O_dec_Z O_dec_X : ℬ[L, Site0])
    (V : 𝒱_pert[L, Site0])
    (R_bath : ℕ)
    (δ_split : ℝ)
    (g_LR : ℕ → ℝ) : Prop :=
  let H := sys.H0 + V.totalPerturbation
  ∃ (U_dress : unitary ℬ[L, Site0]) (E0 : ℝ),
    let P0_dress := U_dress.1 * sys.P0 * U_dress.1†
    let Pi_safe_dress := U_dress.1 * Pi_safe * U_dress.1†
    IsQuasiLocalUnitary U_dress g_LR ∧
    ‖H * P0_dress - P0_dress * H‖ ≤ δ_split ∧
    ‖P0_dress * (H - (E0 : ℂ) • 1) * P0_dress‖ ≤ δ_split ∧
    (∀ ψ : ℋ[L, Site0],
      |RCLike.re (inner ℂ ψ
          ((U_dress.1† * H * U_dress.1 - sys.H0 - (E0 : ℂ) • 1) ψ))| ≤
        (1 / 4 : ℝ) * RCLike.re (inner ℂ ψ (sys.H0 ψ)) + (δ_split / 2) * ‖ψ‖ ^ 2) ∧
    ∀ O_0 : ℬ[L, Site0], (O_0 = O_dec_Z ∨ O_0 = O_dec_X) →
      let O_dress := U_dress.1 * O_0 * U_dress.1†
      ‖Pi_safe_dress * (H * O_dress - O_dress * H) * Pi_safe_dress‖ ≤ δ_split ∧
      (∀ (v : Box3D L) (A_v : ℬ[L, Site0]),
        IsSupportedOn (UniformSite3D L Site0) {v} A_v →
        ‖Pi_safe_dress * (A_v * O_dress - O_dress * A_v) * Pi_safe_dress‖ ≤ δ_split * ‖A_v‖) ∧
      (∀ r ∈ Finset.Icc 1 (min R_bath L), ∀ W ∈ boxCubes 3 L r, ∀ M_W : ℬ[L, Site0],
        IsSupportedOn (UniformSite3D L Site0) W M_W →
        ‖Pi_safe_dress * (M_W * O_dress - O_dress * M_W) * Pi_safe_dress‖ ≤ δ_split * ‖M_W‖) ∧
      (∀ t : ℝ, 0 ≤ t →
        ‖(heisenbergFlow H t O_dress - O_dress) * P0_dress‖ ≤ t * δ_split)

/-- **Fixed-Temperature and Logarithmic-Cooling Perturbative Full-Spectrum, Unpinched Gibbs Failure
    Probability, and KMS Dissipative Dynamical Memory Lifetime Stability
    (`SatisfiesFixedTempPerturbativeThermalAndKMSStability`)**. -/
abbrev SatisfiesFixedTempPerturbativeThermalAndKMSStability
    {L N_checks : ℕ} [NeZero L]
    {Site0 : Type} [Fintype Site0] [DecidableEq Site0]
    (sys : ℋ_CP[L, Site0, N_checks])
    (Pi_safe O_dec_Z O_dec_X : ℬ[L, Site0])
    (V : 𝒱_pert[L, Site0])
    (R_imm R_bath : ℕ)
    (β_c β_max c_F_pert C_scale c_F_dress η δ_split : ℝ)
    (g_LR : ℕ → ℝ) : Prop :=
  let H := sys.H0 + V.totalPerturbation
  ∃ (U_dress : unitary ℬ[L, Site0]) (E0 : ℝ),
    let P0_dress := U_dress.1 * sys.P0 * U_dress.1†
    let Pi_safe_dress := U_dress.1 * Pi_safe * U_dress.1†
    IsQuasiLocalUnitary U_dress g_LR ∧
    ‖H * P0_dress - P0_dress * H‖ ≤ δ_split ∧
    ‖P0_dress * (H - (E0 : ℂ) • 1) * P0_dress‖ ≤ δ_split ∧
    (∀ ψ : ℋ[L, Site0],
      |RCLike.re (inner ℂ ψ
          ((U_dress.1† * H * U_dress.1 - sys.H0 - (E0 : ℂ) • 1) ψ))| ≤
        (1 / 4 : ℝ) * RCLike.re (inner ℂ ψ (sys.H0 ψ)) + (δ_split / 2) * ‖ψ‖ ^ 2) ∧
    (∀ O_0 : ℬ[L, Site0], (O_0 = O_dec_Z ∨ O_0 = O_dec_X) →
      let O_dress := U_dress.1 * O_0 * U_dress.1†
      ‖Pi_safe_dress * (H * O_dress - O_dress * H) * Pi_safe_dress‖ ≤ δ_split ∧
      (∀ (v : Box3D L) (A_v : ℬ[L, Site0]),
        IsSupportedOn (UniformSite3D L Site0) {v} A_v →
        ‖Pi_safe_dress * (A_v * O_dress - O_dress * A_v) * Pi_safe_dress‖ ≤ δ_split * ‖A_v‖) ∧
      (∀ r ∈ Finset.Icc 1 (min R_bath L), ∀ W ∈ boxCubes 3 L r, ∀ M_W : ℬ[L, Site0],
        IsSupportedOn (UniformSite3D L Site0) W M_W →
        ‖Pi_safe_dress * (M_W * O_dress - O_dress * M_W) * Pi_safe_dress‖ ≤ δ_split * ‖M_W‖) ∧
      (∀ t : ℝ, 0 ≤ t →
        ‖(heisenbergFlow H t O_dress - O_dress) * P0_dress‖ ≤ t * δ_split)) ∧
    -- 4. Fixed-temperature window (∀ β ∈ (β_c, β_max])
    (∀ (β : ℝ) (hH : IsSelfAdjoint H),
      β > β_c → β ≤ β_max →
      let ΔF_pert := c_F_pert * min (β - β_c) 1 * (((L ^ 3 : ℕ) : ℝ) ^ η)
      let p_fail := Real.exp (-ΔF_pert)
      gibbsFailureProb H hH β (1 - Pi_safe) ≤ p_fail ∧
      (∀ (L_diss : ℬ[L, Site0] →L[ℂ] ℬ[L, Site0]) (O_0 : ℬ[L, Site0]) (Γ_diss : ℝ),
        (O_0 = O_dec_Z ∨ O_0 = O_dec_X) →
        IsKMSSymmetricDissipativeGenerator H hH β L_diss →
        2 * kmsDissipativeForm H hH β L_diss O_0 O_0 ≤ Γ_diss →
        ∀ (O_t : ℝ → ℬ[L, Site0]) (t : ℝ),
          0 ≤ t →
          SatisfiesKMSDissipativeODE H hH β L_diss O_0 O_t t →
          opKMSNorm H hH β (O_t t - O_0) ≤
            kmsDriftDirichletBound
              (2 * ‖H * O_0 - O_0 * H‖ * (p_fail ^ (1 / 4 : ℝ))) Γ_diss t) ∧
      (∀ (bath : Finset ℬ_bath[L, Site0]) (O_0 : ℬ[L, Site0]),
        (O_0 = O_dec_Z ∨ O_0 = O_dec_X) →
        IsCubeRangeBath 3 L R_imm bath →
        (IsAdjointSymmetricBath bath →
          ∀ t : ℝ, 0 ≤ t →
            SatisfiesKMSLindbladODE H hH β bath O_0
              (fun s => opKMSLindbladSemigroup H hH β bath s O_0) t) ∧
        (∀ (O_t : ℝ → ℬ[L, Site0]) (t : ℝ),
          0 ≤ t →
          SatisfiesKMSLindbladODE H hH β bath O_0 O_t t →
          opKMSNorm H hH β (O_t t - O_0) ≤
            kmsDriftDirichletBound
              (2 * ‖H * O_0 - O_0 * H‖ * (p_fail ^ (1 / 4 : ℝ)))
              (16 * (∑ ch ∈ bath, ch.γ * ‖ch.L‖ ^ 2) * (p_fail ^ (1 / 2 : ℝ)))
              t))) ∧
    -- 5. Logarithmic-cooling / cryogenic QAC-dressed regime (∀ β ≥ C_scale * log L)
    (∀ (β : ℝ) (hH : IsSelfAdjoint H),
      C_scale * Real.log (L : ℝ) ≤ β →
      let p_log := ((L ^ 3 : ℕ) : ℝ) * Real.exp (-c_F_dress * β) + δ_split
      gibbsFailureProb H hH β (1 - Pi_safe_dress) ≤ p_log ∧
      (∀ (L_diss : ℬ[L, Site0] →L[ℂ] ℬ[L, Site0]) (O_0 : ℬ[L, Site0]) (Γ_diss : ℝ),
        (O_0 = O_dec_Z ∨ O_0 = O_dec_X) →
        let O_dress := U_dress.1 * O_0 * U_dress.1†
        IsKMSSymmetricDissipativeGenerator H hH β L_diss →
        2 * kmsDissipativeForm H hH β L_diss O_dress O_dress ≤ Γ_diss →
        ∀ (O_t : ℝ → ℬ[L, Site0]) (t : ℝ),
          0 ≤ t →
          SatisfiesKMSDissipativeODE H hH β L_diss O_dress O_t t →
          opKMSNorm H hH β (O_t t - O_dress) ≤
            kmsDriftDirichletBound
              (2 * ‖H * O_dress - O_dress * H‖ * (p_log ^ (1 / 4 : ℝ)) + δ_split) Γ_diss t) ∧
      (∀ (bath : Finset ℬ_bath[L, Site0]) (O_0 : ℬ[L, Site0]),
        (O_0 = O_dec_Z ∨ O_0 = O_dec_X) →
        IsCubeRangeBath 3 L R_bath bath →
        let O_dress := U_dress.1 * O_0 * U_dress.1†
        (IsAdjointSymmetricBath bath →
          ∀ t : ℝ, 0 ≤ t →
            SatisfiesKMSLindbladODE H hH β bath O_dress
              (fun s => opKMSLindbladSemigroup H hH β bath s O_dress) t) ∧
        (∀ (O_t : ℝ → ℬ[L, Site0]) (t : ℝ),
          0 ≤ t →
          SatisfiesKMSLindbladODE H hH β bath O_dress O_t t →
          opKMSNorm H hH β (O_t t - O_dress) ≤
            kmsDriftDirichletBound
              (2 * ‖H * O_dress - O_dress * H‖ * (p_log ^ (1 / 4 : ℝ)) + δ_split)
              ((∑ ch ∈ bath, ch.γ * ‖ch.L‖ ^ 2) * (16 * (p_log ^ (1 / 2 : ℝ)) + δ_split))
              t)))

/-!
## 3. Main Theorems (Part I and Part II)
-/

/-- **Part I Main Theorem (`part1_thermally_and_perturbatively_stable_memory`; Part I, Section 7.4 (`subsec:main-theorem-synthesis`), Theorem 7.5 (`thm:main`))**:
    Simultaneous finite-temperature unperturbed thermal & KMS / GKLS Davies stability and
    zero-temperature superpolynomial perturbative & dynamical memory stability. -/
theorem part1_thermally_and_perturbatively_stable_memory :
    ∃ (d_loc r_0 w_0 Λ_scale : ℕ)
      (β_c c_F η : ℝ)
      (L N_checks : ℕ → ℕ)
      (_ : ∀ k : ℕ, NeZero (L k))
      (_ : NeZero d_loc)
      (sys : ∀ k : ℕ, ℋ_CP[L k, Fin d_loc, N_checks k])
      (Pi_safe O_dec_Z O_dec_X : ∀ k : ℕ, ℬ[L k, Fin d_loc]),
      2 ≤ d_loc ∧ 1 ≤ r_0 ∧ 1 ≤ w_0 ∧ 2 ≤ Λ_scale ∧
      0 < β_c ∧ 0 < c_F ∧ 0 < η ∧
      (∀ k : ℕ, L k = Λ_scale ^ (2 * k + 4)) ∧
      IsStrictlyIncreasingBoxSequence L ∧
      -- 1. Geometric locality and unperturbed thermal / GKLS Davies stability at all scales k
      (∀ k : ℕ,
        (sys k).IsGeometricallyLocal r_0 w_0 ∧
        (∀ i : Fin (N_checks k), (sys k).weight i = 1) ∧
        HasSafeDecodedLogicalObservables (sys k) (Pi_safe k) (O_dec_Z k) (O_dec_X k)
          (37 * Λ_scale ^ k) ∧
        SatisfiesUnperturbedThermalAndKMSStability (sys k)
          (Pi_safe k) (O_dec_Z k) (O_dec_X k) (37 * Λ_scale ^ k) w_0 β_c c_F η) ∧
      -- 2. Zero-temperature superpolynomial perturbative & dynamical memory stability
      (∀ (f : ℕ → ℝ) (R_bath : ℕ),
        IsSuperpolynomialDecay f →
        1 ≤ R_bath →
        ∃ (J_0 : ℝ) (k_0 : ℕ) (δ_split g_LR : ℕ → ℝ),
          0 < J_0 ∧
          IsSuperpolynomialDecay δ_split ∧
          IsSuperpolynomialDecay g_LR ∧
          ∀ (k : ℕ), k_0 ≤ k →
            ∀ (J : ℝ), 0 ≤ J → J ≤ J_0 →
              ∀ (V : 𝒱_pert[L k, Fin d_loc]),
                V.SatisfiesDecayBound J f →
                SatisfiesZeroTempPerturbativeMemoryStability
                  (sys k) (Pi_safe k) (O_dec_Z k) (O_dec_X k)
                  V R_bath (δ_split (L k)) g_LR) := by
  sorry

/-- **Part II Main Theorem (`part2_fixed_temp_perturbative_thermal_and_kms_stability`; Part II, Section 6.3 (`subsec:main-theorems`), Theorems 6.3, 6.4, and 6.5 (`thm:main-A`, `thm:main-B`, `thm:main-D`))**:
    Fixed-temperature window (`β ∈ (β_c, β_max]` for any `β_max > β_c`) and logarithmic-cooling
    unpinched Gibbs failure probability and KMS dissipative dynamical memory lifetime bounds under
    general finite-range perturbations at constant $O(1)$ coupling. -/
theorem part2_fixed_temp_perturbative_thermal_and_kms_stability :
    ∃ (d_loc r_0 w_0 Λ_scale : ℕ)
      (β_c c_F c_F_pert C_scale c_F_dress η : ℝ)
      (L N_checks : ℕ → ℕ)
      (_ : ∀ k : ℕ, NeZero (L k))
      (_ : NeZero d_loc)
      (sys : ∀ k : ℕ, ℋ_CP[L k, Fin d_loc, N_checks k])
      (Pi_safe O_dec_Z O_dec_X : ∀ k : ℕ, ℬ[L k, Fin d_loc]),
      2 ≤ d_loc ∧ 1 ≤ r_0 ∧ 1 ≤ w_0 ∧ 2 ≤ Λ_scale ∧
      0 < β_c ∧ 0 < c_F ∧ 0 < c_F_pert ∧ 0 < C_scale ∧ 0 < c_F_dress ∧ 0 < η ∧
      (∀ k : ℕ, L k = Λ_scale ^ (2 * k + 4)) ∧
      IsStrictlyIncreasingBoxSequence L ∧
      -- 1. Geometric locality and unperturbed thermal / GKLS Davies stability at all scales k
      (∀ k : ℕ,
        (sys k).IsGeometricallyLocal r_0 w_0 ∧
        (∀ i : Fin (N_checks k), (sys k).weight i = 1) ∧
        HasSafeDecodedLogicalObservables (sys k) (Pi_safe k) (O_dec_Z k) (O_dec_X k)
          (37 * Λ_scale ^ k) ∧
        SatisfiesUnperturbedThermalAndKMSStability (sys k)
          (Pi_safe k) (O_dec_Z k) (O_dec_X k) (37 * Λ_scale ^ k) w_0 β_c c_F η) ∧
      -- 2. Fixed-temperature and logarithmic-cooling unpinched Gibbs & KMS dissipative memory stability
      (∀ (R_pert R_bath : ℕ) (β_max : ℝ),
        1 ≤ R_pert →
        1 ≤ R_bath →
        β_c < β_max →
        ∃ (J_0 : ℝ) (k_0 : ℕ) (δ_split g_LR : ℕ → ℝ),
          0 < J_0 ∧
          IsSuperpolynomialDecay δ_split ∧
          IsSuperpolynomialDecay g_LR ∧
          ∀ (k : ℕ), k_0 ≤ k →
            ∀ (J : ℝ), 0 ≤ J → J ≤ J_0 →
              ∀ (V : 𝒱_pert[L k, Fin d_loc]),
                HasFiniteRangeBound V R_pert J →
                SatisfiesFixedTempPerturbativeThermalAndKMSStability
                  (sys k) (Pi_safe k) (O_dec_Z k) (O_dec_X k)
                  V (37 * Λ_scale ^ k) R_bath
                  β_c β_max c_F_pert C_scale c_F_dress η (δ_split (L k)) g_LR) := by
  sorry

end PassiveQuantumMemory
