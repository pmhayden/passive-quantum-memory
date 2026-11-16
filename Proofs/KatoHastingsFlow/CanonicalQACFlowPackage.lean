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

import Proofs.KatoHastingsFlow.OffDiagProjectorDerivatives

noncomputable section

open scoped Classical InnerProduct ComplexConjugate BigOperators
open Filter Topology Asymptotics ContinuousLinearMap MeasureTheory

/-!
# Unitary Off-Diagonal Covariance and Canonical QAC Flow Package

Proves symmetry-sector commutation along `IsKatoHastingsFlowSystem` (`commute_U_of_isKatoHastingsFlowSystem`, `commute_P_of_isKatoHastingsFlowSystem`) and unitary conjugation covariance of `twoBlockOffDiagProj` (`twoBlockProj_unitary_adj_conj`, `twoBlockOffDiagProj_dressed_bochnerFilteredSiteOp_eq_zero`). Packages the canonical quasi-local QAC flow `qacGeneratorPerturbation`, `qacUnitaryFlow`, and `qacProjectorFlow` in `qac_ode_flow_properties`.

## References

* Part I, Section 6.3 (`subsec:qac-block-diag`), Proposition 6.4 (`prop:qac-block-diagonalization`), Equations (76)–(77) (`eq:Xu-direct-def`, `eq:rotated-H-block-decomp`)
-/

/-!
## 1. General ODE Sector Commutation along `IsKatoHastingsFlowSystem`
-/

/-- **ODE Sector Commutation along `IsKatoHastingsFlowSystem` (`commute_U_of_isKatoHastingsFlowSystem`)**:
    For any `IsKatoHastingsFlowSystem P0 D_gen U P` and any operator $\Pi_{\mathrm{sec}}$, if
    $\mathcal{D}(\tau)$ commutes with $\Pi_{\mathrm{sec}}$ for all $\tau \in \mathbb{R}$, then for all $s \in \mathbb{R}$:
    1. `(U s)† * Pi_sec * U s = Pi_sec`,
    2. `U s * Pi_sec * (U s)† = Pi_sec`,
    3. `Commute (U s) Pi_sec`,
    4. `Commute (U s)† Pi_sec`,
    5. `Commute (katoFlowUnitary hFlow s).1 Pi_sec`. -/
theorem commute_U_of_isKatoHastingsFlowSystem {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    {P0 Pi_sec : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site}
    {D_gen U P : ℝ → (ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site)}
    (hFlow : IsKatoHastingsFlowSystem P0 D_gen U P)
    (hD_sec : ∀ τ : ℝ, Commute (D_gen τ) Pi_sec) (s : ℝ) :
    (U s)† * Pi_sec * U s = Pi_sec ∧
    U s * Pi_sec * (U s)† = Pi_sec ∧
    Commute (U s) Pi_sec ∧
    Commute ((U s)†) Pi_sec ∧
    Commute (katoFlowUnitary hFlow s).1 Pi_sec := by
  have h_deriv_zero : ∀ τ : ℝ, HasDerivAt (fun u => (U u)† * Pi_sec * U u) 0 τ := by
    intro τ
    have hd := (duhamel_conjugation_bound P0 D_gen U P hFlow Pi_sec).1 τ
    have h_comm_zero : Pi_sec * D_gen τ - D_gen τ * Pi_sec = 0 :=
      sub_eq_zero.mpr (hD_sec τ).symm.eq
    rw [h_comm_zero, mul_zero, zero_mul, smul_zero] at hd
    exact hd
  have h_conj_adj : (U s)† * Pi_sec * U s = Pi_sec := by
    rw [eq_of_hasDerivAt_zero h_deriv_zero s, hFlow.U_zero]
    change star (1 : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site) * Pi_sec * 1 = Pi_sec
    rw [star_one, one_mul, mul_one]
  rcases (kato_hastings_ode_flow P0 D_gen U P hFlow).1 s with ⟨hU_adj_U, hU_U_adj⟩
  have h_comm_U : Commute (U s) Pi_sec := by
    rw [commute_iff_eq]
    calc U s * Pi_sec
      _ = U s * ((U s)† * Pi_sec * U s) := by rw [h_conj_adj]
      _ = (U s * (U s)†) * Pi_sec * U s := by simp only [mul_assoc]
      _ = Pi_sec * U s := by rw [hU_U_adj, one_mul]
  have h_conj : U s * Pi_sec * (U s)† = Pi_sec := by
    rw [h_comm_U.eq, mul_assoc, hU_U_adj, mul_one]
  have h_comm_adj : Commute ((U s)†) Pi_sec := by
    rw [commute_iff_eq]
    calc (U s)† * Pi_sec
      _ = (U s)† * (U s * Pi_sec * (U s)†) := by rw [h_conj]
      _ = ((U s)† * U s) * Pi_sec * (U s)† := by simp only [mul_assoc]
      _ = Pi_sec * (U s)† := by rw [hU_adj_U, one_mul]
  exact ⟨h_conj_adj, h_conj, h_comm_U, h_comm_adj, h_comm_U⟩

/-- If `∀ τ, Commute (D_gen τ) Pi_sec` and `Commute P0 Pi_sec`, then `Commute (P s) Pi_sec` for all $s \in \mathbb{R}$. -/
theorem commute_P_of_isKatoHastingsFlowSystem {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    {P0 Pi_sec : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site}
    {D_gen U P : ℝ → (ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site)}
    (hFlow : IsKatoHastingsFlowSystem P0 D_gen U P)
    (hD_sec : ∀ τ : ℝ, Commute (D_gen τ) Pi_sec)
    (hP0_sec : Commute P0 Pi_sec) (s : ℝ) :
    Commute (P s) Pi_sec := by
  have h_abs := kato_hastings_ode_abstract P0 D_gen U P
    hFlow.isSelfAdjoint_D hFlow.U_zero hFlow.P_zero hFlow.hasDerivAt_U hFlow.hasDerivAt_P s
  rcases commute_U_of_isKatoHastingsFlowSystem hFlow hD_sec s with ⟨_, _, hU_sec, hU_adj_sec, _⟩
  rw [← h_abs.2.2.2.2.1]
  exact (hU_sec.mul_left hP0_sec).mul_left hU_adj_sec

/-!
## 2. Unitary Covariance of `twoBlockOffDiagProj`, `twoBlockDiagProj` & Spectral Low-Pass Filtering
-/

/-- Along any `IsKatoHastingsFlowSystem P0 D_gen U P`, `P s = (katoFlowUnitary hFlow s).1 * P0 * (katoFlowUnitary hFlow s).1†`,
    and if `IsStarProjection P0`, then `IsStarProjection (P s)`. -/
theorem isStarProjection_P_of_isKatoHastingsFlowSystem {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    {P0 : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site}
    {D_gen U P : ℝ → (ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site)}
    (hFlow : IsKatoHastingsFlowSystem P0 D_gen U P)
    (hP0 : IsStarProjection P0) (s : ℝ) :
    P s = (katoFlowUnitary hFlow s).1 * P0 * (katoFlowUnitary hFlow s).1† ∧
    IsStarProjection (P s) := by
  have h_abs := kato_hastings_ode_abstract P0 D_gen U P
    hFlow.isSelfAdjoint_D hFlow.U_zero hFlow.P_zero hFlow.hasDerivAt_U hFlow.hasDerivAt_P s
  have hP_eq : P s = (katoFlowUnitary hFlow s).1 * P0 * (katoFlowUnitary hFlow s).1† :=
    h_abs.2.2.2.2.1.symm
  refine ⟨hP_eq, ?_⟩
  rw [hP_eq]
  exact isStarProjection_dressedSafeProjector (katoFlowUnitary hFlow s) hP0

/-- Unitary intertwining of `twoBlockOffDiagProj` and `twoBlockDiagProj`:
    When `P_s = U.1 * P0 * U.1†` for a unitary `U`, for every operator $Y$,
    1. `twoBlockOffDiagProj P0 (U.1† * Y * U.1) = U.1† * (twoBlockOffDiagProj P_s Y) * U.1`,
    2. `twoBlockDiagProj P0 (U.1† * Y * U.1) = U.1† * (twoBlockDiagProj P_s Y) * U.1`. -/
theorem twoBlockProj_unitary_adj_conj {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] [CompleteSpace E]
    (U : unitary (E →L[ℂ] E)) (P0 Y : E →L[ℂ] E) :
    let P_s := U.1 * P0 * (U.1†)
    twoBlockOffDiagProj P0 ((U.1†) * Y * U.1) =
      (U.1†) * twoBlockOffDiagProj P_s Y * U.1 ∧
    twoBlockDiagProj P0 ((U.1†) * Y * U.1) =
      (U.1†) * twoBlockDiagProj P_s Y * U.1 := by
  intro P_s
  have hU_adj_U : (U.1†) * U.1 = 1 := unitary_adj_mul_self U
  have hU_U_adj : U.1 * (U.1†) = 1 := unitary_mul_adj_self U
  have hP0_U : P0 * (U.1†) = (U.1†) * P_s := by
    dsimp [P_s]
    calc P0 * (U.1†)
      _ = ((U.1†) * U.1) * P0 * (U.1†) := by rw [hU_adj_U, one_mul]
      _ = (U.1†) * (U.1 * P0 * (U.1†)) := by simp only [mul_assoc]
  have hU_P0 : U.1 * P0 = P_s * U.1 := by
    dsimp [P_s]
    calc U.1 * P0
      _ = U.1 * P0 * ((U.1†) * U.1) := by rw [hU_adj_U, mul_one]
      _ = (U.1 * P0 * (U.1†)) * U.1 := by simp only [mul_assoc]
  have h1P0_U : (1 - P0) * (U.1†) = (U.1†) * (1 - P_s) := by
    rw [sub_mul, one_mul, mul_sub, mul_one, hP0_U]
  have hU_1P0 : U.1 * (1 - P0) = (1 - P_s) * U.1 := by
    rw [mul_sub, mul_one, sub_mul, one_mul, hU_P0]
  have h_P1P : P0 * ((U.1†) * Y * U.1) * (1 - P0) =
      (U.1†) * (P_s * Y * (1 - P_s)) * U.1 := by
    calc P0 * ((U.1†) * Y * U.1) * (1 - P0)
      _ = (P0 * (U.1†)) * Y * (U.1 * (1 - P0)) := by simp only [mul_assoc]
      _ = ((U.1†) * P_s) * Y * ((1 - P_s) * U.1) := by rw [hP0_U, hU_1P0]
      _ = (U.1†) * (P_s * Y * (1 - P_s)) * U.1 := by simp only [mul_assoc]
  have h_1PP : (1 - P0) * ((U.1†) * Y * U.1) * P0 =
      (U.1†) * ((1 - P_s) * Y * P_s) * U.1 := by
    calc (1 - P0) * ((U.1†) * Y * U.1) * P0
      _ = ((1 - P0) * (U.1†)) * Y * (U.1 * P0) := by simp only [mul_assoc]
      _ = ((U.1†) * (1 - P_s)) * Y * (P_s * U.1) := by rw [h1P0_U, hU_P0]
      _ = (U.1†) * ((1 - P_s) * Y * P_s) * U.1 := by simp only [mul_assoc]
  have h_PP : P0 * ((U.1†) * Y * U.1) * P0 =
      (U.1†) * (P_s * Y * P_s) * U.1 := by
    calc P0 * ((U.1†) * Y * U.1) * P0
      _ = (P0 * (U.1†)) * Y * (U.1 * P0) := by simp only [mul_assoc]
      _ = ((U.1†) * P_s) * Y * (P_s * U.1) := by rw [hP0_U, hU_P0]
      _ = (U.1†) * (P_s * Y * P_s) * U.1 := by simp only [mul_assoc]
  have h_1P1P : (1 - P0) * ((U.1†) * Y * U.1) * (1 - P0) =
      (U.1†) * ((1 - P_s) * Y * (1 - P_s)) * U.1 := by
    calc (1 - P0) * ((U.1†) * Y * U.1) * (1 - P0)
      _ = ((1 - P0) * (U.1†)) * Y * (U.1 * (1 - P0)) := by simp only [mul_assoc]
      _ = ((U.1†) * (1 - P_s)) * Y * ((1 - P_s) * U.1) := by rw [h1P0_U, hU_1P0]
      _ = (U.1†) * ((1 - P_s) * Y * (1 - P_s)) * U.1 := by simp only [mul_assoc]
  refine ⟨?_, ?_⟩
  · unfold twoBlockOffDiagProj
    rw [h_P1P, h_1PP, ← add_mul, ← mul_add]
  · unfold twoBlockDiagProj
    rw [h_PP, h_1P1P, ← add_mul, ← mul_add]

/-- **Dressed Frame Off-Diagonal Vanishing from Bare Frame Spectral Low-Pass Filtering
    (`twoBlockOffDiagProj_dressed_bochnerFilteredSiteOp_eq_zero`)**:
    Along `IsKatoHastingsFlowSystem P0 D_gen U P`, if at parameter $s \in \mathbb{R}$ the bare
    Bochner filter $\mathcal{F}_w^{H(s)}$ annihilates off-diagonal blocks relative to $P(s)$
    (`∀ Y, twoBlockOffDiagProj (P s) (bochnerFilteredOp (H s) w Y) = 0`) and $Q_u$ annihilates $P_0$
    ($Q_u P_0 = 0$ and $P_0 Q_u = 0$), then for $U_s := \mathrm{katoFlowUnitary}\ hFlow\ s$ and
    $H_{\mathrm{dress}}(s) := U_s.1^\dagger H(s) U_s.1$, the dressed site operator
    $X_u := \mathrm{bochnerFilteredSiteOp}\ (H_{\mathrm{dress}}(s))\ U_s.1\ w\ V_u\ Q_u$ satisfies:
    1. `twoBlockOffDiagProj P0 X_u = 0`,
    2. `twoBlockDiagProj P0 X_u = X_u`,
    3. `twoBlockBochnerFilteredSiteOp P0 (H_dress s) U_s.1 w V_u Q_u = X_u`,
    4. `Commute X_u P0` (when `P0 * P0 = P0`). -/
theorem twoBlockOffDiagProj_dressed_bochnerFilteredSiteOp_eq_zero {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    {P0 : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site}
    {D_gen U P : ℝ → (ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site)}
    (hFlow : IsKatoHastingsFlowSystem P0 D_gen U P)
    (hP0_idem : P0 * P0 = P0)
    {H_s V_u Q_u : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site}
    (hHs_sa : IsSelfAdjoint H_s)
    {w : ℝ → ℂ} (hw_int : Integrable w) (s : ℝ)
    (hQP0 : Q_u * P0 = 0) (hP0Q : P0 * Q_u = 0)
    (h_bare_offDiag : ∀ Y : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site,
      twoBlockOffDiagProj (P s) (bochnerFilteredOp H_s w Y) = 0) :
    let U_s := katoFlowUnitary hFlow s
    let H_dress := U_s.1† * H_s * U_s.1
    let X_u := bochnerFilteredSiteOp H_dress U_s.1 w V_u Q_u
    twoBlockOffDiagProj P0 X_u = 0 ∧
    twoBlockDiagProj P0 X_u = X_u ∧
    twoBlockBochnerFilteredSiteOp P0 H_dress U_s.1 w V_u Q_u = X_u ∧
    Commute X_u P0 := by
  intro U_s H_dress X_u
  have h_abs := kato_hastings_ode_abstract P0 D_gen U P
    hFlow.isSelfAdjoint_D hFlow.U_zero hFlow.P_zero hFlow.hasDerivAt_U hFlow.hasDerivAt_P s
  have hP_eq : P s = U_s.1 * P0 * (U_s.1†) := h_abs.2.2.2.2.1.symm
  have h_filt_offDiag : ∀ A : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site,
      twoBlockOffDiagProj P0 (bochnerFilteredOp H_dress w (U_s.1† * A * U_s.1)) = 0 := by
    intro A
    rw [bochnerFilteredOp_unitary_conj hHs_sa U_s hw_int A,
      (twoBlockProj_unitary_adj_conj U_s P0 (bochnerFilteredOp H_s w A)).1,
      ← hP_eq, h_bare_offDiag A, mul_zero, zero_mul]
  have hQ_off : twoBlockOffDiagProj P0 Q_u = 0 := by
    unfold twoBlockOffDiagProj
    rw [hP0Q, zero_mul, zero_add, mul_assoc, hQP0, mul_zero]
  have hX_off : twoBlockOffDiagProj P0 X_u = 0 := by
    dsimp [X_u, bochnerFilteredSiteOp]
    rw [twoBlockOffDiagProj_add, twoBlockOffDiagProj_sub,
      h_filt_offDiag V_u, h_filt_offDiag Q_u, hQ_off, sub_zero, add_zero]
  have hX_diag : twoBlockDiagProj P0 X_u = X_u := by
    calc twoBlockDiagProj P0 X_u
      _ = twoBlockDiagProj P0 X_u + twoBlockOffDiagProj P0 X_u := by rw [hX_off, add_zero]
      _ = X_u := twoBlockDiagProj_add_twoBlockOffDiagProj P0 X_u
  have h_twoBlock : twoBlockBochnerFilteredSiteOp P0 H_dress U_s.1 w V_u Q_u = X_u :=
    hX_diag
  have h_comm : Commute X_u P0 := by
    rw [← hX_diag]
    exact commute_twoBlockDiagProj hP0_idem X_u
  exact ⟨hX_off, hX_diag, h_twoBlock, h_comm⟩

/-!
## 3. Canonical Quasi-Local QAC Unitary Flow & Master ODE Block-Diagonalization Package
-/

/-- **Canonical Constructive QAC Generator (`qacGeneratorPerturbation`)**:
    Alias for `indexedQuasiLocalQACGenerator sys V`, with local terms
    $D_{r, A} = i [\mathrm{sys.P\_loc}\ A, V_{r, A}] = \mathrm{katoHastingsGeneratorOp}\ (1 - \mathrm{sys.P\_loc}\ A)\ W_{\mathrm{BH11}}^{\mathrm{sa}}\ V_{r, A}$. -/
def qacGeneratorPerturbation {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (sys : IndexedCommutingProjectorHamiltonian D L Site ι)
    (V : QuasiLocalPerturbation D L Site) :
    QuasiLocalPerturbation D L Site :=
  indexedQuasiLocalQACGenerator sys V

/-- **Canonical QAC Unitary Flow (`qacUnitaryFlow`)**:
    $U_{\mathrm{QAC}}(s) := \exp(i s \mathcal{D}_{\mathrm{loc}}.V_{\mathrm{tot}}) \in \mathrm{unitary}(\mathcal{B}(\mathcal{H}))$. -/
def qacUnitaryFlow {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (sys : IndexedCommutingProjectorHamiltonian D L Site ι)
    (V : QuasiLocalPerturbation D L Site) (s : ℝ) :
    unitary (ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site) :=
  let D_loc := qacGeneratorPerturbation sys V
  unitaryOfTimeEvolutionOp D_loc.totalPerturbation D_loc.isSelfAdjoint_totalPerturbation s

/-- **Canonical QAC Evolved Ground Projector (`qacProjectorFlow`)**:
    $P_{\mathrm{QAC}}(s) := U_{\mathrm{QAC}}(s) P_0 U_{\mathrm{QAC}}(s)^\dagger = \tau_s^{\mathcal{D}_{\mathrm{loc}}}(P_0)$. -/
def qacProjectorFlow {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (sys : IndexedCommutingProjectorHamiltonian D L Site ι)
    (V : QuasiLocalPerturbation D L Site) (s : ℝ) :
    ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site :=
  heisenbergFlow (qacGeneratorPerturbation sys V).totalPerturbation s sys.P0

/-- The canonical pair `(fun s => (qacUnitaryFlow sys V s).1, qacProjectorFlow sys V)` forms a valid
    `IsKatoHastingsFlowSystem sys.P0 (fun _ => (qacGeneratorPerturbation sys V).V_tot)`. -/
theorem isKatoHastingsFlowSystem_qacUnitaryFlow {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (sys : IndexedCommutingProjectorHamiltonian D L Site ι)
    (V : QuasiLocalPerturbation D L Site) :
    let D_loc := qacGeneratorPerturbation sys V
    IsKatoHastingsFlowSystem sys.P0
      (fun _ => D_loc.totalPerturbation)
      (fun s => (qacUnitaryFlow sys V s).1)
      (qacProjectorFlow sys V) := by
  intro D_loc
  refine
    { isSelfAdjoint_D := fun _ => D_loc.isSelfAdjoint_totalPerturbation
      U_zero := timeEvolutionOp_zero D_loc.totalPerturbation
      P_zero := by
        dsimp [qacProjectorFlow, heisenbergFlow]
        rw [neg_zero, timeEvolutionOp_zero, one_mul, mul_one]
      hasDerivAt_U := fun s => hasDerivAt_timeEvolutionOp D_loc.totalPerturbation s
      hasDerivAt_P := fun s => hasDerivAt_heisenbergFlow D_loc.totalPerturbation sys.P0 s }

/-- **Master Linear Operator ODE Flow & Block-Diagonalization Theorem (`qac_ode_flow_properties`)**:
    For any `IsKatoHastingsFlowSystem sys.P0 D_gen U_flow P_flow` and any $s \in \mathbb{R}$,
    let $U_s := \mathrm{katoFlowUnitary}\ hFlow\ s$ and $H(s) := \mathrm{sys.H0} + (s : \mathbb{C}) \bullet V.V_{\mathrm{tot}}$:
    1. `(U_flow s)† * U_flow s = 1` and `U_flow s * (U_flow s)† = 1`;
    2. `(U_flow s)† * P_flow s * U_flow s = sys.P0` and `P_flow s = U_flow s * sys.P0 * (U_flow s)†`;
    3. `IsStarProjection (P_flow s)`;
    4. `Commute (H s) (P_flow s) → Commute (U_s.1† * H s * U_s.1) sys.P0`;
    5. `(∀ τ, Commute (D_gen τ) Pi_sec) → Commute U_s.1 Pi_sec ∧ U_s.1† * Pi_sec * U_s.1 = Pi_sec`. -/
theorem qac_ode_flow_properties {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (sys : IndexedCommutingProjectorHamiltonian D L Site ι)
    (V : QuasiLocalPerturbation D L Site)
    {D_gen U_flow P_flow : ℝ → (ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site)}
    (hFlow : IsKatoHastingsFlowSystem sys.P0 D_gen U_flow P_flow) (s : ℝ) :
    let U_s := katoFlowUnitary hFlow s
    let H_s := interpolatedHamiltonianOp sys V s
    ((U_flow s)† * U_flow s = 1 ∧ U_flow s * (U_flow s)† = 1) ∧
    (U_s.1† * P_flow s * U_s.1 = sys.P0 ∧ P_flow s = U_s.1 * sys.P0 * U_s.1†) ∧
    IsStarProjection (P_flow s) ∧
    (Commute H_s (P_flow s) → Commute (U_s.1† * H_s * U_s.1) sys.P0) ∧
    (∀ Pi_sec : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site,
      (∀ τ : ℝ, Commute (D_gen τ) Pi_sec) →
      Commute U_s.1 Pi_sec ∧ U_s.1† * Pi_sec * U_s.1 = Pi_sec) := by
  intro U_s H_s
  have h_ode := kato_hastings_ode_flow sys.P0 D_gen U_flow P_flow hFlow
  rcases isStarProjection_P_of_isKatoHastingsFlowSystem hFlow sys.isStarProjection_P0 s with
    ⟨hP_eq, hP_proj⟩
  refine ⟨h_ode.1 s, ⟨h_ode.2.1 s, hP_eq⟩, hP_proj, h_ode.2.2 s H_s, fun Pi_sec hD_sec => ?_⟩
  rcases commute_U_of_isKatoHastingsFlowSystem hFlow hD_sec s with ⟨h_conj_adj, _, _, _, h_comm⟩
  exact ⟨h_comm, h_conj_adj⟩

end
