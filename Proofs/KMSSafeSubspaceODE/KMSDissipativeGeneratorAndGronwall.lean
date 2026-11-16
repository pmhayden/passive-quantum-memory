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

import Proofs.KMSSafeSubspaceODE.SupersolutionODEIntegral

open scoped Classical InnerProduct ComplexConjugate BigOperators
open Filter Topology Asymptotics ContinuousLinearMap

noncomputable section

/-!
# General KMS-Symmetric Dissipative Generators, Semigroup ODE Solutions, and Drift–Dissipation Grönwall Bound

Formalizes the structural properties of general KMS-symmetric dissipative generators
(`IsKMSSymmetricDissipativeGenerator`, Part II, Definition 2.6 (`def:kms-lindblad`)) and proves
the generalized KMS drift–dissipation Grönwall bound (`opKMSNorm_sub_le_kmsDriftDirichletBound_of_dissipativeODE`,
Part II, Theorem 6.2 (`thm:kms-gronwall-bare`)). Establishes:
1. Positivity-preserving, unital, $\dagger$-preserving semigroups $\Phi_t = e^{t\mathcal{L}_{\beta,\mathrm{diss}}^*}$
   with KMS-symmetric generator contract the KMS norm (via $2^m$ power iteration) and automatically
   satisfy `IsKMSSymmetricDissipativeGenerator`;
2. Every jump channel family `bath` with non-negative rates $\gamma_{\mathrm{ch}} \ge 0$ induces a
   KMS-symmetric dissipative generator `opKMSLindbladDissipator` with exact KMS pre-Dirichlet form
   $2\,\mathcal{E}_\beta(A, B) = \sum_{\mathrm{ch}} \gamma_{\mathrm{ch}} \langle [L_{\mathrm{ch}}, A], [L_{\mathrm{ch}}, B]\rangle_{\mathrm{KMS},\beta}$,
   and adjoint-symmetric families generate genuine self-adjoint Heisenberg trajectories via
   `opKMSLindbladSemigroup`;
3. Generalized Theorem 6.2 (`thm:kms-gronwall-bare`) and its exact $\Gamma_{\mathrm{coh}} = 0$
   squared-norm specialization (Part I, Theorem 5.8(i)).

## References

* Part I, Section 5.5 (`subsec:unperturbed-kms-lifetime`), Theorem 5.8(i) (`thm:unperturbed-kms-lifetime`)
* Part II, Section 2 (`subsec:setup`), Definition 2.6 (`def:kms-lindblad`)
* Part II, Section 6.2 (`subsec:kms-gronwall`), Theorem 6.2 (`thm:kms-gronwall-bare`)
-/

private lemma isSelfAdjoint_gibbsSqrtOp {D L_box : ℕ}
    {Site : BoxD D L_box → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    (ψ_eig : ManyBodyConfig Site → ManyBodyHilbertSpace Site)
    (E_eig : ManyBodyConfig Site → ℝ) (β : ℝ) :
    IsSelfAdjoint (gibbsSqrtOp ψ_eig E_eig β) := by
  have h_eq : gibbsSqrtOp ψ_eig E_eig β =
      (((Real.sqrt (gibbsPartitionZ E_eig β))⁻¹ : ℝ) : ℂ) •
        spectralWeightOp ψ_eig (fun ω => Real.exp (-β * E_eig ω / 2)) := by
    unfold gibbsSqrtOp spectralWeightOp; rw [Complex.ofReal_inv]
  rw [h_eq]
  exact isSelfAdjoint_smul_ofReal _ (isSelfAdjoint_spectralWeightOp ψ_eig _)

private lemma kmsInnerReal_symm {D L_box : ℕ}
    {Site : BoxD D L_box → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    (ψ_eig : ManyBodyConfig Site → ManyBodyHilbertSpace Site)
    (E_eig : ManyBodyConfig Site → ℝ) (β : ℝ)
    (A B : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site) :
    kmsInnerReal ψ_eig E_eig β A B = kmsInnerReal ψ_eig E_eig β B A := by
  let S := gibbsSqrtOp ψ_eig E_eig β
  have hS : IsSelfAdjoint S := isSelfAdjoint_gibbsSqrtOp ψ_eig E_eig β
  have h_adj : (S * A† * S * B)† = (B† * S * A) * S := by
    change star (S * star A * S * B) = (star B * S * A) * S
    rw [star_mul, star_mul, star_mul, star_star, hS.star_eq]
    simp only [mul_assoc]
  unfold kmsInnerReal
  change hilbertTrace (S * A† * S * B) = hilbertTrace (S * B† * S * A)
  rw [← hilbertTrace_adjoint (S * A† * S * B), h_adj,
    hilbertTrace_mul_comm_aux (B† * S * A) S]
  simp only [mul_assoc]

private lemma kmsInnerReal_smul_right {D L_box : ℕ}
    {Site : BoxD D L_box → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    (ψ_eig : ManyBodyConfig Site → ManyBodyHilbertSpace Site)
    (E_eig : ManyBodyConfig Site → ℝ) (β : ℝ) (r : ℝ)
    (A B : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site) :
    kmsInnerReal ψ_eig E_eig β A ((r : ℂ) • B) = r * kmsInnerReal ψ_eig E_eig β A B := by
  unfold kmsInnerReal
  rw [clm_mul_smul, hilbertTrace_smul_ofReal]

private lemma kmsInnerReal_smul_left {D L_box : ℕ}
    {Site : BoxD D L_box → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    (ψ_eig : ManyBodyConfig Site → ManyBodyHilbertSpace Site)
    (E_eig : ManyBodyConfig Site → ℝ) (β : ℝ) (r : ℝ)
    (A B : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site) :
    kmsInnerReal ψ_eig E_eig β ((r : ℂ) • A) B = r * kmsInnerReal ψ_eig E_eig β A B := by
  rw [kmsInnerReal_symm, kmsInnerReal_smul_right, kmsInnerReal_symm]

private lemma adjoint_smul_clm {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [CompleteSpace E] (c : ℂ) (Y : E →L[ℂ] E) :
    (c • Y)† = starRingEnd ℂ c • (Y†) := by
  change star (c • Y) = star c • star Y
  exact star_smul c Y

private lemma adjoint_mul_clm {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [CompleteSpace E] (A B : E →L[ℂ] E) :
    (A * B)† = B† * A† :=
  star_mul A B

private lemma isSelfAdjoint_gibbsInvSqrtOp {D L_box : ℕ}
    {Site : BoxD D L_box → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    (ψ_eig : ManyBodyConfig Site → ManyBodyHilbertSpace Site)
    (E_eig : ManyBodyConfig Site → ℝ) (β : ℝ) :
    IsSelfAdjoint (gibbsInvSqrtOp ψ_eig E_eig β) := by
  exact isSelfAdjoint_smul_ofReal _ (isSelfAdjoint_spectralWeightOp ψ_eig _)

private lemma isStarPreservingMap_pow {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [CompleteSpace E] {N : (E →L[ℂ] E) →L[ℂ] (E →L[ℂ] E)} (hN : IsStarPreservingMap N) :
    ∀ n : ℕ, IsStarPreservingMap (N ^ n)
  | 0 => fun _ => rfl
  | n + 1 => fun X => by
      rw [pow_succ']
      change (N ((N ^ n) X))† = N ((N ^ n) (X†))
      rw [hN, isStarPreservingMap_pow hN n X]

private lemma isStarPreservingMap_exp_real_smul {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] [CompleteSpace E]
    {M : (E →L[ℂ] E) →L[ℂ] (E →L[ℂ] E)} (hM : IsStarPreservingMap M) (s : ℝ) :
    IsStarPreservingMap (NormedSpace.exp ((s : ℂ) • M)) := by
  let +nondep : NormedAlgebra ℚ ((E →L[ℂ] E) →L[ℂ] (E →L[ℂ] E)) := .restrictScalars ℚ ℂ _
  intro X
  let N := (s : ℂ) • M
  have hN : IsStarPreservingMap N := fun Y => by
    dsimp [N]
    rw [smul_apply, adjoint_smul_clm, Complex.conj_ofReal, hM Y, smul_apply]
  have h_sum := NormedSpace.exp_series_hasSum_exp' (𝕂 := ℂ) N
  let evX := ContinuousLinearMap.apply ℂ (E →L[ℂ] E) X
  let evXstar := ContinuousLinearMap.apply ℂ (E →L[ℂ] E) (X†)
  have h1 : HasSum (fun n : ℕ => (((n.factorial : ℂ)⁻¹ • N ^ n) X)†)
      ((NormedSpace.exp N X)†) := by
    have h1a := h_sum.map evX.toAddMonoidHom evX.continuous
    exact h1a.map ContinuousLinearMap.adjoint.toLinearEquiv.toAddMonoidHom
      ContinuousLinearMap.adjoint.continuous
  have h2 : HasSum (fun n : ℕ => ((n.factorial : ℂ)⁻¹ • N ^ n) (X†))
      (NormedSpace.exp N (X†)) :=
    h_sum.map evXstar.toAddMonoidHom evXstar.continuous
  have h_eq : (fun n : ℕ => (((n.factorial : ℂ)⁻¹ • N ^ n) X)†) =
      (fun n : ℕ => ((n.factorial : ℂ)⁻¹ • N ^ n) (X†)) := by
    ext n : 1
    have h_real : (n.factorial : ℂ)⁻¹ = (((n.factorial : ℝ)⁻¹ : ℝ) : ℂ) := by push_cast; rfl
    rw [smul_apply, h_real, adjoint_smul_clm, Complex.conj_ofReal,
      isStarPreservingMap_pow hN n X, smul_apply]
  rw [h_eq] at h1
  exact h1.unique h2

private lemma exp_zero_smul_apply {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [CompleteSpace E] (G : (E →L[ℂ] E) →L[ℂ] (E →L[ℂ] E)) (X : E →L[ℂ] E) :
    NormedSpace.exp (((0 : ℝ) : ℂ) • G) X = X := by
  have h0 : ((0 : ℝ) : ℂ) • G = 0 := by ext Y φ; simp
  rw [h0, NormedSpace.exp_zero]
  rfl

private lemma hasDerivAt_exp_real_smul_apply {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] [CompleteSpace E]
    (G : (E →L[ℂ] E) →L[ℂ] (E →L[ℂ] E)) (X : E →L[ℂ] E) (s : ℝ) :
    HasDerivAt (fun u : ℝ => NormedSpace.exp ((u : ℂ) • G) X)
      (G (NormedSpace.exp ((s : ℂ) • G) X)) s := by
  have hd_c : HasDerivAt (fun z : ℂ => NormedSpace.exp (z • G))
      (G * NormedSpace.exp ((s : ℂ) • G)) (s : ℂ) :=
    _root_.hasDerivAt_exp_smul_const' G (s : ℂ)
  have hd_t : Tendsto
      (fun u : ℝ =>
        (‖(u : ℂ) - (s : ℂ)‖⁻¹ *
          ‖NormedSpace.exp ((u : ℂ) • G) - NormedSpace.exp ((s : ℂ) • G) -
            ((u : ℂ) - (s : ℂ)) • (G * NormedSpace.exp ((s : ℂ) • G))‖) * ‖X‖)
      (𝓝 s) (𝓝 0) := by
    have hd_c_t :=
      (hasDerivAt_iff_tendsto (𝕜 := ℂ) (F := (E →L[ℂ] E) →L[ℂ] (E →L[ℂ] E))).mp hd_c
    have h_comp := hd_c_t.comp (Complex.continuous_ofReal.tendsto s)
    simpa only [Function.comp_apply, zero_mul] using h_comp.mul_const ‖X‖
  refine hasDerivAt_iff_tendsto.mpr ?_
  refine squeeze_zero (fun _ => by positivity) (fun u => ?_) hd_t
  have h_sub : NormedSpace.exp ((u : ℂ) • G) X - NormedSpace.exp ((s : ℂ) • G) X -
        (u - s) • G (NormedSpace.exp ((s : ℂ) • G) X) =
      (NormedSpace.exp ((u : ℂ) • G) - NormedSpace.exp ((s : ℂ) • G) -
        ((u : ℂ) - (s : ℂ)) • (G * NormedSpace.exp ((s : ℂ) • G))) X := by
    ext φ
    simp only [sub_apply, smul_apply, mul_apply_eq_comp]
    congr 1
    rw [← Complex.ofReal_sub, Complex.coe_smul]
  have h_norm_u : ‖u - s‖ = ‖(u : ℂ) - (s : ℂ)‖ := by
    rw [← Complex.ofReal_sub, Complex.norm_real]
  rw [h_sub, h_norm_u]
  calc ‖(u : ℂ) - (s : ℂ)‖⁻¹ * ‖(NormedSpace.exp ((u : ℂ) • G) - NormedSpace.exp ((s : ℂ) • G) -
          ((u : ℂ) - (s : ℂ)) • (G * NormedSpace.exp ((s : ℂ) • G))) X‖
    _ ≤ ‖(u : ℂ) - (s : ℂ)‖⁻¹ * (‖NormedSpace.exp ((u : ℂ) • G) - NormedSpace.exp ((s : ℂ) • G) -
          ((u : ℂ) - (s : ℂ)) • (G * NormedSpace.exp ((s : ℂ) • G))‖ * ‖X‖) :=
        mul_le_mul_of_nonneg_left (ContinuousLinearMap.le_opNorm _ X) (by positivity)
    _ = (‖(u : ℂ) - (s : ℂ)‖⁻¹ * ‖NormedSpace.exp ((u : ℂ) • G) - NormedSpace.exp ((s : ℂ) • G) -
          ((u : ℂ) - (s : ℂ)) • (G * NormedSpace.exp ((s : ℂ) • G))‖) * ‖X‖ := by ring

private lemma hasDerivAt_finset_sum {α : Type*} (s_fin : Finset α)
    {g : α → ℝ → ℝ} {g' : α → ℝ} {x : ℝ}
    (hg : ∀ a ∈ s_fin, HasDerivAt (g a) (g' a) x) :
    HasDerivAt (fun u : ℝ => ∑ a ∈ s_fin, g a u) (∑ a ∈ s_fin, g' a) x := by
  classical
  induction s_fin using Finset.induction_on with
  | empty => simpa using hasDerivAt_const x (0 : ℝ)
  | insert a s' ha ih =>
    simp_rw [Finset.sum_insert ha]
    exact (hg a (Finset.mem_insert_self a s')).add
      (ih fun b hb => hg b (Finset.mem_insert_of_mem hb))

private lemma hasDerivAt_kmsNormSq {D L_box : ℕ}
    {Site : BoxD D L_box → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    [∀ x, Nonempty (Site x)]
    (H : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site)
    (hH : IsSelfAdjoint H) (β : ℝ)
    {Δ : ℝ → (ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site)}
    {Δ' : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site} {s : ℝ}
    (hΔ : HasDerivAt Δ Δ' s) :
    HasDerivAt (fun u : ℝ => kmsNormSq (opEigenbasis H hH) (opEigenvalues H hH) β (Δ u))
      (2 * kmsInnerReal (opEigenbasis H hH) (opEigenvalues H hH) β (Δ s) Δ') s := by
  let ψ_eig := opEigenbasis H hH
  let E_eig := opEigenvalues H hH
  have h_eq_fn : (fun u : ℝ => kmsNormSq ψ_eig E_eig β (Δ u)) =
      fun u : ℝ => ∑ ω₁ : ManyBodyConfig Site, ∑ ω₂ : ManyBodyConfig Site,
        Real.sqrt (gibbsProb E_eig β ω₁) * Real.sqrt (gibbsProb E_eig β ω₂) *
          ‖inner ℂ (ψ_eig ω₂) (Δ u (ψ_eig ω₁))‖ ^ 2 := by
    ext u
    exact kmsNormSq_eq_spectral_sum ψ_eig E_eig β
      (opEigenbasis_orthonormal H hH) (hilbertTrace_eq_sum_opEigenbasis H hH) (Δ u)
  have hΔ_t := hasDerivAt_iff_tendsto.mp hΔ
  have h_term : ∀ ω₁ ω₂ : ManyBodyConfig Site,
      HasDerivAt (fun u : ℝ =>
        Real.sqrt (gibbsProb E_eig β ω₁) * Real.sqrt (gibbsProb E_eig β ω₂) *
          ‖inner ℂ (ψ_eig ω₂) (Δ u (ψ_eig ω₁))‖ ^ 2)
        (Real.sqrt (gibbsProb E_eig β ω₁) * Real.sqrt (gibbsProb E_eig β ω₂) *
          (2 * RCLike.re (starRingEnd ℂ (inner ℂ (ψ_eig ω₂) (Δ s (ψ_eig ω₁))) *
            inner ℂ (ψ_eig ω₂) (Δ' (ψ_eig ω₁))))) s := by
    intro ω₁ ω₂
    have hz : HasDerivAt (fun u : ℝ => inner ℂ (ψ_eig ω₂) (Δ u (ψ_eig ω₁)))
        (inner ℂ (ψ_eig ω₂) (Δ' (ψ_eig ω₁))) s := by
      have hz_lim : Tendsto
          (fun u : ℝ => (‖u - s‖⁻¹ * ‖Δ u - Δ s - (u - s) • Δ'‖) * (‖ψ_eig ω₂‖ * ‖ψ_eig ω₁‖))
          (𝓝 s) (𝓝 0) := by
        simpa only [zero_mul] using hΔ_t.mul_const (‖ψ_eig ω₂‖ * ‖ψ_eig ω₁‖)
      refine hasDerivAt_iff_tendsto.mpr ?_
      refine squeeze_zero (fun _ => by positivity) (fun u => ?_) hz_lim
      have h_lin : inner ℂ (ψ_eig ω₂) (Δ u (ψ_eig ω₁)) -
            inner ℂ (ψ_eig ω₂) (Δ s (ψ_eig ω₁)) -
            (u - s) • inner ℂ (ψ_eig ω₂) (Δ' (ψ_eig ω₁)) =
          inner ℂ (ψ_eig ω₂) (((Δ u - Δ s - (u - s) • Δ') (ψ_eig ω₁))) := by
        have h_clm_smul : ((u - s) • Δ') (ψ_eig ω₁) = ((u - s : ℝ) : ℂ) • (Δ' (ψ_eig ω₁)) := rfl
        rw [sub_apply, sub_apply, h_clm_smul, inner_sub_right, inner_sub_right,
          inner_smul_right, Complex.real_smul]
      rw [h_lin]
      have h_cs : ‖inner ℂ (ψ_eig ω₂) (((Δ u - Δ s - (u - s) • Δ') (ψ_eig ω₁)))‖ ≤
          ‖Δ u - Δ s - (u - s) • Δ'‖ * (‖ψ_eig ω₂‖ * ‖ψ_eig ω₁‖) := by
        calc ‖inner ℂ (ψ_eig ω₂) (((Δ u - Δ s - (u - s) • Δ') (ψ_eig ω₁)))‖
          _ ≤ ‖ψ_eig ω₂‖ * ‖(Δ u - Δ s - (u - s) • Δ') (ψ_eig ω₁)‖ := norm_inner_le_norm _ _
          _ ≤ ‖ψ_eig ω₂‖ * (‖Δ u - Δ s - (u - s) • Δ'‖ * ‖ψ_eig ω₁‖) :=
              mul_le_mul_of_nonneg_left (ContinuousLinearMap.le_opNorm _ _) (norm_nonneg _)
          _ = ‖Δ u - Δ s - (u - s) • Δ'‖ * (‖ψ_eig ω₂‖ * ‖ψ_eig ω₁‖) := by ring
      calc ‖u - s‖⁻¹ * ‖inner ℂ (ψ_eig ω₂) (((Δ u - Δ s - (u - s) • Δ') (ψ_eig ω₁)))‖
        _ ≤ ‖u - s‖⁻¹ * (‖Δ u - Δ s - (u - s) • Δ'‖ * (‖ψ_eig ω₂‖ * ‖ψ_eig ω₁‖)) :=
            mul_le_mul_of_nonneg_left h_cs (by positivity)
        _ = (‖u - s‖⁻¹ * ‖Δ u - Δ s - (u - s) • Δ'‖) * (‖ψ_eig ω₂‖ * ‖ψ_eig ω₁‖) := by ring
    have h_re := Complex.reCLM.hasFDerivAt.comp_hasDerivAt s hz
    have h_im := Complex.imCLM.hasFDerivAt.comp_hasDerivAt s hz
    have h_sq_eq : (fun u : ℝ => ‖inner ℂ (ψ_eig ω₂) (Δ u (ψ_eig ω₁))‖ ^ 2) =
        fun u : ℝ => (inner ℂ (ψ_eig ω₂) (Δ u (ψ_eig ω₁))).re ^ 2 +
          (inner ℂ (ψ_eig ω₂) (Δ u (ψ_eig ω₁))).im ^ 2 := by
      ext u
      rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
      ring
    have h_norm_deriv : HasDerivAt (fun u : ℝ => ‖inner ℂ (ψ_eig ω₂) (Δ u (ψ_eig ω₁))‖ ^ 2)
        (2 * RCLike.re (starRingEnd ℂ (inner ℂ (ψ_eig ω₂) (Δ s (ψ_eig ω₁))) *
          inner ℂ (ψ_eig ω₂) (Δ' (ψ_eig ω₁)))) s := by
      rw [h_sq_eq]
      refine ((h_re.fun_pow 2).add (h_im.fun_pow 2)).congr_deriv ?_
      change 2 * (inner ℂ (ψ_eig ω₂) (Δ s (ψ_eig ω₁))).re ^ (2 - 1) *
            (inner ℂ (ψ_eig ω₂) (Δ' (ψ_eig ω₁))).re +
          2 * (inner ℂ (ψ_eig ω₂) (Δ s (ψ_eig ω₁))).im ^ (2 - 1) *
            (inner ℂ (ψ_eig ω₂) (Δ' (ψ_eig ω₁))).im =
        2 * (starRingEnd ℂ (inner ℂ (ψ_eig ω₂) (Δ s (ψ_eig ω₁))) *
          inner ℂ (ψ_eig ω₂) (Δ' (ψ_eig ω₁))).re
      rw [Complex.mul_re, Complex.conj_re, Complex.conj_im]
      ring
    exact h_norm_deriv.const_mul _
  rw [h_eq_fn]
  have h_sum_deriv := hasDerivAt_finset_sum Finset.univ fun ω₁ _ =>
    hasDerivAt_finset_sum Finset.univ fun ω₂ _ => h_term ω₁ ω₂
  refine h_sum_deriv.congr_deriv ?_
  rw [kmsInnerReal_eq_spectral_sum ψ_eig E_eig β
    (opEigenbasis_orthonormal H hH) (hilbertTrace_eq_sum_opEigenbasis H hH) (Δ s) Δ',
    Finset.mul_sum]
  refine Finset.sum_congr rfl fun ω₁ _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun ω₂ _ => by ring

private lemma superop_pow_succ_apply {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] [CompleteSpace E]
    (N : (E →L[ℂ] E) →L[ℂ] (E →L[ℂ] E)) (n : ℕ) (X : E →L[ℂ] E) :
    (N ^ (n + 1)) X = N ((N ^ n) X) ∧ (N ^ (n + 1)) X = (N ^ n) (N X) := by
  refine ⟨?_, ?_⟩
  · rw [pow_succ']; rfl
  · rw [pow_succ]; rfl

private lemma exp_series_hasSum_exp_apply {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] [CompleteSpace E]
    (N : (E →L[ℂ] E) →L[ℂ] (E →L[ℂ] E)) (X : E →L[ℂ] E) :
    HasSum (fun n : ℕ => (n.factorial : ℂ)⁻¹ • ((N ^ n) X)) (NormedSpace.exp N X) := by
  let ev := ContinuousLinearMap.apply ℂ (E →L[ℂ] E) X
  have h1 := (NormedSpace.exp_series_hasSum_exp' (𝕂 := ℂ) N).map ev.toAddMonoidHom ev.continuous
  have h_eq : (⇑ev.toAddMonoidHom ∘ fun n : ℕ => (n.factorial : ℂ)⁻¹ • N ^ n) =
      fun n : ℕ => (n.factorial : ℂ)⁻¹ • ((N ^ n) X) := by
    ext n φ; rfl
  rw [h_eq] at h1
  exact h1

private lemma exp_real_smul_one_eq_one {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] [CompleteSpace E]
    {L_diss : (E →L[ℂ] E) →L[ℂ] (E →L[ℂ] E)} (h_unital : L_diss 1 = 0) (t : ℝ) :
    NormedSpace.exp ((t : ℂ) • L_diss) 1 = 1 := by
  let N := (t : ℂ) • L_diss
  have hN1 : N 1 = 0 := by dsimp [N]; rw [smul_apply, h_unital, smul_zero]
  have h_pow : ∀ n : ℕ, (N ^ n) 1 = if n = 0 then (1 : E →L[ℂ] E) else 0
    | 0 => rfl
    | n + 1 => by
        rw [(superop_pow_succ_apply N n 1).2, hN1, map_zero]
        simp
  have h1 := exp_series_hasSum_exp_apply N 1
  have h_fn : (fun n : ℕ => (n.factorial : ℂ)⁻¹ • ((N ^ n) 1)) =
      fun n : ℕ => if n = 0 then (1 : E →L[ℂ] E) else 0 := by
    ext n : 1
    rw [h_pow n]
    split_ifs with hn
    · subst hn; simp
    · simp
  rw [h_fn] at h1
  exact h1.unique (hasSum_single (0 : ℕ) fun n hn => by simp [hn])

private lemma exp_real_smul_add_apply {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] [CompleteSpace E]
    (L_diss : (E →L[ℂ] E) →L[ℂ] (E →L[ℂ] E)) (s t : ℝ) (X : E →L[ℂ] E) :
    NormedSpace.exp (((s + t : ℝ) : ℂ) • L_diss) X =
      NormedSpace.exp ((s : ℂ) • L_diss) (NormedSpace.exp ((t : ℂ) • L_diss) X) := by
  have h_add : (((s + t : ℝ) : ℂ) • L_diss) = (s : ℂ) • L_diss + (t : ℂ) • L_diss := by
    ext Y φ
    simp only [add_apply, smul_apply]
    rw [Complex.ofReal_add, add_smul]
  have h_comm : Commute ((s : ℂ) • L_diss) ((t : ℂ) • L_diss) := by
    unfold Commute SemiconjBy
    ext Y φ
    simp only [mul_apply_eq_comp, smul_apply, map_smul, smul_smul]
    rw [mul_comm (s : ℂ) (t : ℂ)]
  have hexp := @NormedSpace.exp_add_of_commute
    ((E →L[ℂ] E) →L[ℂ] (E →L[ℂ] E)) _ (.restrictScalars ℚ ℂ _) _ _ _ h_comm
  rw [h_add, hexp]
  rfl

private lemma continuous_kmsInnerReal_right {D L_box : ℕ}
    {Site : BoxD D L_box → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    [∀ x, Nonempty (Site x)]
    (H : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site)
    (hH : IsSelfAdjoint H) (β : ℝ)
    (A : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site) :
    Continuous (fun Y => kmsInnerReal (opEigenbasis H hH) (opEigenvalues H hH) β A Y) := by
  let ψ_eig := opEigenbasis H hH
  let E_eig := opEigenvalues H hH
  have h_eq : (fun Y => kmsInnerReal ψ_eig E_eig β A Y) =
      fun Y => ∑ ω₁ : ManyBodyConfig Site, ∑ ω₂ : ManyBodyConfig Site,
        Real.sqrt (gibbsProb E_eig β ω₁) * Real.sqrt (gibbsProb E_eig β ω₂) *
          RCLike.re (starRingEnd ℂ (inner ℂ (ψ_eig ω₂) (A (ψ_eig ω₁))) *
            inner ℂ (ψ_eig ω₂) (Y (ψ_eig ω₁))) := by
    ext Y
    exact kmsInnerReal_eq_spectral_sum ψ_eig E_eig β
      (opEigenbasis_orthonormal H hH) (hilbertTrace_eq_sum_opEigenbasis H hH) A Y
  rw [h_eq]
  refine continuous_finsetSum Finset.univ fun ω₁ _ =>
    continuous_finsetSum Finset.univ fun ω₂ _ => ?_
  have h_ev : Continuous (fun Y : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site =>
      Y (ψ_eig ω₁)) :=
    (ContinuousLinearMap.apply ℂ (ManyBodyHilbertSpace Site) (ψ_eig ω₁)).continuous
  have h_in : Continuous (fun Y : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site =>
      inner ℂ (ψ_eig ω₂) (Y (ψ_eig ω₁))) :=
    continuous_const.inner h_ev
  exact continuous_const.mul (Complex.continuous_re.comp (continuous_const.mul h_in))

private lemma kmsInnerReal_exp_real_smul_symm {D L_box : ℕ}
    {Site : BoxD D L_box → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    [∀ x, Nonempty (Site x)]
    (H : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site)
    (hH : IsSelfAdjoint H) (β : ℝ)
    {L_diss : (ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site) →L[ℂ]
      (ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site)}
    (h_symm : ∀ A B,
      kmsInnerReal (opEigenbasis H hH) (opEigenvalues H hH) β A (L_diss B) =
        kmsInnerReal (opEigenbasis H hH) (opEigenvalues H hH) β (L_diss A) B)
    (t : ℝ) (A B : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site) :
    kmsInnerReal (opEigenbasis H hH) (opEigenvalues H hH) β A
        (NormedSpace.exp ((t : ℂ) • L_diss) B) =
      kmsInnerReal (opEigenbasis H hH) (opEigenvalues H hH) β
        (NormedSpace.exp ((t : ℂ) • L_diss) A) B := by
  let ψ_eig := opEigenbasis H hH
  let E_eig := opEigenvalues H hH
  let N := (t : ℂ) • L_diss
  have hN_symm : ∀ X Y, kmsInnerReal ψ_eig E_eig β X (N Y) =
      kmsInnerReal ψ_eig E_eig β (N X) Y := fun X Y => by
    dsimp [N]
    rw [smul_apply, smul_apply, kmsInnerReal_smul_right, kmsInnerReal_smul_left, h_symm X Y]
  have h_pow_symm : ∀ (n : ℕ) X Y,
      kmsInnerReal ψ_eig E_eig β X ((N ^ n) Y) =
        kmsInnerReal ψ_eig E_eig β ((N ^ n) X) Y := by
    intro n
    induction n with
    | zero => intro X Y; rfl
    | succ n ih =>
        intro X Y
        rw [(superop_pow_succ_apply N n Y).1, (superop_pow_succ_apply N n X).2,
          hN_symm X ((N ^ n) Y), ih (N X) Y]
  let homR := AddMonoidHom.mk' (fun Y => kmsInnerReal ψ_eig E_eig β A Y)
    (fun Y₁ Y₂ => kmsInnerReal_add_right ψ_eig E_eig β A Y₁ Y₂)
  let homL := AddMonoidHom.mk' (fun X => kmsInnerReal ψ_eig E_eig β X B)
    (fun X₁ X₂ => by
      rw [kmsInnerReal_symm, kmsInnerReal_add_right,
        kmsInnerReal_symm ψ_eig E_eig β B X₁, kmsInnerReal_symm ψ_eig E_eig β B X₂])
  have h_contL : Continuous (fun X => kmsInnerReal ψ_eig E_eig β X B) := by
    have h_eq : (fun X => kmsInnerReal ψ_eig E_eig β X B) =
        fun X => kmsInnerReal ψ_eig E_eig β B X := by
      ext X; exact kmsInnerReal_symm ψ_eig E_eig β X B
    rw [h_eq]
    exact continuous_kmsInnerReal_right H hH β B
  have hR : HasSum (fun n : ℕ => kmsInnerReal ψ_eig E_eig β A ((n.factorial : ℂ)⁻¹ • ((N ^ n) B)))
      (kmsInnerReal ψ_eig E_eig β A (NormedSpace.exp N B)) :=
    (exp_series_hasSum_exp_apply N B).map homR (continuous_kmsInnerReal_right H hH β A)
  have hL : HasSum (fun n : ℕ => kmsInnerReal ψ_eig E_eig β ((n.factorial : ℂ)⁻¹ • ((N ^ n) A)) B)
      (kmsInnerReal ψ_eig E_eig β (NormedSpace.exp N A) B) :=
    (exp_series_hasSum_exp_apply N A).map homL h_contL
  have h_eq :
      (fun n : ℕ => kmsInnerReal ψ_eig E_eig β A ((n.factorial : ℂ)⁻¹ • ((N ^ n) B))) =
      (fun n : ℕ => kmsInnerReal ψ_eig E_eig β ((n.factorial : ℂ)⁻¹ • ((N ^ n) A)) B) := by
    ext n : 1
    have h_real : (n.factorial : ℂ)⁻¹ = (((n.factorial : ℝ)⁻¹ : ℝ) : ℂ) := by push_cast; rfl
    rw [h_real, kmsInnerReal_smul_right, kmsInnerReal_smul_left, h_pow_symm n A B]
  rw [h_eq] at hR
  exact hR.unique hL

private lemma norm_opEigenbasis_eq_one {D L_box : ℕ}
    {Site : BoxD D L_box → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    (M : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site)
    (hM : IsSelfAdjoint M) (ω : ManyBodyConfig Site) :
    ‖opEigenbasis M hM ω‖ = 1 := by
  have h_in := opEigenbasis_orthonormal M hM ω ω
  simp only [ ↓reduceIte] at h_in
  have h_sq : ‖opEigenbasis M hM ω‖ ^ 2 = 1 := by
    rw [norm_sq_eq_re_inner (𝕜 := ℂ), h_in, RCLike.one_re]
  nlinarith [norm_nonneg (opEigenbasis M hM ω)]

private lemma opKMSNorm_le_opNorm {D L_box : ℕ}
    {Site : BoxD D L_box → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    [∀ x, Nonempty (Site x)]
    (H : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site)
    (hH : IsSelfAdjoint H) (β : ℝ)
    (A : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site) :
    opKMSNorm H hH β A ≤ ‖A‖ := by
  let ψ_eig := opEigenbasis H hH
  let E_eig := opEigenvalues H hH
  have h_sq_le : opKMSNormSq H hH β A ≤ ‖A‖ ^ 2 := by
    unfold opKMSNormSq
    rw [kmsNormSq_eq_spectral_sum ψ_eig E_eig β
      (opEigenbasis_orthonormal H hH) (hilbertTrace_eq_sum_opEigenbasis H hH) A]
    have h_amgm :
        (∑ ω₁ : ManyBodyConfig Site, ∑ ω₂ : ManyBodyConfig Site,
          Real.sqrt (gibbsProb E_eig β ω₁) * Real.sqrt (gibbsProb E_eig β ω₂) *
            ‖inner ℂ (ψ_eig ω₂) (A (ψ_eig ω₁))‖ ^ 2) ≤
        (1 / 2 : ℝ) * (∑ ω₁ : ManyBodyConfig Site, gibbsProb E_eig β ω₁ *
            ∑ ω₂ : ManyBodyConfig Site, ‖inner ℂ (ψ_eig ω₂) (A (ψ_eig ω₁))‖ ^ 2) +
        (1 / 2 : ℝ) * (∑ ω₂ : ManyBodyConfig Site, gibbsProb E_eig β ω₂ *
            ∑ ω₁ : ManyBodyConfig Site, ‖inner ℂ (ψ_eig ω₂) (A (ψ_eig ω₁))‖ ^ 2) := by
      have h_split :
          (1 / 2 : ℝ) * (∑ ω₁ : ManyBodyConfig Site, gibbsProb E_eig β ω₁ *
              ∑ ω₂ : ManyBodyConfig Site, ‖inner ℂ (ψ_eig ω₂) (A (ψ_eig ω₁))‖ ^ 2) +
          (1 / 2 : ℝ) * (∑ ω₂ : ManyBodyConfig Site, gibbsProb E_eig β ω₂ *
              ∑ ω₁ : ManyBodyConfig Site, ‖inner ℂ (ψ_eig ω₂) (A (ψ_eig ω₁))‖ ^ 2) =
          ∑ ω₁ : ManyBodyConfig Site, ∑ ω₂ : ManyBodyConfig Site,
            ((gibbsProb E_eig β ω₁ + gibbsProb E_eig β ω₂) / 2) *
              ‖inner ℂ (ψ_eig ω₂) (A (ψ_eig ω₁))‖ ^ 2 := by
        simp_rw [Finset.mul_sum]
        rw [Finset.sum_comm (f := fun ω₂ ω₁ =>
          (1 / 2 : ℝ) * (gibbsProb E_eig β ω₂ * ‖inner ℂ (ψ_eig ω₂) (A (ψ_eig ω₁))‖ ^ 2)),
          ← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun ω₁ _ => ?_
        rw [← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun ω₂ _ => by ring
      rw [h_split]
      refine Finset.sum_le_sum fun ω₁ _ => Finset.sum_le_sum fun ω₂ _ => ?_
      refine mul_le_mul_of_nonneg_right ?_ (sq_nonneg _)
      have hp1 : (Real.sqrt (gibbsProb E_eig β ω₁)) ^ 2 = gibbsProb E_eig β ω₁ :=
        Real.sq_sqrt (gibbsProb_nonneg E_eig β ω₁)
      have hp2 : (Real.sqrt (gibbsProb E_eig β ω₂)) ^ 2 = gibbsProb E_eig β ω₂ :=
        Real.sq_sqrt (gibbsProb_nonneg E_eig β ω₂)
      have hsq : 0 ≤ (Real.sqrt (gibbsProb E_eig β ω₁) - Real.sqrt (gibbsProb E_eig β ω₂)) ^ 2 :=
        sq_nonneg _
      nlinarith
    have h_s1 :
        (∑ ω₁ : ManyBodyConfig Site, gibbsProb E_eig β ω₁ *
          ∑ ω₂ : ManyBodyConfig Site, ‖inner ℂ (ψ_eig ω₂) (A (ψ_eig ω₁))‖ ^ 2) ≤ ‖A‖ ^ 2 := by
      calc ∑ ω₁ : ManyBodyConfig Site, gibbsProb E_eig β ω₁ *
            ∑ ω₂ : ManyBodyConfig Site, ‖inner ℂ (ψ_eig ω₂) (A (ψ_eig ω₁))‖ ^ 2
        _ ≤ ∑ ω₁ : ManyBodyConfig Site, gibbsProb E_eig β ω₁ * ‖A‖ ^ 2 := by
            refine Finset.sum_le_sum fun ω₁ _ =>
              mul_le_mul_of_nonneg_left ?_ (gibbsProb_nonneg E_eig β ω₁)
            rw [opEigenbasis_parseval H hH (A (ψ_eig ω₁))]
            have h_le := ContinuousLinearMap.le_opNorm A (ψ_eig ω₁)
            rw [norm_opEigenbasis_eq_one H hH ω₁, mul_one] at h_le
            exact pow_le_pow_left₀ (norm_nonneg _) h_le 2
        _ = (∑ ω₁ : ManyBodyConfig Site, gibbsProb E_eig β ω₁) * ‖A‖ ^ 2 := by
            rw [Finset.sum_mul]
        _ = ‖A‖ ^ 2 := by rw [sum_gibbsProb_eq_one E_eig β, one_mul]
    have h_s2 :
        (∑ ω₂ : ManyBodyConfig Site, gibbsProb E_eig β ω₂ *
          ∑ ω₁ : ManyBodyConfig Site, ‖inner ℂ (ψ_eig ω₂) (A (ψ_eig ω₁))‖ ^ 2) ≤ ‖A‖ ^ 2 := by
      calc ∑ ω₂ : ManyBodyConfig Site, gibbsProb E_eig β ω₂ *
            ∑ ω₁ : ManyBodyConfig Site, ‖inner ℂ (ψ_eig ω₂) (A (ψ_eig ω₁))‖ ^ 2
        _ ≤ ∑ ω₂ : ManyBodyConfig Site, gibbsProb E_eig β ω₂ * ‖A‖ ^ 2 := by
            refine Finset.sum_le_sum fun ω₂ _ =>
              mul_le_mul_of_nonneg_left ?_ (gibbsProb_nonneg E_eig β ω₂)
            have h_adj_sum :
                (∑ ω₁ : ManyBodyConfig Site, ‖inner ℂ (ψ_eig ω₂) (A (ψ_eig ω₁))‖ ^ 2) =
                ∑ ω₁ : ManyBodyConfig Site, ‖inner ℂ (ψ_eig ω₁) ((A†) (ψ_eig ω₂))‖ ^ 2 := by
              refine Finset.sum_congr rfl fun ω₁ _ => ?_
              rw [ContinuousLinearMap.adjoint_inner_right, norm_inner_symm]
            rw [h_adj_sum, opEigenbasis_parseval H hH ((A†) (ψ_eig ω₂))]
            have h_le := ContinuousLinearMap.le_opNorm (A†) (ψ_eig ω₂)
            rw [norm_opEigenbasis_eq_one H hH ω₂, mul_one,
              ContinuousLinearMap.adjoint.norm_map A] at h_le
            exact pow_le_pow_left₀ (norm_nonneg _) h_le 2
        _ = (∑ ω₂ : ManyBodyConfig Site, gibbsProb E_eig β ω₂) * ‖A‖ ^ 2 := by
            rw [Finset.sum_mul]
        _ = ‖A‖ ^ 2 := by rw [sum_gibbsProb_eq_one E_eig β, one_mul]
    linarith
  unfold opKMSNorm kmsNorm
  calc Real.sqrt (opKMSNormSq H hH β A)
    _ ≤ Real.sqrt (‖A‖ ^ 2) := Real.sqrt_le_sqrt h_sq_le
    _ = ‖A‖ := Real.sqrt_sq (norm_nonneg A)

private lemma opNorm_le_of_quadForm_le {D L_box : ℕ}
    {Site : BoxD D L_box → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    {Y : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site}
    (hY : IsSelfAdjoint Y) {C : ℝ} (hC : 0 ≤ C)
    (h_quad : ∀ ψ : ManyBodyHilbertSpace Site,
      -C * ‖ψ‖ ^ 2 ≤ RCLike.re (inner ℂ ψ (Y ψ)) ∧
        RCLike.re (inner ℂ ψ (Y ψ)) ≤ C * ‖ψ‖ ^ 2) :
    ‖Y‖ ≤ C := by
  let e := opEigenbasis Y hY
  let lam := opEigenvalues Y hY
  have h_lam_sq : ∀ ω : ManyBodyConfig Site, (lam ω) ^ 2 ≤ C ^ 2 := fun ω => by
    have h_onb := opEigenbasis_orthonormal Y hY ω ω
    simp only [ ↓reduceIte] at h_onb
    have h_re : RCLike.re (inner ℂ (e ω) (Y (e ω))) = lam ω := by
      dsimp [e, lam]
      rw [opEigenbasis_apply_H Y hY ω, inner_smul_right, h_onb, mul_one, Complex.ofReal_re]
    have hq := h_quad (e ω)
    rw [h_re, norm_opEigenbasis_eq_one Y hY ω, one_pow, mul_one, mul_one] at hq
    nlinarith [hq.1, hq.2]
  refine ContinuousLinearMap.opNorm_le_bound Y hC fun φ => ?_
  have h_sq : ‖Y φ‖ ^ 2 ≤ (C * ‖φ‖) ^ 2 := by
    rw [← opEigenbasis_parseval Y hY (Y φ), mul_pow, ← opEigenbasis_parseval Y hY φ, Finset.mul_sum]
    refine Finset.sum_le_sum fun ω _ => ?_
    have h_in : inner ℂ (e ω) (Y φ) = (lam ω : ℂ) * inner ℂ (e ω) φ := by
      dsimp [e, lam]
      rw [← ContinuousLinearMap.adjoint_inner_left,
        ContinuousLinearMap.isSelfAdjoint_iff'.mp hY,
        opEigenbasis_apply_H Y hY ω, inner_smul_left, Complex.conj_ofReal]
    rw [h_in, norm_mul, Complex.norm_real, Real.norm_eq_abs, mul_pow, sq_abs]
    exact mul_le_mul_of_nonneg_right (h_lam_sq ω) (sq_nonneg _)
  calc ‖Y φ‖
    _ = Real.sqrt (‖Y φ‖ ^ 2) := (Real.sqrt_sq (norm_nonneg _)).symm
    _ ≤ Real.sqrt ((C * ‖φ‖) ^ 2) := Real.sqrt_le_sqrt h_sq
    _ = C * ‖φ‖ := Real.sqrt_sq (mul_nonneg hC (norm_nonneg _))

private lemma isPositiveOp_norm_sub_and_add {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] [CompleteSpace E] {X : E →L[ℂ] E} (hX : IsSelfAdjoint X) :
    IsPositiveOp ((‖X‖ : ℂ) • (1 : E →L[ℂ] E) - X) ∧
      IsPositiveOp ((‖X‖ : ℂ) • (1 : E →L[ℂ] E) + X) := by
  have h1_adj : (1 : E →L[ℂ] E)† = 1 := by
    ext ψ; apply ext_inner_right ℂ; intro χ
    rw [ContinuousLinearMap.adjoint_inner_left, one_apply_eq_self, one_apply_eq_self]
  have h_smul_adj : ((‖X‖ : ℂ) • (1 : E →L[ℂ] E))† = (‖X‖ : ℂ) • 1 := by
    rw [adjoint_smul_clm, Complex.conj_ofReal, h1_adj]
  have hX_adj : X† = X := ContinuousLinearMap.isSelfAdjoint_iff'.mp hX
  have h_re_bound : ∀ ψ : E,
      -‖X‖ * ‖ψ‖ ^ 2 ≤ RCLike.re (inner ℂ ψ (X ψ)) ∧
        RCLike.re (inner ℂ ψ (X ψ)) ≤ ‖X‖ * ‖ψ‖ ^ 2 := fun ψ => by
    have h_norm : ‖inner ℂ ψ (X ψ)‖ ≤ ‖X‖ * ‖ψ‖ ^ 2 := by
      calc ‖inner ℂ ψ (X ψ)‖
        _ ≤ ‖ψ‖ * ‖X ψ‖ := norm_inner_le_norm _ _
        _ ≤ ‖ψ‖ * (‖X‖ * ‖ψ‖) := mul_le_mul_of_nonneg_left (ContinuousLinearMap.le_opNorm X ψ) (norm_nonneg _)
        _ = ‖X‖ * ‖ψ‖ ^ 2 := by ring
    have h1 : RCLike.re (inner ℂ ψ (X ψ)) ≤ ‖inner ℂ ψ (X ψ)‖ := RCLike.re_le_norm _
    have h2 : -RCLike.re (inner ℂ ψ (X ψ)) ≤ ‖inner ℂ ψ (X ψ)‖ := by
      simpa only [map_neg, norm_neg] using RCLike.re_le_norm (-inner ℂ ψ (X ψ))
    exact ⟨by linarith, by linarith⟩
  refine ⟨⟨?_, fun ψ => ?_⟩, ⟨?_, fun ψ => ?_⟩⟩
  · rw [ContinuousLinearMap.isSelfAdjoint_iff', map_sub, h_smul_adj, hX_adj]
  · rw [sub_apply, smul_apply, one_apply_eq_self, inner_sub_right, inner_smul_right,
      map_sub, re_ofReal_mul, ← norm_sq_eq_re_inner (𝕜 := ℂ)]
    linarith [(h_re_bound ψ).2]
  · rw [ContinuousLinearMap.isSelfAdjoint_iff', map_add, h_smul_adj, hX_adj]
  · rw [add_apply, smul_apply, one_apply_eq_self, inner_add_right, inner_smul_right,
      map_add, re_ofReal_mul, ← norm_sq_eq_re_inner (𝕜 := ℂ)]
    linarith [(h_re_bound ψ).1]

private lemma le_of_pow_two_pow_le {a b M : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hM : 0 ≤ M)
    (h_iter : ∀ k : ℕ, a ^ (2 ^ (k + 1)) ≤ b ^ (2 ^ (k + 1) - 1) * M) :
    a ≤ b := by
  let _ := ha
  let _ := hM
  by_contra! hab
  have ha_pos : 0 < a := lt_of_le_of_lt hb hab
  rcases eq_or_lt_of_le hb with rfl | hb_pos
  · have h1 := h_iter 1
    norm_num at h1
    linarith [pow_pos ha_pos 4]
  · let δ := a / b - 1
    have hδ_pos : 0 < δ := by
      dsimp [δ]; linarith [(one_lt_div hb_pos).mpr hab]
    have h_bern : ∀ n : ℕ, 1 + (n : ℝ) * δ ≤ (1 + δ) ^ n := by
      intro n
      induction n with
      | zero => simp
      | succ n ih =>
          rw [pow_succ]
          push_cast
          have h_step := mul_le_mul_of_nonneg_right ih (by linarith : 0 ≤ 1 + δ)
          have h_nδ2 : 0 ≤ (n : ℝ) * δ ^ 2 := mul_nonneg (Nat.cast_nonneg n) (sq_nonneg δ)
          linarith
    have h_pow2 : ∀ k : ℕ, k + 1 ≤ 2 ^ (k + 1) := by
      intro k
      induction k with
      | zero => norm_num
      | succ k ih => rw [pow_succ]; omega
    have h_lin_all : ∀ k : ℕ, b * (1 + ((k + 1 : ℕ) : ℝ) * δ) ≤ M := fun k => by
      set N := 2 ^ (k + 1)
      have hN1 : 1 ≤ N := Nat.one_le_pow (k + 1) 2 (by norm_num)
      have ha_eq : a = b * (1 + δ) := by
        dsimp [δ]; field_simp [ne_of_gt hb_pos]; ring
      have hbN_pos : 0 < b ^ N := pow_pos hb_pos N
      have h_mul := mul_le_mul_of_nonneg_left (h_iter k) (le_of_lt hb_pos)
      have h_rhs : b * (b ^ (N - 1) * M) = b ^ N * M := by
        rw [← mul_assoc, ← pow_succ', Nat.sub_add_cancel hN1]
      have h_lhs : b * a ^ N = b ^ N * (b * (1 + δ) ^ N) := by
        rw [ha_eq, mul_pow]; ring
      rw [h_lhs, h_rhs] at h_mul
      have h_b_pow : b * (1 + δ) ^ N ≤ M := le_of_mul_le_mul_left h_mul hbN_pos
      have h_kN : ((k + 1 : ℕ) : ℝ) ≤ (N : ℝ) := Nat.cast_le.mpr (h_pow2 k)
      have h_step : 1 + ((k + 1 : ℕ) : ℝ) * δ ≤ (1 + δ) ^ N :=
        le_trans (by nlinarith) (h_bern N)
      exact le_trans (mul_le_mul_of_nonneg_left h_step (le_of_lt hb_pos)) h_b_pow
    let k₀ := Nat.ceil (M / (b * δ))
    have hbd_pos : 0 < b * δ := mul_pos hb_pos hδ_pos
    have hk₀ : M ≤ (k₀ : ℝ) * (b * δ) := by
      have hc := Nat.le_ceil (M / (b * δ))
      have hm := mul_le_mul_of_nonneg_right hc (le_of_lt hbd_pos)
      rwa [div_mul_cancel₀ M (ne_of_gt hbd_pos)] at hm
    have hk₀_bound := h_lin_all k₀
    push_cast at hk₀_bound
    nlinarith

private lemma kmsNormSq_add_I_smul_of_selfAdjoint {D L_box : ℕ}
    {Site : BoxD D L_box → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    (H : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site)
    (hH : IsSelfAdjoint H) (β : ℝ)
    {U V : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site}
    (hU : IsSelfAdjoint U) (hV : IsSelfAdjoint V) :
    opKMSNormSq H hH β (U + Complex.I • V) =
      opKMSNormSq H hH β U + opKMSNormSq H hH β V := by
  let ψ_eig := opEigenbasis H hH
  let E_eig := opEigenvalues H hH
  have h_orth : kmsInnerReal ψ_eig E_eig β U (Complex.I • V) = 0 := by
    unfold kmsInnerReal
    rw [ContinuousLinearMap.isSelfAdjoint_iff'.mp hU, clm_mul_smul]
    exact (hilbertTrace_I_smul_mul_eq_zero
      (isSelfAdjoint_conj_self (isSelfAdjoint_gibbsSqrtOp ψ_eig E_eig β) hU) hV
      (fun Z => hilbertTrace_mul_comm_aux _ Z)).1
  have h_add_left : ∀ X₁ X₂ Y,
      kmsInnerReal ψ_eig E_eig β (X₁ + X₂) Y =
        kmsInnerReal ψ_eig E_eig β X₁ Y + kmsInnerReal ψ_eig E_eig β X₂ Y := fun X₁ X₂ Y => by
    rw [kmsInnerReal_symm, kmsInnerReal_add_right,
      kmsInnerReal_symm ψ_eig E_eig β Y X₁, kmsInnerReal_symm ψ_eig E_eig β Y X₂]
  unfold opKMSNormSq kmsNormSq
  rw [h_add_left, kmsInnerReal_add_right, kmsInnerReal_add_right,
    kmsInnerReal_symm ψ_eig E_eig β (Complex.I • V) U, h_orth]
  have h_I_sq : kmsInnerReal ψ_eig E_eig β (Complex.I • V) (Complex.I • V) =
      kmsInnerReal ψ_eig E_eig β V V :=
    kmsNormSq_I_smul ψ_eig E_eig β V
  linarith

private lemma nonpos_of_hasDerivAt_zero_of_le_right {g : ℝ → ℝ} {g' : ℝ}
    (hg : HasDerivAt g g' 0) (h_le : ∀ t : ℝ, 0 ≤ t → g t ≤ g 0) :
    g' ≤ 0 := by
  by_contra! hg'_pos
  have h_t := hasDerivAt_iff_tendsto.mp hg
  have h_ev := Metric.tendsto_nhds.mp h_t (g' / 2) (by linarith)
  rcases Metric.eventually_nhds_iff.mp h_ev with ⟨r, hr_pos, hr⟩
  let u := r / 2
  have hu_pos : 0 < u := by dsimp [u]; linarith
  have hu_dist : dist u 0 < r := by
    rw [Real.dist_eq, sub_zero, abs_of_pos hu_pos]; dsimp [u]; linarith
  have hb := hr hu_dist
  have h_nonneg : 0 ≤ ‖u - 0‖⁻¹ * ‖g u - g 0 - (u - 0) • g'‖ := by positivity
  rw [Real.dist_0_eq_abs, abs_of_nonneg h_nonneg, sub_zero,
    Real.norm_of_nonneg (le_of_lt hu_pos), smul_eq_mul] at hb
  have h_mul := mul_lt_mul_of_pos_left hb hu_pos
  rw [← mul_assoc, mul_inv_cancel₀ (ne_of_gt hu_pos), one_mul] at h_mul
  have h_le_norm : -(g u - g 0 - u * g') ≤ ‖g u - g 0 - u * g'‖ := by
    rw [Real.norm_eq_abs]; exact neg_le_abs _
  have hgu : g u ≤ g 0 := h_le u (le_of_lt hu_pos)
  nlinarith

/-- **Positivity-Preserving KMS-Symmetric Semigroups Are KMS Contractions and Dissipative
    (Part II, Section 2, Remark following Definition 2.6 (`def:kms-lindblad`))**:
    Every unital (`L_diss 1 = 0`), $\dagger$-preserving (`IsStarPreservingMap L_diss`) superoperator
    whose generated semigroup $\Phi_t = e^{t \mathcal{L}_{\beta,\mathrm{diss}}^*}$ preserves operator
    positivity for all $t \ge 0$ and is symmetric with respect to `kmsInnerReal` contracts `opKMSNorm`
    and satisfies `IsKMSSymmetricDissipativeGenerator`. -/
theorem isKMSSymmetricDissipativeGenerator_of_positivityPreserving_semigroup {D L_box : ℕ}
    {Site : BoxD D L_box → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    [∀ x, Nonempty (Site x)]
    (H : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site)
    (hH : IsSelfAdjoint H) (β : ℝ)
    (L_diss : (ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site) →L[ℂ]
      (ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site))
    (h_unital : L_diss 1 = 0)
    (h_star : IsStarPreservingMap L_diss)
    (h_symm : ∀ A B,
      kmsInnerReal (opEigenbasis H hH) (opEigenvalues H hH) β A (L_diss B) =
        kmsInnerReal (opEigenbasis H hH) (opEigenvalues H hH) β (L_diss A) B)
    (h_pos : ∀ t : ℝ, 0 ≤ t →
      IsPositivityPreservingMap (NormedSpace.exp ((t : ℂ) • L_diss))) :
    (∀ t : ℝ, 0 ≤ t → ∀ A,
      opKMSNorm H hH β (NormedSpace.exp ((t : ℂ) • L_diss) A) ≤ opKMSNorm H hH β A) ∧
    IsKMSSymmetricDissipativeGenerator H hH β L_diss := by
  let Φ := fun t : ℝ => NormedSpace.exp ((t : ℂ) • L_diss)
  have hΦ_sa_opNorm : ∀ {t : ℝ}, 0 ≤ t →
      ∀ {X : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site},
      IsSelfAdjoint X → IsSelfAdjoint (Φ t X) ∧ opKMSNorm H hH β (Φ t X) ≤ ‖X‖ := by
    intro t ht X hX
    have hΦX_sa : IsSelfAdjoint (Φ t X) := by
      rw [ContinuousLinearMap.isSelfAdjoint_iff', isStarPreservingMap_exp_real_smul h_star t X,
        ContinuousLinearMap.isSelfAdjoint_iff'.mp hX]
    rcases isPositiveOp_norm_sub_and_add hX with ⟨hp_sub, hp_add⟩
    have h_pos_sub := (h_pos t ht _ hp_sub).2
    have h_pos_add := (h_pos t ht _ hp_add).2
    have hΦ1 : Φ t 1 = 1 := exp_real_smul_one_eq_one h_unital t
    have h_quad : ∀ ψ : ManyBodyHilbertSpace Site,
        -‖X‖ * ‖ψ‖ ^ 2 ≤ RCLike.re (inner ℂ ψ (Φ t X ψ)) ∧
          RCLike.re (inner ℂ ψ (Φ t X ψ)) ≤ ‖X‖ * ‖ψ‖ ^ 2 := fun ψ => by
      have h1 := h_pos_sub ψ
      have h2 := h_pos_add ψ
      rw [map_sub, map_smul, hΦ1, sub_apply, smul_apply, one_apply_eq_self,
        inner_sub_right, inner_smul_right, map_sub, re_ofReal_mul, ← norm_sq_eq_re_inner (𝕜 := ℂ)] at h1
      rw [map_add, map_smul, hΦ1, add_apply, smul_apply, one_apply_eq_self,
        inner_add_right, inner_smul_right, map_add, re_ofReal_mul, ← norm_sq_eq_re_inner (𝕜 := ℂ)] at h2
      exact ⟨by linarith, by linarith⟩
    refine ⟨hΦX_sa, le_trans (opKMSNorm_le_opNorm H hH β (Φ t X))
      (opNorm_le_of_quadForm_le hΦX_sa (norm_nonneg X) h_quad)⟩
  have h_doubling : ∀ {s : ℝ}, 0 ≤ s →
      ∀ (X : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site),
      (opKMSNorm H hH β (Φ s X)) ^ 2 ≤
        opKMSNorm H hH β X * opKMSNorm H hH β (Φ (2 * s) X) := by
    intro s _ X
    have h_nn : 0 ≤ kmsNormSq (opEigenbasis H hH) (opEigenvalues H hH) β (Φ s X) :=
      kmsNormSq_nonneg (opEigenbasis H hH) (opEigenvalues H hH) β
        (opEigenbasis_orthonormal H hH) (hilbertTrace_eq_sum_opEigenbasis H hH) (Φ s X)
    have h_two : 2 * s = s + s := by ring
    calc (opKMSNorm H hH β (Φ s X)) ^ 2
      _ = kmsInnerReal (opEigenbasis H hH) (opEigenvalues H hH) β (Φ s X) (Φ s X) :=
          Real.sq_sqrt h_nn
      _ = kmsInnerReal (opEigenbasis H hH) (opEigenvalues H hH) β X (Φ s (Φ s X)) :=
          (kmsInnerReal_exp_real_smul_symm H hH β h_symm s X (Φ s X)).symm
      _ = kmsInnerReal (opEigenbasis H hH) (opEigenvalues H hH) β X (Φ (2 * s) X) := by
          rw [h_two, exp_real_smul_add_apply L_diss s s X]
      _ ≤ opKMSNorm H hH β X * opKMSNorm H hH β (Φ (2 * s) X) :=
          kmsInnerReal_le_kmsNorm_mul_kmsNorm (opEigenbasis H hH) (opEigenvalues H hH) β
            (opEigenbasis_orthonormal H hH) (hilbertTrace_eq_sum_opEigenbasis H hH) X _
  have h_contr_sa : ∀ {t : ℝ}, 0 ≤ t →
      ∀ {X : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site},
      IsSelfAdjoint X → opKMSNorm H hH β (Φ t X) ≤ opKMSNorm H hH β X := by
    intro t ht X hX
    have h_iter : ∀ (k : ℕ) {s : ℝ}, 0 ≤ s →
        (opKMSNorm H hH β (Φ s X)) ^ (2 ^ (k + 1)) ≤
          (opKMSNorm H hH β X) ^ (2 ^ (k + 1) - 1) * ‖X‖ := by
      intro k
      induction k with
      | zero =>
          intro s hs
          norm_num
          calc (opKMSNorm H hH β (Φ s X)) ^ 2
            _ ≤ opKMSNorm H hH β X * opKMSNorm H hH β (Φ (2 * s) X) := h_doubling hs X
            _ ≤ opKMSNorm H hH β X * ‖X‖ :=
                mul_le_mul_of_nonneg_left (hΦ_sa_opNorm (by linarith) hX).2 (Real.sqrt_nonneg _)
      | succ k ih =>
          intro s hs
          have h_exp : 2 ^ (k + 2) = 2 * 2 ^ (k + 1) := by ring
          have h_sub_exp : 2 ^ (k + 1) + (2 ^ (k + 1) - 1) = 2 ^ (k + 2) - 1 := by
            have h1 : 1 ≤ 2 ^ (k + 1) := Nat.one_le_pow (k + 1) 2 (by norm_num)
            omega
          calc (opKMSNorm H hH β (Φ s X)) ^ (2 ^ (k + 2))
            _ = ((opKMSNorm H hH β (Φ s X)) ^ 2) ^ (2 ^ (k + 1)) := by rw [h_exp, pow_mul]
            _ ≤ (opKMSNorm H hH β X * opKMSNorm H hH β (Φ (2 * s) X)) ^ (2 ^ (k + 1)) :=
                pow_le_pow_left₀ (sq_nonneg _) (h_doubling hs X) _
            _ = (opKMSNorm H hH β X) ^ (2 ^ (k + 1)) *
                  (opKMSNorm H hH β (Φ (2 * s) X)) ^ (2 ^ (k + 1)) := mul_pow _ _ _
            _ ≤ (opKMSNorm H hH β X) ^ (2 ^ (k + 1)) *
                  ((opKMSNorm H hH β X) ^ (2 ^ (k + 1) - 1) * ‖X‖) :=
                mul_le_mul_of_nonneg_left (ih (by linarith)) (pow_nonneg (Real.sqrt_nonneg _) _)
            _ = (opKMSNorm H hH β X) ^ (2 ^ (k + 2) - 1) * ‖X‖ := by
                rw [← mul_assoc, ← pow_add, h_sub_exp]
    exact le_of_pow_two_pow_le (Real.sqrt_nonneg _) (Real.sqrt_nonneg _) (norm_nonneg X)
      (fun k => h_iter k ht)
  have h_contr : ∀ t : ℝ, 0 ≤ t → ∀ A, opKMSNorm H hH β (Φ t A) ≤ opKMSNorm H hH β A := by
    intro t ht A
    let X := (1 / 2 : ℂ) • (A + A†)
    let Y := (-Complex.I / 2 : ℂ) • (A - A†)
    have hX_sa : IsSelfAdjoint X := by
      rw [ContinuousLinearMap.isSelfAdjoint_iff']
      dsimp [X]
      have h_half : (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) := by norm_num
      rw [h_half, adjoint_smul_clm, Complex.conj_ofReal, map_add,
        ContinuousLinearMap.adjoint_adjoint, add_comm]
    have hY_sa : IsSelfAdjoint Y := by
      rw [ContinuousLinearMap.isSelfAdjoint_iff']
      dsimp [Y]
      have h_conj : starRingEnd ℂ (-Complex.I / 2 : ℂ) = (Complex.I / 2 : ℂ) := by
        have h2 : (-Complex.I / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) * (-Complex.I) := by push_cast; ring
        rw [h2, map_mul, Complex.conj_ofReal, map_neg, Complex.conj_I]
        push_cast; ring
      rw [adjoint_smul_clm, h_conj, map_sub, ContinuousLinearMap.adjoint_adjoint]
      have h_neg : (Complex.I / 2 : ℂ) = -(-Complex.I / 2 : ℂ) := by ring
      rw [h_neg, neg_smul, ← smul_neg, neg_sub]
    have hA_eq : A = X + Complex.I • Y := by
      dsimp [X, Y]
      rw [smul_smul]
      have hI : Complex.I * (-Complex.I / 2 : ℂ) = (1 / 2 : ℂ) := by
        calc Complex.I * (-Complex.I / 2 : ℂ)
          _ = -(Complex.I * Complex.I) / 2 := by ring
          _ = (1 / 2 : ℂ) := by rw [Complex.I_mul_I]; ring
      rw [hI]
      have h_alg : (1 / 2 : ℂ) • (A + A†) + (1 / 2 : ℂ) • (A - A†) =
          ((1 / 2 : ℂ) + (1 / 2 : ℂ)) • A := by
        rw [smul_add, smul_sub, _root_.add_smul (1 / 2 : ℂ) (1 / 2 : ℂ) A]
        abel
      have h_one : (1 / 2 : ℂ) + (1 / 2 : ℂ) = 1 := by norm_num
      rw [h_alg, h_one, one_smul]
    have hΦA_eq : Φ t A = Φ t X + Complex.I • Φ t Y := by
      conv_lhs => rw [hA_eq]
      rw [map_add (Φ t) X (Complex.I • Y), map_smul (Φ t) Complex.I Y]
    have hX_sq : opKMSNormSq H hH β (Φ t X) ≤ opKMSNormSq H hH β X := by
      have hc := h_contr_sa ht hX_sa
      have h1 : 0 ≤ opKMSNormSq H hH β (Φ t X) :=
        kmsNormSq_nonneg (opEigenbasis H hH) (opEigenvalues H hH) β
          (opEigenbasis_orthonormal H hH) (hilbertTrace_eq_sum_opEigenbasis H hH) (Φ t X)
      have h2 : 0 ≤ opKMSNormSq H hH β X :=
        kmsNormSq_nonneg (opEigenbasis H hH) (opEigenvalues H hH) β
          (opEigenbasis_orthonormal H hH) (hilbertTrace_eq_sum_opEigenbasis H hH) X
      have hsq := mul_self_le_mul_self (Real.sqrt_nonneg _) hc
      change Real.sqrt (opKMSNormSq H hH β (Φ t X)) * Real.sqrt (opKMSNormSq H hH β (Φ t X)) ≤
        Real.sqrt (opKMSNormSq H hH β X) * Real.sqrt (opKMSNormSq H hH β X) at hsq
      rwa [Real.mul_self_sqrt h1, Real.mul_self_sqrt h2] at hsq
    have hY_sq : opKMSNormSq H hH β (Φ t Y) ≤ opKMSNormSq H hH β Y := by
      have hc := h_contr_sa ht hY_sa
      have h1 : 0 ≤ opKMSNormSq H hH β (Φ t Y) :=
        kmsNormSq_nonneg (opEigenbasis H hH) (opEigenvalues H hH) β
          (opEigenbasis_orthonormal H hH) (hilbertTrace_eq_sum_opEigenbasis H hH) (Φ t Y)
      have h2 : 0 ≤ opKMSNormSq H hH β Y :=
        kmsNormSq_nonneg (opEigenbasis H hH) (opEigenvalues H hH) β
          (opEigenbasis_orthonormal H hH) (hilbertTrace_eq_sum_opEigenbasis H hH) Y
      have hsq := mul_self_le_mul_self (Real.sqrt_nonneg _) hc
      change Real.sqrt (opKMSNormSq H hH β (Φ t Y)) * Real.sqrt (opKMSNormSq H hH β (Φ t Y)) ≤
        Real.sqrt (opKMSNormSq H hH β Y) * Real.sqrt (opKMSNormSq H hH β Y) at hsq
      rwa [Real.mul_self_sqrt h1, Real.mul_self_sqrt h2] at hsq
    have hA_sq : opKMSNormSq H hH β (Φ t A) ≤ opKMSNormSq H hH β A := by
      rw [hΦA_eq, kmsNormSq_add_I_smul_of_selfAdjoint H hH β
        (hΦ_sa_opNorm ht hX_sa).1 (hΦ_sa_opNorm ht hY_sa).1]
      conv_rhs => rw [hA_eq]
      rw [kmsNormSq_add_I_smul_of_selfAdjoint H hH β hX_sa hY_sa]
      linarith
    exact Real.sqrt_le_sqrt hA_sq
  refine ⟨h_contr, h_unital, h_symm, fun A => ?_⟩
  have h0_eq : Φ 0 A = A := exp_zero_smul_apply L_diss A
  have hd0 : HasDerivAt (fun u : ℝ => Φ u A) (L_diss A) 0 :=
    (hasDerivAt_exp_real_smul_apply L_diss A 0).congr_deriv (by rw [exp_zero_smul_apply])
  have hd_norm : HasDerivAt (fun u : ℝ => kmsNormSq (opEigenbasis H hH) (opEigenvalues H hH) β (Φ u A))
      (2 * kmsInnerReal (opEigenbasis H hH) (opEigenvalues H hH) β A (L_diss A)) 0 := by
    simpa only [h0_eq] using hasDerivAt_kmsNormSq H hH β hd0
  have h_le_zero : ∀ u : ℝ, 0 ≤ u →
      kmsNormSq (opEigenbasis H hH) (opEigenvalues H hH) β (Φ u A) ≤
        kmsNormSq (opEigenbasis H hH) (opEigenvalues H hH) β (Φ 0 A) := by
    intro u hu
    rw [h0_eq]
    have hc := h_contr u hu A
    have h1 := kmsNormSq_nonneg (opEigenbasis H hH) (opEigenvalues H hH) β
      (opEigenbasis_orthonormal H hH) (hilbertTrace_eq_sum_opEigenbasis H hH) (Φ u A)
    have h2 := kmsNormSq_nonneg (opEigenbasis H hH) (opEigenvalues H hH) β
      (opEigenbasis_orthonormal H hH) (hilbertTrace_eq_sum_opEigenbasis H hH) A
    have hsq := mul_self_le_mul_self (Real.sqrt_nonneg _) hc
    change Real.sqrt (kmsNormSq (opEigenbasis H hH) (opEigenvalues H hH) β (Φ u A)) *
        Real.sqrt (kmsNormSq (opEigenbasis H hH) (opEigenvalues H hH) β (Φ u A)) ≤
      Real.sqrt (kmsNormSq (opEigenbasis H hH) (opEigenvalues H hH) β A) *
        Real.sqrt (kmsNormSq (opEigenbasis H hH) (opEigenvalues H hH) β A) at hsq
    rwa [Real.mul_self_sqrt h1, Real.mul_self_sqrt h2] at hsq
  have h_deriv_nonpos := nonpos_of_hasDerivAt_zero_of_le_right hd_norm h_le_zero
  linarith

private lemma kmsInnerReal_sub_right {D L_box : ℕ}
    {Site : BoxD D L_box → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    (ψ_eig : ManyBodyConfig Site → ManyBodyHilbertSpace Site)
    (E_eig : ManyBodyConfig Site → ℝ) (β : ℝ)
    (A B₁ B₂ : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site) :
    kmsInnerReal ψ_eig E_eig β A (B₁ - B₂) =
      kmsInnerReal ψ_eig E_eig β A B₁ - kmsInnerReal ψ_eig E_eig β A B₂ := by
  unfold kmsInnerReal
  rw [mul_sub, hilbertTrace_sub]

private lemma kmsInnerReal_sub_left' {D L_box : ℕ}
    {Site : BoxD D L_box → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    (ψ_eig : ManyBodyConfig Site → ManyBodyHilbertSpace Site)
    (E_eig : ManyBodyConfig Site → ℝ) (β : ℝ)
    (A₁ A₂ B : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site) :
    kmsInnerReal ψ_eig E_eig β (A₁ - A₂) B =
      kmsInnerReal ψ_eig E_eig β A₁ B - kmsInnerReal ψ_eig E_eig β A₂ B := by
  rw [kmsInnerReal_symm, kmsInnerReal_sub_right,
    kmsInnerReal_symm ψ_eig E_eig β B A₁, kmsInnerReal_symm ψ_eig E_eig β B A₂]

private lemma kmsInnerReal_sum_right {D L_box : ℕ}
    {Site : BoxD D L_box → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    {α : Type*} (s : Finset α)
    (ψ_eig : ManyBodyConfig Site → ManyBodyHilbertSpace Site)
    (E_eig : ManyBodyConfig Site → ℝ) (β : ℝ)
    (A : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site)
    (f : α → (ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site)) :
    kmsInnerReal ψ_eig E_eig β A (∑ i ∈ s, f i) =
      ∑ i ∈ s, kmsInnerReal ψ_eig E_eig β A (f i) := by
  unfold kmsInnerReal
  rw [Finset.mul_sum, hilbertTrace_sum]

private lemma kmsInnerReal_singleChannel_eq {D L_box : ℕ}
    {Site : BoxD D L_box → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    [∀ x, Nonempty (Site x)]
    (H : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site)
    (hH : IsSelfAdjoint H) (β : ℝ)
    (L_op A B : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site) :
    let ψ_eig := opEigenbasis H hH
    let E_eig := opEigenvalues H hH
    let S := gibbsSqrtOp ψ_eig E_eig β
    let S_inv := gibbsInvSqrtOp ψ_eig E_eig β
    kmsInnerReal ψ_eig E_eig β A
      (S_inv * opCommutator (L_op†) (S * opCommutator L_op B * S) * S_inv) =
      kmsInnerReal ψ_eig E_eig β (opCommutator L_op A) (opCommutator L_op B) := by
  intro ψ_eig E_eig S S_inv
  have h_SSinv : S * S_inv = 1 :=
    gibbsSqrtOp_mul_gibbsInvSqrtOp ψ_eig E_eig β
      (opEigenbasis_orthonormal H hH) (opEigenbasis_parseval H hH)
  have h_SinvS : S_inv * S = 1 :=
    gibbsInvSqrtOp_mul_gibbsSqrtOp ψ_eig E_eig β
      (opEigenbasis_orthonormal H hH) (opEigenbasis_parseval H hH)
  set D_B := opCommutator L_op B
  have h_step1 :
      S * A† * S * (S_inv * opCommutator (L_op†) (S * D_B * S) * S_inv) =
        (S * A† * opCommutator (L_op†) (S * D_B * S)) * S_inv := by
    calc S * A† * S * (S_inv * opCommutator (L_op†) (S * D_B * S) * S_inv)
      _ = (S * A† * (S * S_inv) * opCommutator (L_op†) (S * D_B * S)) * S_inv := by
          simp only [mul_assoc]
      _ = (S * A† * opCommutator (L_op†) (S * D_B * S)) * S_inv := by rw [h_SSinv, mul_one]
  have h_step2 :
      S_inv * (S * A† * opCommutator (L_op†) (S * D_B * S)) =
        (A† * L_op†) * (S * D_B * S) - (A† * (S * D_B * S)) * L_op† := by
    calc S_inv * (S * A† * opCommutator (L_op†) (S * D_B * S))
      _ = (S_inv * S) * A† * (L_op† * (S * D_B * S) - (S * D_B * S) * L_op†) := by
          dsimp [opCommutator]; simp only [mul_assoc]
      _ = A† * (L_op† * (S * D_B * S) - (S * D_B * S) * L_op†) := by rw [h_SinvS, one_mul]
      _ = (A† * L_op†) * (S * D_B * S) - (A† * (S * D_B * S)) * L_op† := by
          rw [mul_sub]; simp only [mul_assoc]
  have h_adj_comm : (opCommutator L_op A)† = A† * L_op† - L_op† * A† := by
    dsimp [opCommutator]
    rw [map_sub]
    exact congrArg₂ Sub.sub (star_mul L_op A) (star_mul A L_op)
  have h_step3 :
      (A† * L_op†) * (S * D_B * S) - L_op† * (A† * (S * D_B * S)) =
        ((opCommutator L_op A)† * S * D_B) * S := by
    rw [← mul_assoc (L_op†) (A†) (S * D_B * S), ← sub_mul, ← h_adj_comm]
    simp only [mul_assoc]
  unfold kmsInnerReal
  change hilbertTrace (S * A† * S * (S_inv * opCommutator (L_op†) (S * D_B * S) * S_inv)) =
    hilbertTrace (S * (opCommutator L_op A)† * S * D_B)
  rw [h_step1, hilbertTrace_mul_comm_aux _ S_inv, h_step2, hilbertTrace_sub,
    hilbertTrace_mul_comm_aux (A† * (S * D_B * S)) (L_op†), ← hilbertTrace_sub,
    h_step3, hilbertTrace_mul_comm_aux _ S]
  simp only [mul_assoc]

/-- **Exact KMS Pre-Dirichlet Identity for `opKMSLindbladDissipator`
    (Part II, Definition 2.6, Equation (`eq:kms-dirichlet-def`) and Theorem 6.2 Step 2)**:
    $2\,\mathcal{E}_\beta(A, B) = \sum_{\mathrm{ch} \in \mathrm{bath}} \gamma_{\mathrm{ch}}\,
    \langle [L_{\mathrm{ch}}, A], [L_{\mathrm{ch}}, B]\rangle_{\mathrm{KMS},\beta}$. -/
theorem kmsDissipativeForm_opKMSLindbladDissipator_eq {D L_box : ℕ}
    {Site : BoxD D L_box → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    [∀ x, Nonempty (Site x)]
    (H : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site)
    (hH : IsSelfAdjoint H) (β : ℝ)
    (bath : Finset (BathChannel D L_box Site))
    (A B : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site) :
    2 * kmsDissipativeForm H hH β (opKMSLindbladDissipator H hH β bath) A B =
      ∑ ch ∈ bath, ch.γ *
        kmsInnerReal (opEigenbasis H hH) (opEigenvalues H hH) β
          (opCommutator ch.L A) (opCommutator ch.L B) := by
  unfold kmsDissipativeForm opKMSLindbladDissipator
  simp only [smul_apply, sum_apply,
    ContinuousLinearMap.comp_apply, clmSandwichOp_apply, opCommutatorCLM_apply]
  have h_half : (-1 / 2 : ℂ) = ((-1 / 2 : ℝ) : ℂ) := by norm_num
  rw [h_half, kmsInnerReal_smul_right, kmsInnerReal_sum_right]
  have h_sum :
      (∑ x ∈ bath,
        kmsInnerReal (opEigenbasis H hH) (opEigenvalues H hH) β A
          ((x.γ : ℂ) •
            (gibbsInvSqrtOp (opEigenbasis H hH) (opEigenvalues H hH) β *
              opCommutator (x.L†)
                (gibbsSqrtOp (opEigenbasis H hH) (opEigenvalues H hH) β *
                  opCommutator x.L B *
                  gibbsSqrtOp (opEigenbasis H hH) (opEigenvalues H hH) β) *
              gibbsInvSqrtOp (opEigenbasis H hH) (opEigenvalues H hH) β))) =
      ∑ ch ∈ bath, ch.γ *
        kmsInnerReal (opEigenbasis H hH) (opEigenvalues H hH) β
          (opCommutator ch.L A) (opCommutator ch.L B) := by
    refine Finset.sum_congr rfl fun ch _ => ?_
    rw [kmsInnerReal_smul_right, kmsInnerReal_singleChannel_eq H hH β ch.L A B]
  rw [h_sum]
  ring

/-- **`opKMSLindbladDissipator` Is a KMS-Symmetric Dissipative Generator
    (Part II, Definition 2.6 (`def:kms-lindblad`) and Theorem 6.2 Step 2)**:
    Whenever $\gamma_{\mathrm{ch}} \ge 0$ for all $\mathrm{ch} \in \mathrm{bath}$,
    `opKMSLindbladDissipator H hH β bath` satisfies `IsKMSSymmetricDissipativeGenerator`. -/
theorem isKMSSymmetricDissipativeGenerator_opKMSLindbladDissipator {D L_box : ℕ}
    {Site : BoxD D L_box → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    [∀ x, Nonempty (Site x)]
    (H : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site)
    (hH : IsSelfAdjoint H) (β : ℝ)
    (bath : Finset (BathChannel D L_box Site))
    (h_nonneg : ∀ ch ∈ bath, 0 ≤ ch.γ) :
    IsKMSSymmetricDissipativeGenerator H hH β (opKMSLindbladDissipator H hH β bath) := by
  refine ⟨?_, ?_, ?_⟩
  · unfold opKMSLindbladDissipator
    ext φ
    simp [clmSandwichOp_apply, opCommutatorCLM_apply, opCommutator]
  · intro A B
    have hAB := kmsDissipativeForm_opKMSLindbladDissipator_eq H hH β bath A B
    have hBA := kmsDissipativeForm_opKMSLindbladDissipator_eq H hH β bath B A
    have h_rhs_eq :
        (∑ ch ∈ bath, ch.γ *
          kmsInnerReal (opEigenbasis H hH) (opEigenvalues H hH) β
            (opCommutator ch.L A) (opCommutator ch.L B)) =
        ∑ ch ∈ bath, ch.γ *
          kmsInnerReal (opEigenbasis H hH) (opEigenvalues H hH) β
            (opCommutator ch.L B) (opCommutator ch.L A) := by
      refine Finset.sum_congr rfl fun ch _ => ?_
      rw [kmsInnerReal_symm]
    unfold kmsDissipativeForm at hAB hBA
    rw [kmsInnerReal_symm _ _ _ (opKMSLindbladDissipator H hH β bath A) B]
    linarith
  · intro A
    have hAA := kmsDissipativeForm_opKMSLindbladDissipator_eq H hH β bath A A
    unfold kmsDissipativeForm at hAA
    have h_sum_nonneg :
        0 ≤ ∑ ch ∈ bath, ch.γ *
          kmsInnerReal (opEigenbasis H hH) (opEigenvalues H hH) β
            (opCommutator ch.L A) (opCommutator ch.L A) := by
      refine Finset.sum_nonneg fun ch hch => mul_nonneg (h_nonneg ch hch) ?_
      exact kmsNormSq_nonneg (opEigenbasis H hH) (opEigenvalues H hH) β
        (opEigenbasis_orthonormal H hH) (hilbertTrace_eq_sum_opEigenbasis H hH)
        (opCommutator ch.L A)
    linarith

private lemma opKMSLindbladGenerator_eq_add_dissipator {D L_box : ℕ}
    {Site : BoxD D L_box → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    (H : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site)
    (hH : IsSelfAdjoint H) (β : ℝ)
    (bath : Finset (BathChannel D L_box Site))
    (X : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site) :
    opKMSLindbladGenerator H hH β bath X =
      Complex.I • opCommutator H X + opKMSLindbladDissipator H hH β bath X := by
  rw [← opKMSLindbladGeneratorCLM_apply]
  rfl

/-- **Equivalence of `SatisfiesKMSLindbladODE` and `SatisfiesKMSDissipativeODE` for `opKMSLindbladDissipator`**. -/
theorem satisfiesKMSLindbladODE_iff_satisfiesKMSDissipativeODE {D L_box : ℕ}
    {Site : BoxD D L_box → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    (H : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site)
    (hH : IsSelfAdjoint H) (β : ℝ)
    (bath : Finset (BathChannel D L_box Site))
    (O_dec : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site)
    (O_t : ℝ → (ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site))
    (t : ℝ) :
    SatisfiesKMSLindbladODE H hH β bath O_dec O_t t ↔
      SatisfiesKMSDissipativeODE H hH β (opKMSLindbladDissipator H hH β bath) O_dec O_t t := by
  unfold SatisfiesKMSLindbladODE SatisfiesKMSDissipativeODE
  simp only [opKMSLindbladGenerator_eq_add_dissipator]

/-- **Matrix-Exponential Semigroup Solves `SatisfiesKMSDissipativeODE` Under $\dagger$-Preservation
    (Part II, Definition 2.6 (`def:kms-lindblad`))**:
    Whenever `L_diss` is $\dagger$-preserving (`IsStarPreservingMap L_diss`) and `O_init` is
    self-adjoint, $O_s := e^{s(i[H,\cdot] + \mathcal{L}_{\beta,\mathrm{diss}}^*)}(O_{\mathrm{init}})$
    satisfies `SatisfiesKMSDissipativeODE` on $[0, t]$ for every $t \ge 0$. -/
theorem satisfiesKMSDissipativeODE_exp_of_isStarPreserving {D L_box : ℕ}
    {Site : BoxD D L_box → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    [∀ x, Nonempty (Site x)]
    (H : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site)
    (hH : IsSelfAdjoint H) (β : ℝ)
    (L_diss : (ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site) →L[ℂ]
      (ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site))
    (h_star : IsStarPreservingMap L_diss)
    (O_init : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site)
    (hO_sa : IsSelfAdjoint O_init)
    {t : ℝ} (ht : 0 ≤ t) :
    SatisfiesKMSDissipativeODE H hH β L_diss O_init
      (fun s => NormedSpace.exp ((s : ℂ) • (Complex.I • opCommutatorCLM H + L_diss)) O_init) t := by
  let _ := ht
  let G := Complex.I • opCommutatorCLM H + L_diss
  let O_s := fun s : ℝ => NormedSpace.exp ((s : ℂ) • G) O_init
  have hG_star : IsStarPreservingMap G := by
    intro X
    have hH_adj : H† = H := ContinuousLinearMap.isSelfAdjoint_iff'.mp hH
    dsimp [G]
    rw [add_apply, map_add, smul_apply, opCommutatorCLM_apply, adjoint_smul_clm,
      Complex.conj_I, h_star X, add_apply, smul_apply, opCommutatorCLM_apply]
    congr 1
    dsimp [opCommutator]
    rw [map_sub, adjoint_mul_clm H X, adjoint_mul_clm X H, hH_adj,
      neg_smul, ← smul_neg, neg_sub]
  refine ⟨?_, ?_, ?_⟩
  · exact exp_zero_smul_apply G O_init
  · intro s _
    rw [ContinuousLinearMap.isSelfAdjoint_iff']
    rw [isStarPreservingMap_exp_real_smul hG_star s O_init,
      ContinuousLinearMap.isSelfAdjoint_iff'.mp hO_sa]
  · refine ⟨fun s => 2 * kmsInnerReal (opEigenbasis H hH) (opEigenvalues H hH) β
        (O_s s - O_init) (G (O_s s)), ?_, ?_⟩
    · intro s _
      have h_deriv_O : HasDerivAt O_s (G (O_s s)) s :=
        hasDerivAt_exp_real_smul_apply G O_init s
      exact hasDerivAt_kmsNormSq H hH β (h_deriv_O.sub_const O_init)
    · intro s _
      have hG_apply : G (O_s s) = Complex.I • opCommutator H (O_s s) + L_diss (O_s s) := by
        dsimp [G]; simp [opCommutatorCLM_apply]
      dsimp only
      rw [hG_apply]
      change (1 / 2 : ℝ) *
          (2 * kmsInnerReal (opEigenbasis H hH) (opEigenvalues H hH) β (O_s s - O_init)
            (Complex.I • opCommutator H (O_s s) + L_diss (O_s s))) =
        kmsInnerReal (opEigenbasis H hH) (opEigenvalues H hH) β (O_s s - O_init)
          (Complex.I • opCommutator H (O_s s) + L_diss (O_s s))
      ring

/-- **Adjoint-Symmetric Bath Semigroup Solves `SatisfiesKMSLindbladODE`
    (Part I, Section 5.5 (`eq:kms-lindblad-generator-def`); Part II, Definition 2.6 (`def:kms-lindblad`), (`eq:lindblad-heisenberg`))**:
    Whenever `IsAdjointSymmetricBath bath` holds, `opKMSLindbladDissipator` is $\dagger$-preserving
    and `fun s => opKMSLindbladSemigroup H hH β bath s O_init` satisfies `SatisfiesKMSLindbladODE`
    on $[0, t]$ for every self-adjoint `O_init` and $t \ge 0$. -/
theorem satisfiesKMSLindbladODE_opKMSLindbladSemigroup {D L_box : ℕ}
    {Site : BoxD D L_box → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    [∀ x, Nonempty (Site x)]
    (H : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site)
    (hH : IsSelfAdjoint H) (β : ℝ)
    (bath : Finset (BathChannel D L_box Site))
    (h_adj : IsAdjointSymmetricBath bath)
    (O_init : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site)
    (hO_sa : IsSelfAdjoint O_init)
    {t : ℝ} (ht : 0 ≤ t) :
    IsStarPreservingMap (opKMSLindbladDissipator H hH β bath) ∧
    SatisfiesKMSLindbladODE H hH β bath O_init
      (fun s => opKMSLindbladSemigroup H hH β bath s O_init) t := by
  have h_star : IsStarPreservingMap (opKMSLindbladDissipator H hH β bath) := by
    rcases h_adj with ⟨inv, h_invol, h_props⟩
    let ψ_eig := opEigenbasis H hH
    let E_eig := opEigenvalues H hH
    let S := gibbsSqrtOp ψ_eig E_eig β
    let S_inv := gibbsInvSqrtOp ψ_eig E_eig β
    have hS : S† = S := ContinuousLinearMap.isSelfAdjoint_iff'.mp (isSelfAdjoint_gibbsSqrtOp ψ_eig E_eig β)
    have hS_inv : S_inv† = S_inv :=
      ContinuousLinearMap.isSelfAdjoint_iff'.mp (isSelfAdjoint_gibbsInvSqrtOp ψ_eig E_eig β)
    have h_chan_adj : ∀ (L_op X : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site),
        (S_inv * opCommutator (L_op†) (S * opCommutator L_op X * S) * S_inv)† =
          S_inv * opCommutator ((L_op†)†) (S * opCommutator (L_op†) (X†) * S) * S_inv := by
      intro L_op X
      have h_inner_adj : (S * opCommutator L_op X * S)† = -(S * opCommutator (L_op†) (X†) * S) := by
        dsimp [opCommutator]
        rw [adjoint_mul_clm, adjoint_mul_clm, hS, map_sub,
          adjoint_mul_clm L_op X, adjoint_mul_clm X L_op]
        simp only [mul_sub, sub_mul, mul_assoc]
        abel
      dsimp [opCommutator] at h_inner_adj ⊢
      rw [adjoint_mul_clm, adjoint_mul_clm, hS_inv, map_sub,
        adjoint_mul_clm (L_op†) _, adjoint_mul_clm _ (L_op†), h_inner_adj]
      simp only [mul_sub, sub_mul, mul_neg, neg_mul, mul_assoc]
      abel
    intro X
    unfold opKMSLindbladDissipator
    simp only [smul_apply, sum_apply, ContinuousLinearMap.comp_apply,
      clmSandwichOp_apply, opCommutatorCLM_apply]
    have h_half : (-1 / 2 : ℂ) = ((-1 / 2 : ℝ) : ℂ) := by norm_num
    rw [h_half, adjoint_smul_clm, Complex.conj_ofReal, map_sum]
    congr 1
    rw [← Finset.sum_attach bath, ← Finset.sum_attach bath]
    let e : {x // x ∈ bath} ≃ {x // x ∈ bath} :=
      { toFun := inv, invFun := inv, left_inv := h_invol, right_inv := h_invol }
    have h_step : ∀ ch : {x // x ∈ bath},
        ((ch.1.γ : ℂ) • (S_inv * opCommutator (ch.1.L†) (S * opCommutator ch.1.L X * S) * S_inv))† =
          ((e ch).1.γ : ℂ) •
            (S_inv * opCommutator ((e ch).1.L†) (S * opCommutator (e ch).1.L (X†) * S) * S_inv) := by
      intro ch
      have hγ : ch.1.γ = (e ch).1.γ := ((h_props ch).1).symm
      have hL : ch.1.L† = (e ch).1.L := ((h_props ch).2).symm
      rw [adjoint_smul_clm, Complex.conj_ofReal, h_chan_adj ch.1.L X, hγ, hL]
    calc ∑ x ∈ bath.attach,
          ((x.1.γ : ℂ) •
            (S_inv * opCommutator (x.1.L†) (S * opCommutator x.1.L X * S) * S_inv))†
      _ = ∑ ch : {x // x ∈ bath},
          ((e ch).1.γ : ℂ) •
            (S_inv * opCommutator ((e ch).1.L†) (S * opCommutator (e ch).1.L (X†) * S) * S_inv) :=
          Finset.sum_congr rfl fun ch _ => h_step ch
      _ = ∑ ch : {x // x ∈ bath},
          (ch.1.γ : ℂ) •
            (S_inv * opCommutator (ch.1.L†) (S * opCommutator ch.1.L (X†) * S) * S_inv) :=
          Fintype.sum_equiv e _ _ (fun _ => rfl)
  refine ⟨h_star, ?_⟩
  rw [satisfiesKMSLindbladODE_iff_satisfiesKMSDissipativeODE]
  exact satisfiesKMSDissipativeODE_exp_of_isStarPreserving H hH β
    (opKMSLindbladDissipator H hH β bath) h_star O_init hO_sa ht

private lemma kmsDissipativeForm_symm {D L_box : ℕ}
    {Site : BoxD D L_box → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    (H : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site)
    (hH : IsSelfAdjoint H) (β : ℝ)
    {L_diss : (ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site) →L[ℂ]
      (ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site)}
    (hL_gen : IsKMSSymmetricDissipativeGenerator H hH β L_diss)
    (A B : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site) :
    kmsDissipativeForm H hH β L_diss A B = kmsDissipativeForm H hH β L_diss B A := by
  unfold kmsDissipativeForm
  rw [hL_gen.2.1 A B, kmsInnerReal_symm]

private lemma kmsDissipativeForm_le_sqrt_mul_sqrt {D L_box : ℕ}
    {Site : BoxD D L_box → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    (H : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site)
    (hH : IsSelfAdjoint H) (β : ℝ)
    {L_diss : (ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site) →L[ℂ]
      (ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site)}
    (hL_gen : IsKMSSymmetricDissipativeGenerator H hH β L_diss)
    (A B : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site) :
    |kmsDissipativeForm H hH β L_diss A B| ≤
      Real.sqrt (kmsDissipativeForm H hH β L_diss A A) *
        Real.sqrt (kmsDissipativeForm H hH β L_diss B B) := by
  set EA := kmsDissipativeForm H hH β L_diss A A
  set EB := kmsDissipativeForm H hH β L_diss B B
  set EAB := kmsDissipativeForm H hH β L_diss A B
  have hEA : 0 ≤ EA := hL_gen.2.2 A
  have hEB : 0 ≤ EB := hL_gen.2.2 B
  have h_quad : ∀ r : ℝ, 0 ≤ EA - 2 * r * EAB + r ^ 2 * EB := fun r => by
    have h_nonneg := hL_gen.2.2 (A - (r : ℂ) • B)
    have h_symm_BA : kmsDissipativeForm H hH β L_diss B A = EAB :=
      kmsDissipativeForm_symm H hH β hL_gen B A
    have h_exp : -kmsInnerReal (opEigenbasis H hH) (opEigenvalues H hH) β
        (A - (r : ℂ) • B) (L_diss (A - (r : ℂ) • B)) =
        EA - r * EAB - r * kmsDissipativeForm H hH β L_diss B A + r ^ 2 * EB := by
      rw [map_sub, map_smul, kmsInnerReal_sub_left', kmsInnerReal_sub_right,
        kmsInnerReal_sub_right, kmsInnerReal_smul_right, kmsInnerReal_smul_left,
        kmsInnerReal_smul_left, kmsInnerReal_smul_right]
      dsimp [EA, EB, EAB, kmsDissipativeForm]
      ring
    rw [h_exp, h_symm_BA] at h_nonneg
    linarith
  have h_sq : EAB ^ 2 ≤ EA * EB := by
    rcases eq_or_lt_of_le hEB with hEB_zero | hEB_pos
    · have hEAB_zero : EAB = 0 := by
        by_contra h_ne
        have hq := h_quad ((EA + 1) / (2 * EAB))
        rw [← hEB_zero, mul_zero, add_zero] at hq
        have h_cancel : 2 * ((EA + 1) / (2 * EAB)) * EAB = EA + 1 := by
          field_simp [h_ne]
        linarith
      rw [hEAB_zero, ← hEB_zero]; norm_num
    · have hq := h_quad (EAB / EB)
      have h_mul := mul_le_mul_of_nonneg_right hq (le_of_lt hEB_pos)
      have h_simp : (EA - 2 * (EAB / EB) * EAB + (EAB / EB) ^ 2 * EB) * EB =
          EA * EB - EAB ^ 2 := by
        field_simp [ne_of_gt hEB_pos]; ring
      linarith
  calc |EAB|
    _ = Real.sqrt (EAB ^ 2) := (Real.sqrt_sq_eq_abs EAB).symm
    _ ≤ Real.sqrt (EA * EB) := Real.sqrt_le_sqrt h_sq
    _ = Real.sqrt EA * Real.sqrt EB := Real.sqrt_mul hEA EB

private lemma kmsInnerReal_sub_dissipative_le {D L_box : ℕ}
    {Site : BoxD D L_box → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    (H : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site)
    (hH : IsSelfAdjoint H) (β : ℝ)
    {L_diss : (ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site) →L[ℂ]
      (ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site)}
    (hL_gen : IsKMSSymmetricDissipativeGenerator H hH β L_diss)
    (O_init O_s : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site) :
    kmsInnerReal (opEigenbasis H hH) (opEigenvalues H hH) β (O_s - O_init) (L_diss O_s) ≤
      (1 / 4 : ℝ) * kmsDissipativeForm H hH β L_diss O_init O_init := by
  have h_ibp :
      kmsInnerReal (opEigenbasis H hH) (opEigenvalues H hH) β (O_s - O_init) (L_diss O_s) =
        -kmsDissipativeForm H hH β L_diss O_s O_s +
          kmsDissipativeForm H hH β L_diss O_init O_s := by
    rw [kmsInnerReal_sub_left']
    unfold kmsDissipativeForm
    ring
  have h_cs :
      kmsDissipativeForm H hH β L_diss O_init O_s ≤
        Real.sqrt (kmsDissipativeForm H hH β L_diss O_init O_init) *
          Real.sqrt (kmsDissipativeForm H hH β L_diss O_s O_s) :=
    le_trans (le_abs_self _) (kmsDissipativeForm_le_sqrt_mul_sqrt H hH β hL_gen O_init O_s)
  have hE0 : 0 ≤ kmsDissipativeForm H hH β L_diss O_init O_init := hL_gen.2.2 O_init
  have hEs : 0 ≤ kmsDissipativeForm H hH β L_diss O_s O_s := hL_gen.2.2 O_s
  have h_young := kms_dirichlet_young_ineq hE0 hEs
  linarith

/-- **General KMS Drift–Dissipation Grönwall Bound
    (`opKMSNorm_sub_le_kmsDriftDirichletBound_of_dissipativeODE`;
    Part II, Section 6.2 (`subsec:kms-gronwall`), Theorem 6.2 (`thm:kms-gronwall-bare`))**:
    For any self-adjoint Hamiltonian $H$, any `IsKMSSymmetricDissipativeGenerator H hH β L_diss`,
    and any self-adjoint initial observable $O_{\mathrm{init}}$ with
    $\|[H, O_{\mathrm{init}}]\|_{\mathrm{KMS},\beta} \le \Gamma_{\mathrm{coh}}$ and
    $2\,\mathcal{E}_\beta(O_{\mathrm{init}}, O_{\mathrm{init}}) \le \Gamma_{\mathrm{diss}}$,
    every trajectory satisfying `SatisfiesKMSDissipativeODE` obeys
    $\|O_t - O_{\mathrm{init}}\|_{\mathrm{KMS},\beta} \le t\,\Gamma_{\mathrm{coh}} + \sqrt{(t/2)\,\Gamma_{\mathrm{diss}}}$. -/
theorem opKMSNorm_sub_le_kmsDriftDirichletBound_of_dissipativeODE {D L_box : ℕ}
    {Site : BoxD D L_box → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    [∀ x, Nonempty (Site x)]
    (H : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site)
    (hH : IsSelfAdjoint H) (β : ℝ)
    (L_diss : (ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site) →L[ℂ]
      (ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site))
    (hL_gen : IsKMSSymmetricDissipativeGenerator H hH β L_diss)
    (O_init : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site)
    (hO_sa : IsSelfAdjoint O_init)
    {Γ_coh Γ_diss t : ℝ}
    (hΓ_coh : 0 ≤ Γ_coh) (hΓ_diss : 0 ≤ Γ_diss) (ht : 0 ≤ t)
    (h_coh : opKMSNorm H hH β (opCommutator H O_init) ≤ Γ_coh)
    (h_diss : 2 * kmsDissipativeForm H hH β L_diss O_init O_init ≤ Γ_diss)
    {O_t : ℝ → (ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site)}
    (h_ode : SatisfiesKMSDissipativeODE H hH β L_diss O_init O_t t) :
    opKMSNorm H hH β (O_t t - O_init) ≤ kmsDriftDirichletBound Γ_coh Γ_diss t := by
  let ψ_eig := opEigenbasis H hH
  let E_eig := opEigenvalues H hH
  rcases h_ode with ⟨hO0, hOs_sa, f', hf_deriv, hf_eq⟩
  let f : ℝ → ℝ := fun u => kmsNormSq ψ_eig E_eig β (O_t u - O_init)
  have hf0 : f 0 ≤ 0 := by
    dsimp [f, kmsNormSq, kmsInnerReal]
    rw [hO0, sub_self, map_zero, mul_zero, hilbertTrace_zero]
  have hf_nonneg : ∀ s ∈ Set.Icc 0 t, 0 ≤ f s := fun s _ =>
    kmsNormSq_nonneg ψ_eig E_eig β
      (opEigenbasis_orthonormal H hH) (hilbertTrace_eq_sum_opEigenbasis H hH) (O_t s - O_init)
  have hf_ineq : ∀ s ∈ Set.Icc 0 t,
      f' s ≤ 2 * Γ_coh * Real.sqrt (f s) + (1 / 2 : ℝ) * Γ_diss := by
    intro s hs
    have hΔ_sa : IsSelfAdjoint (O_t s - O_init) := by
      have hOs := ContinuousLinearMap.isSelfAdjoint_iff'.mp (hOs_sa s hs)
      have hOi := ContinuousLinearMap.isSelfAdjoint_iff'.mp hO_sa
      rw [ContinuousLinearMap.isSelfAdjoint_iff', map_sub, hOs, hOi]
    have h_split :
        (1 / 2 : ℝ) * f' s =
          kmsInnerReal ψ_eig E_eig β (O_t s - O_init)
            (Complex.I • opCommutator H (O_t s - O_init)) +
          kmsInnerReal ψ_eig E_eig β (O_t s - O_init)
            (Complex.I • opCommutator H O_init) +
          kmsInnerReal ψ_eig E_eig β (O_t s - O_init) (L_diss (O_t s)) := by
      rw [hf_eq s hs, kmsInnerReal_add_right,
        opCommutator_sub_add_cancel H (O_t s) O_init, kmsInnerReal_add_right]
    have h_skew :
        kmsInnerReal ψ_eig E_eig β (O_t s - O_init)
          (Complex.I • opCommutator H (O_t s - O_init)) = 0 :=
      kmsInnerReal_commutator_eq_zero H ψ_eig E_eig β
        (opEigenbasis_ketBra_props H hH) (O_t s - O_init) hΔ_sa
    have h_coh_s :
        kmsInnerReal ψ_eig E_eig β (O_t s - O_init)
          (Complex.I • opCommutator H O_init) ≤ Γ_coh * Real.sqrt (f s) := by
      calc kmsInnerReal ψ_eig E_eig β (O_t s - O_init) (Complex.I • opCommutator H O_init)
        _ ≤ kmsNorm ψ_eig E_eig β (O_t s - O_init) *
              kmsNorm ψ_eig E_eig β (Complex.I • opCommutator H O_init) :=
            kmsInnerReal_le_kmsNorm_mul_kmsNorm ψ_eig E_eig β
              (opEigenbasis_orthonormal H hH) (hilbertTrace_eq_sum_opEigenbasis H hH) _ _
        _ = Real.sqrt (f s) * opKMSNorm H hH β (opCommutator H O_init) := by
            rw [kmsNorm_I_smul]; rfl
        _ ≤ Real.sqrt (f s) * Γ_coh :=
            mul_le_mul_of_nonneg_left h_coh (Real.sqrt_nonneg _)
        _ = Γ_coh * Real.sqrt (f s) := mul_comm _ _
    have h_diss_s :
        kmsInnerReal ψ_eig E_eig β (O_t s - O_init) (L_diss (O_t s)) ≤
          (1 / 4 : ℝ) * Γ_diss := by
      have h1 := kmsInnerReal_sub_dissipative_le H hH β hL_gen O_init (O_t s)
      linarith
    linarith
  exact kms_gronwall_ode_integral_bound hΓ_coh hΓ_diss ht hf0 hf_nonneg hf_deriv hf_ineq
    t ⟨ht, le_rfl⟩

/-- **Unperturbed ($\Gamma_{\mathrm{coh}} = 0$) Squared-Norm Specialization
    (Part I, Theorem 5.8(i) (`thm:unperturbed-kms-lifetime`); Part II, Theorem 6.2 Step 2)**:
    When $[H, O_{\mathrm{init}}] = 0$, $\|O_t - O_{\mathrm{init}}\|_{\mathrm{KMS},\beta}^2 \le \frac{1}{2}\,\Gamma_{\mathrm{diss}}\,t$. -/
theorem opKMSNormSq_sub_le_of_dissipativeODE_commute {D L_box : ℕ}
    {Site : BoxD D L_box → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    [∀ x, Nonempty (Site x)]
    (H : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site)
    (hH : IsSelfAdjoint H) (β : ℝ)
    (L_diss : (ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site) →L[ℂ]
      (ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site))
    (hL_gen : IsKMSSymmetricDissipativeGenerator H hH β L_diss)
    (O_init : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site)
    (hO_sa : IsSelfAdjoint O_init)
    (h_comm : Commute H O_init)
    {Γ_diss t : ℝ} (hΓ_diss : 0 ≤ Γ_diss) (ht : 0 ≤ t)
    (h_diss : 2 * kmsDissipativeForm H hH β L_diss O_init O_init ≤ Γ_diss)
    {O_t : ℝ → (ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site)}
    (h_ode : SatisfiesKMSDissipativeODE H hH β L_diss O_init O_t t) :
    opKMSNormSq H hH β (O_t t - O_init) ≤ (1 / 2 : ℝ) * Γ_diss * t := by
  have h_comm_zero : opCommutator H O_init = 0 := sub_eq_zero.mpr h_comm.eq
  have h_coh_zero : opKMSNorm H hH β (opCommutator H O_init) ≤ 0 := by
    rw [h_comm_zero]
    unfold opKMSNorm kmsNorm kmsNormSq kmsInnerReal
    rw [map_zero, mul_zero, hilbertTrace_zero, Real.sqrt_zero]
  have h_bound := opKMSNorm_sub_le_kmsDriftDirichletBound_of_dissipativeODE
    H hH β L_diss hL_gen O_init hO_sa le_rfl hΓ_diss ht h_coh_zero h_diss h_ode
  unfold kmsDriftDirichletBound at h_bound
  rw [mul_zero, zero_add] at h_bound
  have h_nonneg : 0 ≤ opKMSNormSq H hH β (O_t t - O_init) :=
    kmsNormSq_nonneg (opEigenbasis H hH) (opEigenvalues H hH) β
      (opEigenbasis_orthonormal H hH) (hilbertTrace_eq_sum_opEigenbasis H hH) (O_t t - O_init)
  have h_rhs_nonneg : 0 ≤ (t / 2) * Γ_diss := by positivity
  have h_sq := mul_self_le_mul_self (Real.sqrt_nonneg _) h_bound
  change Real.sqrt (opKMSNormSq H hH β (O_t t - O_init)) *
      Real.sqrt (opKMSNormSq H hH β (O_t t - O_init)) ≤
    Real.sqrt (t / 2 * Γ_diss) * Real.sqrt (t / 2 * Γ_diss) at h_sq
  rw [Real.mul_self_sqrt h_nonneg, Real.mul_self_sqrt h_rhs_nonneg] at h_sq
  linarith

end
