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
import Proofs.CubeTelescoping.SpectralAlignmentUnitary
import Proofs.BandLimitedFilter.AnchoredSitePerturbationOps
import Proofs.TwoBlockDecomposition.SitePerturbationNormsAndEnvelopes

/-!
# Scaled Perturbations and Weyl Spectral Gap Continuity

Defines the linearly scaled perturbation `scaleQuasiLocalPerturbation`, proves Weyl eigenvalue Lipschitz continuity (`sortedEigenvalues_le_add_norm_sub`, `abs_sortedEigenvalues_sub_le_norm`) and coupling continuity (`continuous_sortedEigenvalues_scaleQuasiLocalPerturbation`), and establishes continuity of `indexedEigenvalueGap` and `indexedSpectralGap` (`continuous_indexedEigenvalueGap`).

## References

* Part I, Section 6.3 (`subsec:qac-block-diag`), Proposition 6.4 (`prop:qac-block-diagonalization`)
* Part I, Section 7.2 (`subsec:gap-bootstrap`), Theorem 7.3 (`thm:gap-bootstrap`)
* Bravyi, Hastings, and Michalakis (2010), J. Math. Phys. 51, 093512
* Bravyi and Hastings (2011), Commun. Math. Phys. 307, 609–627
-/

noncomputable section

open scoped Classical InnerProduct ComplexConjugate BigOperators
open Filter Topology Asymptotics ContinuousLinearMap MeasureTheory

/-! ## 1. Scaled Perturbation Family `scaleQuasiLocalPerturbation` ($s V$) -/

private lemma isSelfAdjoint_real_smul_bhm {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] [CompleteSpace E]
    {A : E →L[ℂ] E} (s : ℝ) (hA : IsSelfAdjoint A) : IsSelfAdjoint ((s : ℂ) • A) := by
  rw [IsSelfAdjoint, star_smul, hA.star_eq, RCLike.star_def, Complex.conj_ofReal]

/-- **Scaled Quasi-Local Perturbation (`scaleQuasiLocalPerturbation`)**:
    scales every local interaction term $V_{r,A}$ by $s \in \mathbb{R}$, yielding
    $(s \bullet V)_{r,A} = (s : \mathbb{C}) \bullet V_{r,A}$ and $(s \bullet V).V_{\mathrm{tot}} = (s : \mathbb{C}) \bullet V.V_{\mathrm{tot}}$. -/
def scaleQuasiLocalPerturbation {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    (s : ℝ) (V : QuasiLocalPerturbation D L Site) : QuasiLocalPerturbation D L Site where
  term r A := (s : ℂ) • V.term r A
  is_selfAdjoint r A := isSelfAdjoint_real_smul_bhm s (V.is_selfAdjoint r A)
  is_supported r hr A hA := isSupportedOn_smul A (s : ℂ) (V.is_supported r hr A hA)

@[simp]
lemma scaleQuasiLocalPerturbation_term {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    (s : ℝ) (V : QuasiLocalPerturbation D L Site) (r : ℕ) (A : Finset (BoxD D L)) :
    (scaleQuasiLocalPerturbation s V).term r A = (s : ℂ) • V.term r A := rfl

@[simp]
lemma scaleQuasiLocalPerturbation_V_tot {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    (s : ℝ) (V : QuasiLocalPerturbation D L Site) :
    (scaleQuasiLocalPerturbation s V).totalPerturbation = (s : ℂ) • V.totalPerturbation := by
  unfold QuasiLocalPerturbation.totalPerturbation
  simp only [scaleQuasiLocalPerturbation_term, ← Finset.smul_sum]

@[simp]
lemma scaleQuasiLocalPerturbation_zero_V_tot {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    (V : QuasiLocalPerturbation D L Site) :
    (scaleQuasiLocalPerturbation 0 V).totalPerturbation = 0 := by
  rw [scaleQuasiLocalPerturbation_V_tot, Complex.ofReal_zero]; exact zero_smul ℂ V.totalPerturbation

@[simp]
lemma scaleQuasiLocalPerturbation_one {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    (V : QuasiLocalPerturbation D L Site) :
    scaleQuasiLocalPerturbation 1 V = V := by
  cases V; simp only [scaleQuasiLocalPerturbation, Complex.ofReal_one, one_smul]

@[simp]
lemma scaleQuasiLocalPerturbation_one_V_tot {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    (V : QuasiLocalPerturbation D L Site) :
    (scaleQuasiLocalPerturbation 1 V).totalPerturbation = V.totalPerturbation := by
  rw [scaleQuasiLocalPerturbation_one]

/-- Site-anchored perturbation operator scales linearly under `scaleQuasiLocalPerturbation`. -/
@[simp]
lemma sitePerturbationOp_scaleQuasiLocalPerturbation {D L : ℕ} [NeZero L]
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    (s : ℝ) (V : QuasiLocalPerturbation D L Site) (u : BoxD D L) :
    sitePerturbationOp (scaleQuasiLocalPerturbation s V) u = (s : ℂ) • sitePerturbationOp V u := by
  unfold sitePerturbationOp; simp only [scaleQuasiLocalPerturbation_term, ← Finset.smul_sum]

/-- Commutator with `(scaleQuasiLocalPerturbation s V).V_tot` scales linearly by `(s : ℂ)`. -/
lemma opCommutator_scaleQuasiLocalPerturbation_V_tot {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    (s : ℝ) (V : QuasiLocalPerturbation D L Site)
    (B : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site) :
    opCommutator (scaleQuasiLocalPerturbation s V).totalPerturbation B =
      (s : ℂ) • opCommutator V.totalPerturbation B := by
  unfold opCommutator
  rw [scaleQuasiLocalPerturbation_V_tot, smul_mul_assoc, mul_smul_comm, ← smul_sub]

/-- If `V.SatisfiesDecayBound J f` and `0 ≤ s`, then `(scaleQuasiLocalPerturbation s V)`
    satisfies `SatisfiesDecayBound (s * J) f`. -/
lemma satisfiesDecayBound_scaleQuasiLocalPerturbation {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    {s J : ℝ} {f : ℕ → ℝ} (V : QuasiLocalPerturbation D L Site)
    (hs : 0 ≤ s) (hV : V.SatisfiesDecayBound J f) :
    (scaleQuasiLocalPerturbation s V).SatisfiesDecayBound (s * J) f := by
  intro r hr A hA
  rw [scaleQuasiLocalPerturbation_term, norm_smul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg hs, mul_assoc]
  exact mul_le_mul_of_nonneg_left (hV r hr A hA) hs

/-- For `s ∈ Set.Icc 0 1`, `(scaleQuasiLocalPerturbation s V)` inherits `SatisfiesDecayBound J f`. -/
lemma satisfiesDecayBound_scaleQuasiLocalPerturbation_of_mem_Icc {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    {s J : ℝ} {f : ℕ → ℝ} (V : QuasiLocalPerturbation D L Site)
    (hs : s ∈ Set.Icc 0 1) (hJ : 0 ≤ J) (hf : ∀ r : ℕ, 0 ≤ f r)
    (hV : V.SatisfiesDecayBound J f) :
    (scaleQuasiLocalPerturbation s V).SatisfiesDecayBound J f := by
  intro r hr A hA
  have h1 := satisfiesDecayBound_scaleQuasiLocalPerturbation V hs.1 hV r hr A hA
  have h2 : (s * J) * f r ≤ (1 * J) * f r :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hs.2 hJ) (hf r)
  rw [one_mul] at h2; exact le_trans h1 h2

/-- Finite interaction range (`∀ r > R, V.term r A = 0`) is invariant under `scaleQuasiLocalPerturbation`. -/
lemma finiteRange_scaleQuasiLocalPerturbation {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    (s : ℝ) (V : QuasiLocalPerturbation D L Site) {R : ℕ}
    (hV_range : ∀ r : ℕ, R < r → ∀ A : Finset (BoxD D L), V.term r A = 0) :
    ∀ r : ℕ, R < r → ∀ A : Finset (BoxD D L), (scaleQuasiLocalPerturbation s V).term r A = 0 := by
  intro r hr A; rw [scaleQuasiLocalPerturbation_term, hV_range r hr A]; ext ψ; simp

/-! ## 2. Weyl's Inequality for `sortedEigenvalues` & Continuity of `indexedSpectralGap` -/

/-- One-sided Weyl eigenvalue perturbation bound: $\lambda_i(H_1) \le \lambda_i(H_2) + \|H_1 - H_2\|$. -/
theorem sortedEigenvalues_le_add_norm_sub {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    (H1 H2 : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site)
    (hH1 : IsSelfAdjoint H1) (hH2 : IsSelfAdjoint H2)
    (i : Fin (Module.finrank ℂ (ManyBodyHilbertSpace Site))) :
    sortedEigenvalues H1 hH1 i ≤ sortedEigenvalues H2 hH2 i + ‖H1 - H2‖ := by
  let W := eigenSpanBelow H2 hH2 (i.1 + 1)
  let U_orth := (eigenSpanBelow H1 hH1 i.1)ᗮ
  have hW_dim : Module.finrank ℂ W = i.1 + 1 := finrank_eigenSpanBelow H2 hH2 (i.1 + 1) i.2
  have h_dim_E1 : Module.finrank ℂ (eigenSpanBelow H1 hH1 i.1) = i.1 :=
    finrank_eigenSpanBelow H1 hH1 i.1 (le_of_lt i.2)
  have h_orth := (eigenSpanBelow H1 hH1 i.1).finrank_add_finrank_orthogonal
  have h_dim_lt : Module.finrank ℂ (ManyBodyHilbertSpace Site) <
      Module.finrank ℂ W + Module.finrank ℂ U_orth := by dsimp [U_orth]; omega
  rcases exists_ne_zero_mem_inf_of_finrank_lt_add W U_orth h_dim_lt with ⟨ψ, hψW, hψU, hψ_ne⟩
  have h_H2_le : RCLike.re (inner ℂ ψ (H2 ψ)) ≤ sortedEigenvalues H2 hH2 i * ‖ψ‖ ^ 2 := by
    apply re_inner_apply_H_le_of_mem_eigenSpanBelow H2 hH2 (i.1 + 1) (sortedEigenvalues H2 hH2 i) _ hψW
    intro j hj; exact sortedEigenvalues_monotone_bhm H2 hH2 (Nat.lt_succ_iff.mp hj)
  have h_H1_ge : sortedEigenvalues H1 hH1 i * ‖ψ‖ ^ 2 ≤ RCLike.re (inner ℂ ψ (H1 ψ)) := by
    apply le_re_inner_apply_H_of_mem_orthogonal_eigenSpanBelow H1 hH1 i.1 (sortedEigenvalues H1 hH1 i) _ hψU
    intro j hj; exact sortedEigenvalues_monotone_bhm H1 hH1 hj
  have h_diff_eq : RCLike.re (inner ℂ ψ (H1 ψ)) - RCLike.re (inner ℂ ψ (H2 ψ)) =
      RCLike.re (inner ℂ ψ ((H1 - H2) ψ)) := by
    rw [ContinuousLinearMap.sub_apply, inner_sub_right, map_sub]
  have h_diff_le : RCLike.re (inner ℂ ψ (H1 ψ)) - RCLike.re (inner ℂ ψ (H2 ψ)) ≤
      ‖H1 - H2‖ * ‖ψ‖ ^ 2 := by
    rw [h_diff_eq]
    exact le_trans (le_abs_self _) (abs_re_inner_le_opNorm_mul_norm_sq (H1 - H2) ψ)
  have h_le : sortedEigenvalues H1 hH1 i * ‖ψ‖ ^ 2 ≤
      (sortedEigenvalues H2 hH2 i + ‖H1 - H2‖) * ‖ψ‖ ^ 2 := by linarith
  exact le_of_mul_le_mul_right h_le (sq_pos_of_pos (norm_pos_iff.mpr hψ_ne))

/-- **Weyl's Inequality (`abs_sortedEigenvalues_sub_le_norm`)**:
    $|\lambda_i(H_1) - \lambda_i(H_2)| \le \|H_1 - H_2\|$ for all ordered eigenvalues. -/
theorem abs_sortedEigenvalues_sub_le_norm {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    (H1 H2 : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site)
    (hH1 : IsSelfAdjoint H1) (hH2 : IsSelfAdjoint H2)
    (i : Fin (Module.finrank ℂ (ManyBodyHilbertSpace Site))) :
    |sortedEigenvalues H1 hH1 i - sortedEigenvalues H2 hH2 i| ≤ ‖H1 - H2‖ := by
  have h1 := sortedEigenvalues_le_add_norm_sub H1 H2 hH1 hH2 i
  have h2 := sortedEigenvalues_le_add_norm_sub H2 H1 hH2 hH1 i
  rw [norm_sub_rev H2 H1] at h2; rw [abs_sub_le_iff]; constructor <;> linarith

/-- Lipschitz bound for $\lambda_i(H_0 + s V_{\mathrm{tot}})$:
    $|\lambda_i(s_1) - \lambda_i(s_2)| \le |s_1 - s_2| \cdot \|V.V_{\mathrm{tot}}\|$. -/
theorem abs_sortedEigenvalues_scaleQuasiLocalPerturbation_sub_le {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (sys : IndexedCommutingProjectorHamiltonian D L Site ι) (V : QuasiLocalPerturbation D L Site)
    (i : Fin (Module.finrank ℂ (ManyBodyHilbertSpace Site))) (s1 s2 : ℝ) :
    let hH1 := isSelfAdjoint_indexedH0_add_V_tot_bhm sys (scaleQuasiLocalPerturbation s1 V)
    let hH2 := isSelfAdjoint_indexedH0_add_V_tot_bhm sys (scaleQuasiLocalPerturbation s2 V)
    |sortedEigenvalues (sys.H0 + (scaleQuasiLocalPerturbation s1 V).totalPerturbation) hH1 i -
      sortedEigenvalues (sys.H0 + (scaleQuasiLocalPerturbation s2 V).totalPerturbation) hH2 i| ≤
      |s1 - s2| * ‖V.totalPerturbation‖ := by
  intro hH1 hH2
  have h_weyl := abs_sortedEigenvalues_sub_le_norm
    (sys.H0 + (scaleQuasiLocalPerturbation s1 V).totalPerturbation)
    (sys.H0 + (scaleQuasiLocalPerturbation s2 V).totalPerturbation) hH1 hH2 i
  have h_diff : (sys.H0 + (scaleQuasiLocalPerturbation s1 V).totalPerturbation) -
      (sys.H0 + (scaleQuasiLocalPerturbation s2 V).totalPerturbation) = ((s1 - s2 : ℝ) : ℂ) • V.totalPerturbation := by
    ext ψ; simp [scaleQuasiLocalPerturbation_V_tot, sub_smul]
  rw [h_diff, norm_smul, Complex.norm_real, Real.norm_eq_abs] at h_weyl; exact h_weyl

/-- Continuity of $s \mapsto \lambda_i(H_0 + s V_{\mathrm{tot}})$ on $\mathbb{R}$. -/
theorem continuous_sortedEigenvalues_scaleQuasiLocalPerturbation {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (sys : IndexedCommutingProjectorHamiltonian D L Site ι) (V : QuasiLocalPerturbation D L Site)
    (i : Fin (Module.finrank ℂ (ManyBodyHilbertSpace Site))) :
    Continuous (fun s : ℝ =>
      sortedEigenvalues (sys.H0 + (scaleQuasiLocalPerturbation s V).totalPerturbation)
        (isSelfAdjoint_indexedH0_add_V_tot_bhm sys (scaleQuasiLocalPerturbation s V)) i) := by
  rw [Metric.continuous_iff]
  intro s ε hε
  refine ⟨ε / (‖V.totalPerturbation‖ + 1), div_pos hε (by positivity), fun s' hs' => ?_⟩
  rw [Real.dist_eq] at hs' ⊢
  have h_lip := abs_sortedEigenvalues_scaleQuasiLocalPerturbation_sub_le sys V i s' s
  have h1 : |s' - s| * ‖V.totalPerturbation‖ ≤ |s' - s| * (‖V.totalPerturbation‖ + 1) :=
    mul_le_mul_of_nonneg_left (by linarith) (abs_nonneg _)
  have h2 : |s' - s| * (‖V.totalPerturbation‖ + 1) < ε :=
    (lt_div_iff₀ (by positivity : (0 : ℝ) < ‖V.totalPerturbation‖ + 1)).mp hs'
  exact lt_of_le_of_lt h_lip (lt_of_le_of_lt h1 h2)

/-- **Pairwise Eigenvalue Gap (`indexedEigenvalueGap`)**:
    $\Delta_{i, j}(s) := \lambda_j(H_0 + s V_{\mathrm{tot}}) - \lambda_i(H_0 + s V_{\mathrm{tot}})$. -/
def indexedEigenvalueGap {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (sys : IndexedCommutingProjectorHamiltonian D L Site ι) (V : QuasiLocalPerturbation D L Site)
    (i j : Fin (Module.finrank ℂ (ManyBodyHilbertSpace Site))) (s : ℝ) : ℝ :=
  let hHs := isSelfAdjoint_indexedH0_add_V_tot_bhm sys (scaleQuasiLocalPerturbation s V)
  sortedEigenvalues (sys.H0 + (scaleQuasiLocalPerturbation s V).totalPerturbation) hHs j -
    sortedEigenvalues (sys.H0 + (scaleQuasiLocalPerturbation s V).totalPerturbation) hHs i

/-- **Spectral Gap Function (`indexedSpectralGap`)**:
    $\Delta(s) := \lambda_{d_{\mathrm{gs}}}(H_0 + s V_{\mathrm{tot}}) -
      \lambda_{d_{\mathrm{gs}} - 1}(H_0 + s V_{\mathrm{tot}})$
    when $0 < d_{\mathrm{gs}} < \dim \mathcal{H}$ (and $1$ in the trivial degenerate cases). -/
def indexedSpectralGap {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (sys : IndexedCommutingProjectorHamiltonian D L Site ι)
    (V : QuasiLocalPerturbation D L Site) (s : ℝ) : ℝ :=
  if h : 0 < sys.groundDegeneracy ∧
      sys.groundDegeneracy < Module.finrank ℂ (ManyBodyHilbertSpace Site) then
    indexedEigenvalueGap sys V ⟨sys.groundDegeneracy - 1, by omega⟩ ⟨sys.groundDegeneracy, h.2⟩ s
  else 1

lemma indexedSpectralGap_eq_of_lt {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (sys : IndexedCommutingProjectorHamiltonian D L Site ι) (V : QuasiLocalPerturbation D L Site)
    (h_pos : 0 < sys.groundDegeneracy)
    (h_lt : sys.groundDegeneracy < Module.finrank ℂ (ManyBodyHilbertSpace Site)) (s : ℝ) :
    indexedSpectralGap sys V s =
      indexedEigenvalueGap sys V ⟨sys.groundDegeneracy - 1, by omega⟩ ⟨sys.groundDegeneracy, h_lt⟩ s := by
  unfold indexedSpectralGap; rw [dif_pos ⟨h_pos, h_lt⟩]

/-- Monotonicity of `sortedEigenvalues` implies `indexedSpectralGap sys V s ≤ indexedEigenvalueGap sys V i j s`
    for every ground-band index `i.1 < sys.groundDegeneracy` and excited-band index `sys.groundDegeneracy ≤ j.1`. -/
lemma indexedSpectralGap_le_indexedEigenvalueGap {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (sys : IndexedCommutingProjectorHamiltonian D L Site ι) (V : QuasiLocalPerturbation D L Site)
    {i j : Fin (Module.finrank ℂ (ManyBodyHilbertSpace Site))}
    (hi : i.1 < sys.groundDegeneracy) (hj : sys.groundDegeneracy ≤ j.1) (s : ℝ) :
    indexedSpectralGap sys V s ≤ indexedEigenvalueGap sys V i j s := by
  have h_pos : 0 < sys.groundDegeneracy := by omega
  have h_lt : sys.groundDegeneracy < Module.finrank ℂ (ManyBodyHilbertSpace Site) :=
    lt_of_le_of_lt hj j.2
  rw [indexedSpectralGap_eq_of_lt sys V h_pos h_lt s]; dsimp [indexedEigenvalueGap]
  let hHs := isSelfAdjoint_indexedH0_add_V_tot_bhm sys (scaleQuasiLocalPerturbation s V)
  have hi_le : sortedEigenvalues (sys.H0 + (scaleQuasiLocalPerturbation s V).totalPerturbation) hHs i ≤
      sortedEigenvalues (sys.H0 + (scaleQuasiLocalPerturbation s V).totalPerturbation) hHs
        ⟨sys.groundDegeneracy - 1, by omega⟩ :=
    sortedEigenvalues_monotone_bhm _ hHs (Fin.le_iff_val_le_val.mpr (by dsimp; omega))
  have hj_ge : sortedEigenvalues (sys.H0 + (scaleQuasiLocalPerturbation s V).totalPerturbation) hHs
        ⟨sys.groundDegeneracy, h_lt⟩ ≤
      sortedEigenvalues (sys.H0 + (scaleQuasiLocalPerturbation s V).totalPerturbation) hHs j :=
    sortedEigenvalues_monotone_bhm _ hHs (Fin.le_iff_val_le_val.mpr hj)
  linarith

/-- Continuity of `indexedEigenvalueGap sys V i j` on $\mathbb{R}$. -/
theorem continuous_indexedEigenvalueGap {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (sys : IndexedCommutingProjectorHamiltonian D L Site ι) (V : QuasiLocalPerturbation D L Site)
    (i j : Fin (Module.finrank ℂ (ManyBodyHilbertSpace Site))) :
    Continuous (indexedEigenvalueGap sys V i j) :=
  (continuous_sortedEigenvalues_scaleQuasiLocalPerturbation sys V j).sub
    (continuous_sortedEigenvalues_scaleQuasiLocalPerturbation sys V i)

/-- Continuity of `indexedSpectralGap sys V` on $\mathbb{R}$. -/
theorem continuous_indexedSpectralGap {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (sys : IndexedCommutingProjectorHamiltonian D L Site ι) (V : QuasiLocalPerturbation D L Site) :
    Continuous (indexedSpectralGap sys V) := by
  by_cases h : 0 < sys.groundDegeneracy ∧
      sys.groundDegeneracy < Module.finrank ℂ (ManyBodyHilbertSpace Site)
  · have h_eq : indexedSpectralGap sys V =
        indexedEigenvalueGap sys V ⟨sys.groundDegeneracy - 1, by omega⟩ ⟨sys.groundDegeneracy, h.2⟩ := by
      ext s; exact indexedSpectralGap_eq_of_lt sys V h.1 h.2 s
    rw [h_eq]; exact continuous_indexedEigenvalueGap sys V _ _
  · have h_eq : indexedSpectralGap sys V = fun _ => 1 := by
      ext s; unfold indexedSpectralGap; exact dif_neg h
    rw [h_eq]; exact continuous_const

/-- Continuity of `indexedSpectralGap sys V` on `Set.Icc 0 1`. -/
theorem continuousOn_indexedSpectralGap {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (sys : IndexedCommutingProjectorHamiltonian D L Site ι) (V : QuasiLocalPerturbation D L Site) :
    ContinuousOn (indexedSpectralGap sys V) (Set.Icc 0 1) :=
  (continuous_indexedSpectralGap sys V).continuousOn

/-- At $s = 0$, the unperturbed Hamiltonian $H(0) = H_0$ has spectral gap $\Delta(0) \ge 1$. -/
theorem indexedSpectralGap_zero_ge_one {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (sys : IndexedCommutingProjectorHamiltonian D L Site ι)
    (h_weight : ∀ i : ι, 1 ≤ sys.weight i) (V : QuasiLocalPerturbation D L Site) :
    1 ≤ indexedSpectralGap sys V 0 := by
  unfold indexedSpectralGap; split_ifs with h
  · dsimp [indexedEigenvalueGap]
    let i0 : Fin (Module.finrank ℂ (ManyBodyHilbertSpace Site)) := ⟨sys.groundDegeneracy - 1, by omega⟩
    let j0 : Fin (Module.finrank ℂ (ManyBodyHilbertSpace Site)) := ⟨sys.groundDegeneracy, h.2⟩
    let hH0_s := isSelfAdjoint_indexedH0_add_V_tot_bhm sys (scaleQuasiLocalPerturbation 0 V)
    have h_diff_zero : ‖(sys.H0 + (scaleQuasiLocalPerturbation 0 V).totalPerturbation) - sys.H0‖ = 0 := by
      rw [scaleQuasiLocalPerturbation_zero_V_tot, add_zero, sub_self, norm_zero]
    have h_eq_i : sortedEigenvalues (sys.H0 + (scaleQuasiLocalPerturbation 0 V).totalPerturbation) hH0_s i0 =
        sortedEigenvalues sys.H0 sys.isSelfAdjoint_H0 i0 := by
      have hw := abs_sortedEigenvalues_sub_le_norm
        (sys.H0 + (scaleQuasiLocalPerturbation 0 V).totalPerturbation) sys.H0 hH0_s sys.isSelfAdjoint_H0 i0
      rw [h_diff_zero, abs_le] at hw; linarith
    have h_eq_j : sortedEigenvalues (sys.H0 + (scaleQuasiLocalPerturbation 0 V).totalPerturbation) hH0_s j0 =
        sortedEigenvalues sys.H0 sys.isSelfAdjoint_H0 j0 := by
      have hw := abs_sortedEigenvalues_sub_le_norm
        (sys.H0 + (scaleQuasiLocalPerturbation 0 V).totalPerturbation) sys.H0 hH0_s sys.isSelfAdjoint_H0 j0
      rw [h_diff_zero, abs_le] at hw; linarith
    rcases sys.sortedEigenbasis_H0_properties h_weight with ⟨_h_nn, h_gnd, h_exc⟩
    have hi0 : sortedEigenvalues sys.H0 sys.isSelfAdjoint_H0 i0 = 0 := (h_gnd i0 (by dsimp [i0]; omega)).1
    have hj0 : 1 ≤ sortedEigenvalues sys.H0 sys.isSelfAdjoint_H0 j0 := (h_exc j0 (by dsimp [j0]; exact le_rfl)).1
    linarith
  · exact le_rfl

/-! ## 3. Single-$s$ Bootstrap Step: Relative Form Bound $\implies \Delta(s) \ge \frac{3}{4} - \delta_{\mathrm{split}}$ -/

/-- **Single-$s$ Relative Form Bound to Spectral Gap Step (`indexedSpectralGap_ge_of_unitary_form_bound`)**:
    if at parameter $s \in \mathbb{R}$ there exists a unitary $U_s$ satisfying the relative form bound
    with slope $1/4$ and error $\delta_{\mathrm{split}} / 2$, then $\Delta(s) \ge \frac{3}{4} - \delta_{\mathrm{split}}$
    (and $\Delta(s) \ge 5/8 > 1/2$ when $\delta_{\mathrm{split}} \le 1/8$). -/
theorem indexedSpectralGap_ge_of_unitary_form_bound {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (sys : IndexedCommutingProjectorHamiltonian D L Site ι)
    (h_weight : ∀ i : ι, 1 ≤ sys.weight i)
    (V : QuasiLocalPerturbation D L Site) (s : ℝ)
    (U_s : unitary (ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site))
    {c_shift_s δ_split : ℝ} (hδ_nn : 0 ≤ δ_split)
    (h_form : ∀ ψ : ManyBodyHilbertSpace Site,
      |RCLike.re (inner ℂ ψ
          ((U_s.1† * (sys.H0 + (scaleQuasiLocalPerturbation s V).totalPerturbation) * U_s.1 -
            sys.H0 - (c_shift_s : ℂ) • 1) ψ))| ≤
        bhmSandwichDeviation * RCLike.re (inner ℂ ψ (sys.H0 ψ)) + (δ_split / 2) * ‖ψ‖ ^ 2) :
    let hHs := isSelfAdjoint_indexedH0_add_V_tot_bhm sys (scaleQuasiLocalPerturbation s V)
    (∀ i : Fin (Module.finrank ℂ (ManyBodyHilbertSpace Site)),
      i.1 < sys.groundDegeneracy →
      |sortedEigenvalues (sys.H0 + (scaleQuasiLocalPerturbation s V).totalPerturbation) hHs i - c_shift_s| ≤
        δ_split / 2) ∧
    (∀ j : Fin (Module.finrank ℂ (ManyBodyHilbertSpace Site)),
      sys.groundDegeneracy ≤ j.1 →
      c_shift_s + bhmBootstrapGap - δ_split / 2 ≤
        sortedEigenvalues (sys.H0 + (scaleQuasiLocalPerturbation s V).totalPerturbation) hHs j) ∧
    bhmBootstrapGap - δ_split ≤ indexedSpectralGap sys V s ∧
    (δ_split ≤ 1 / 8 →
      5 / 8 ≤ indexedSpectralGap sys V s ∧ bhmPerturbedGap < indexedSpectralGap sys V s) := by
  intro hHs
  let V_s := scaleQuasiLocalPerturbation s V
  let U_iso := unitaryToLinearIsometryEquiv U_s
  have h_iso_form : ∀ ϕ : ManyBodyHilbertSpace Site,
      |RCLike.re (inner ℂ (U_iso ϕ) ((sys.H0 + V_s.totalPerturbation) (U_iso ϕ))) -
        RCLike.re (inner ℂ ϕ (sys.H0 ϕ)) - c_shift_s * ‖ϕ‖ ^ 2| ≤
        bhmSandwichDeviation * RCLike.re (inner ℂ ϕ (sys.H0 ϕ)) + (δ_split / 2) * ‖ϕ‖ ^ 2 := by
    intro ϕ
    have h_conj : inner ℂ (U_iso ϕ) ((sys.H0 + V_s.totalPerturbation) (U_iso ϕ)) =
        inner ℂ ϕ ((U_s.1† * (sys.H0 + V_s.totalPerturbation) * U_s.1) ϕ) :=
      inner_unitary_conj U_s (sys.H0 + V_s.totalPerturbation) ϕ
    have h_diff : RCLike.re (inner ℂ (U_iso ϕ) ((sys.H0 + V_s.totalPerturbation) (U_iso ϕ))) -
        RCLike.re (inner ℂ ϕ (sys.H0 ϕ)) - c_shift_s * ‖ϕ‖ ^ 2 =
        RCLike.re (inner ℂ ϕ
          ((U_s.1† * (sys.H0 + V_s.totalPerturbation) * U_s.1 - sys.H0 - (c_shift_s : ℂ) • 1) ϕ)) := by
      rw [h_conj, ContinuousLinearMap.sub_apply, ContinuousLinearMap.sub_apply,
        inner_sub_right, inner_sub_right, map_sub, map_sub, re_inner_smul_one]
    rw [h_diff]; exact h_form ϕ
  have h_eig := sortedEigenvalues_sub_le_of_isometry_form_bound sys V_s U_iso
    (γ := bhmSandwichDeviation) (ε := δ_split / 2) (E0 := c_shift_s)
    (by dsimp [bhmSandwichDeviation]; norm_num)
    (by dsimp [bhmSandwichDeviation]; norm_num) h_iso_form
  rcases sys.sortedEigenbasis_H0_properties h_weight with ⟨_h_nn, h_gnd, h_exc⟩
  have h_low : ∀ i : Fin (Module.finrank ℂ (ManyBodyHilbertSpace Site)),
      i.1 < sys.groundDegeneracy →
      |sortedEigenvalues (sys.H0 + (scaleQuasiLocalPerturbation s V).totalPerturbation) hHs i - c_shift_s| ≤
        δ_split / 2 := by
    intro i hi
    have hb := h_eig i
    have hμ0 : sortedEigenvalues sys.H0 sys.isSelfAdjoint_H0 i = 0 := (h_gnd i hi).1
    dsimp [V_s] at hb; rw [hμ0] at hb; ring_nf at hb ⊢; exact hb
  have h_high : ∀ j : Fin (Module.finrank ℂ (ManyBodyHilbertSpace Site)),
      sys.groundDegeneracy ≤ j.1 →
      c_shift_s + bhmBootstrapGap - δ_split / 2 ≤
        sortedEigenvalues (sys.H0 + (scaleQuasiLocalPerturbation s V).totalPerturbation) hHs j := by
    intro j hj
    have hb := (abs_le.mp (h_eig j)).1
    have hμ1 : 1 ≤ sortedEigenvalues sys.H0 sys.isSelfAdjoint_H0 j := (h_exc j hj).1
    dsimp [V_s, bhmSandwichDeviation, bhmBootstrapGap] at hb ⊢; linarith
  have h_gap : bhmBootstrapGap - δ_split ≤ indexedSpectralGap sys V s := by
    unfold indexedSpectralGap; split_ifs with h
    · unfold indexedEigenvalueGap
      have hi := (abs_le.mp (h_low ⟨sys.groundDegeneracy - 1, by omega⟩ (by simp; omega))).2
      have hi' : sortedEigenvalues (sys.H0 + (scaleQuasiLocalPerturbation s V).totalPerturbation) hHs
          ⟨sys.groundDegeneracy - 1, by omega⟩ ≤ c_shift_s + δ_split / 2 := by linarith
      have hj := h_high ⟨sys.groundDegeneracy, h.2⟩ (by simp)
      exact le_trans (by linarith) (sub_le_sub hj hi')
    · dsimp [bhmBootstrapGap]; linarith
  refine ⟨h_low, h_high, h_gap, fun hδ_le => ?_⟩
  dsimp [bhmBootstrapGap, bhmPerturbedGap] at h_gap ⊢; constructor <;> linarith

end
