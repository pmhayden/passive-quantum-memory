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

import Proofs.GapBootstrap.CourantFischerAndBootstrap
import Proofs.DressedSafeSubspace.ScaledPerturbationWeylContinuity

/-!
# Continuous Coupling-Interval Spectral Gap Bootstrap

Proves the topological connectedness open-closed bootstrap (`continuous_gap_bootstrap_Icc_zero_one_of_strict`, `indexedSpectralGap_bootstrap_on_Icc_of_unitary_flow`) showing that a continuous spectral gap starting at $\ge 1$ and bounded below by $1/2$ whenever positive remains $\ge 1/2$ across $[0, 1]$.

## References

* Part I, Section 7.1 (`subsec:single-cube-telescoping`), Proposition 7.2 (`prop:single-cube-telescoping`)
* Part I, Section 7.2 (`subsec:gap-bootstrap`), Theorem 7.3 (`thm:gap-bootstrap`)
* Part I, Section 7.3 (`subsec:zero-temp-dressed-memory`), Theorem 7.4 (`thm:zero-temp-dressed-memory`)
* Bravyi and Hastings (2011), Commun. Math. Phys. 307, 609–627
-/

noncomputable section

open scoped Classical InnerProduct ComplexConjugate BigOperators
open Filter Topology Asymptotics ContinuousLinearMap MeasureTheory

/-! ## 1. Open-Closed Continuous-$s$ Spectral Gap Bootstrap on $[0, 1]$ -/

/-- **General Open-Closed Continuous Bootstrap on $[0, 1]$ (`continuous_gap_bootstrap_Icc_zero_one_of_strict`)**:
    For any continuous function $\Delta : \mathbb{R} \to \mathbb{R}$ on $[0, 1]$ and thresholds
    $\Delta_0 < \Delta_1$ with $\Delta(0) \ge \Delta_1$: if for every $s \in [0, 1]$,
    $(\forall u \in [0, s], \Delta(u) \ge \Delta_0) \implies \Delta(s) \ge \Delta_1$,
    then for **all** $s \in [0, 1]$, $\Delta(s) \ge \Delta_1 > \Delta_0$. -/
theorem continuous_gap_bootstrap_Icc_zero_one_of_strict
    {Δ : ℝ → ℝ} {Δ_0 Δ_1 : ℝ} (h_lt : Δ_0 < Δ_1)
    (h_cont : ContinuousOn Δ (Set.Icc 0 1)) (h_zero : Δ_1 ≤ Δ 0)
    (h_step : ∀ s ∈ Set.Icc 0 1,
      (∀ u ∈ Set.Icc 0 s, Δ_0 ≤ Δ u) → Δ_1 ≤ Δ s) :
    ∀ s ∈ Set.Icc 0 1, Δ_1 ≤ Δ s ∧ Δ_0 ≤ Δ s := by
  have h_ge_Δ0 : ∀ s ∈ Set.Icc 0 1, Δ_0 ≤ Δ s := by
    by_contra! h_fail
    rcases h_fail with ⟨s_bad, hs_bad_Icc, hs_bad_lt⟩
    have h_mid : (Δ_0 + Δ_1) / 2 ∈ Set.Icc (Δ s_bad) (Δ 0) := ⟨by linarith, by linarith⟩
    have h_sub_Icc : Set.Icc 0 s_bad ⊆ Set.Icc 0 1 :=
      fun x hx => ⟨hx.1, le_trans hx.2 hs_bad_Icc.2⟩
    have h_cont_sub : ContinuousOn Δ (Set.Icc 0 s_bad) := h_cont.mono h_sub_Icc
    rcases intermediate_value_Icc' hs_bad_Icc.1 h_cont_sub h_mid with ⟨s_1, hs_1_Icc, hs_1_eq⟩
    let B' : Set ℝ := {s ∈ Set.Icc 0 1 | Δ s ≤ (Δ_0 + Δ_1) / 2}
    have hB'_nonempty : B'.Nonempty := ⟨s_1, ⟨h_sub_Icc hs_1_Icc, le_of_eq hs_1_eq⟩⟩
    have hB'_bdd : BddBelow B' := ⟨0, fun s hs => hs.1.1⟩
    have hB'_closed : IsClosed B' :=
      h_cont.preimage_isClosed_of_isClosed isClosed_Icc isClosed_Iic
    let s_star : ℝ := sInf B'
    have hs_star_mem : s_star ∈ B' := hB'_closed.csInf_mem hB'_nonempty hB'_bdd
    have hs_star_Icc : s_star ∈ Set.Icc 0 1 := hs_star_mem.1
    have hs_star_le : Δ s_star ≤ (Δ_0 + Δ_1) / 2 := hs_star_mem.2
    have h_before : ∀ u ∈ Set.Icc 0 s_star, Δ_0 ≤ Δ u := by
      intro u hu
      rcases eq_or_lt_of_le hu.2 with hu_eq | hu_lt
      · by_contra h_u_lt; push_neg at h_u_lt
        have hu_Icc : u ∈ Set.Icc 0 1 := ⟨hu.1, le_trans hu.2 hs_star_Icc.2⟩
        have h_mid_u : (Δ_0 + Δ_1) / 2 ∈ Set.Icc (Δ u) (Δ 0) := ⟨by linarith, by linarith⟩
        have h_cont_u : ContinuousOn Δ (Set.Icc 0 u) :=
          h_cont.mono (fun x hx => ⟨hx.1, le_trans hx.2 hu_Icc.2⟩)
        rcases intermediate_value_Icc' hu.1 h_cont_u h_mid_u with ⟨w, hw_Icc, hw_eq⟩
        have hw_B' : w ∈ B' := ⟨⟨hw_Icc.1, le_trans hw_Icc.2 hu_Icc.2⟩, le_of_eq hw_eq⟩
        have hw_ge : s_star ≤ w := csInf_le hB'_bdd hw_B'
        have hw_lt : w < u := by
          rcases eq_or_lt_of_le hw_Icc.2 with rfl | h_strict
          · linarith
          · exact h_strict
        linarith
      · by_contra h_u_lt; push_neg at h_u_lt
        have hu_B' : u ∈ B' := ⟨⟨hu.1, le_trans hu.2 hs_star_Icc.2⟩, by linarith⟩
        have hu_ge : s_star ≤ u := csInf_le hB'_bdd hu_B'
        linarith
    have hs_star_ge : Δ_1 ≤ Δ s_star := h_step s_star hs_star_Icc h_before
    linarith
  intro s hs
  have h1 : Δ_1 ≤ Δ s := h_step s hs (fun u hu => h_ge_Δ0 u ⟨hu.1, le_trans hu.2 hs.2⟩)
  exact ⟨h1, le_trans (le_of_lt h_lt) h1⟩

/-- **Continuous-$s$ Spectral Gap Bootstrap from Unitary Form Bounds (`indexedSpectralGap_bootstrap_on_Icc_of_unitary_flow`)**:
    closes $\Delta(s) \ge 3/4 - \delta_{\mathrm{split}} > 1/2$ across all $s \in [0, 1]$ from conditional unitary form bounds. -/
theorem indexedSpectralGap_bootstrap_on_Icc_of_unitary_flow {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (sys : IndexedCommutingProjectorHamiltonian D L Site ι)
    (h_weight : ∀ i : ι, 1 ≤ sys.weight i) (V : QuasiLocalPerturbation D L Site)
    {δ_split : ℝ} (hδ_nn : 0 ≤ δ_split) (hδ_lt : δ_split < 1 / 4)
    (h_flow_form : ∀ s ∈ Set.Icc 0 1,
      (∀ u ∈ Set.Icc 0 s, bhmPerturbedGap ≤ indexedSpectralGap sys V u) →
      ∃ (U_s : unitary (ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site))
        (c_shift_s : ℝ),
        ∀ ψ : ManyBodyHilbertSpace Site,
          |RCLike.re (inner ℂ ψ
              ((U_s.1† * (sys.H0 + (scaleQuasiLocalPerturbation s V).totalPerturbation) * U_s.1 -
                sys.H0 - (c_shift_s : ℂ) • 1) ψ))| ≤
            bhmSandwichDeviation * RCLike.re (inner ℂ ψ (sys.H0 ψ)) + (δ_split / 2) * ‖ψ‖ ^ 2) :
    ∀ s ∈ Set.Icc 0 1,
      bhmBootstrapGap - δ_split ≤ indexedSpectralGap sys V s ∧
      bhmPerturbedGap ≤ indexedSpectralGap sys V s ∧
      (δ_split ≤ 1 / 8 → 5 / 8 ≤ indexedSpectralGap sys V s) := by
  have h_strict : bhmPerturbedGap < bhmBootstrapGap - δ_split := by
    dsimp [bhmPerturbedGap, bhmBootstrapGap]; linarith
  have h_zero : bhmBootstrapGap - δ_split ≤ indexedSpectralGap sys V 0 := by
    have h0 := indexedSpectralGap_zero_ge_one sys h_weight V
    dsimp [bhmBootstrapGap]; linarith
  have h_boot := continuous_gap_bootstrap_Icc_zero_one_of_strict
    h_strict (continuousOn_indexedSpectralGap sys V) h_zero
    (fun s hs h_ih => by
      rcases h_flow_form s hs h_ih with ⟨U_s, c_shift_s, h_form⟩
      exact (indexedSpectralGap_ge_of_unitary_form_bound
        sys h_weight V s U_s hδ_nn h_form).2.2.1)
  intro s hs
  rcases h_boot s hs with ⟨h_ge_boot, h_ge_half⟩
  refine ⟨h_ge_boot, h_ge_half, fun hδ_le => ?_⟩
  dsimp [bhmBootstrapGap] at h_ge_boot; linarith

end
