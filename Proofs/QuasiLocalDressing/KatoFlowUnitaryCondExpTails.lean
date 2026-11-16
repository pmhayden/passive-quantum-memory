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

import Proofs.BandLimitedFilter.BochnerFilterUnitaryCovariance
import Proofs.QuasiLocalDressing.DressedObservableExpansion

noncomputable section

open scoped Classical InnerProduct ComplexConjugate BigOperators
open Filter Topology Asymptotics ContinuousLinearMap MeasureTheory

/-!
# Kato Flow Unitaries and Duhamel Conditional-Expectation Tail Bounds

Constructs `katoFlowUnitary` intertwining the bare ground projector with the instantaneous ground projector (`katoFlowUnitary_adj_mul_P_flow_mul_eq_P0`, `commute_P0_katoFlowUnitary_of_commute_P_flow`) and bounds local conditional-expectation approximation errors via Duhamel commutator integrals (`norm_katoFlowUnitary_conj_sub_condExp_le_of_duhamel`).

## References

* Part I, Section 6.2 (`subsec:bochner-lr`), Proposition 6.3 (`prop:bochner-time-convolution`)
* Part I, Section 6.3 (`subsec:qac-block-diag`), Proposition 6.4 (`prop:qac-block-diagonalization`)
* Part I, Section 7.3 (`subsec:zero-temp-dressed-memory`), Theorem 7.4 (`thm:zero-temp-dressed-memory`)
* Bravyi and Hastings (2011), Commun. Math. Phys. 307, 609–627
-/

/-!
## 1. Canonical Unitary Element & Subspace Tracking from `IsKatoHastingsFlowSystem`
-/

/-- Bundles the evolution operator `U_flow s` of any `IsKatoHastingsFlowSystem P0 D_gen U_flow P_flow`
    into an element of the `unitary` submonoid. -/
def katoFlowUnitary {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    {P0 : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site}
    {D_gen U_flow P_flow : ℝ → (ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site)}
    (hFlow : IsKatoHastingsFlowSystem P0 D_gen U_flow P_flow) (s : ℝ) :
    unitary (ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site) :=
  ⟨U_flow s, Unitary.mem_iff.mpr
    ⟨((kato_hastings_ode_flow P0 D_gen U_flow P_flow hFlow).1 s).1,
     ((kato_hastings_ode_flow P0 D_gen U_flow P_flow hFlow).1 s).2⟩⟩

@[simp]
lemma katoFlowUnitary_coe {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    {P0 : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site}
    {D_gen U_flow P_flow : ℝ → (ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site)}
    (hFlow : IsKatoHastingsFlowSystem P0 D_gen U_flow P_flow) (s : ℝ) :
    (katoFlowUnitary hFlow s).1 = U_flow s := rfl

/-- Exact subspace tracking `(katoFlowUnitary hFlow s).1† * P_flow s * (katoFlowUnitary hFlow s).1 = P0`. -/
theorem katoFlowUnitary_adj_mul_P_flow_mul_eq_P0 {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    {P0 : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site}
    {D_gen U_flow P_flow : ℝ → (ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site)}
    (hFlow : IsKatoHastingsFlowSystem P0 D_gen U_flow P_flow) (s : ℝ) :
    (katoFlowUnitary hFlow s).1† * P_flow s * (katoFlowUnitary hFlow s).1 = P0 :=
  (kato_hastings_ode_flow P0 D_gen U_flow P_flow hFlow).2.1 s

/-- If `H_s` commutes with `P_flow s`, then the dressed Hamiltonian
    `(katoFlowUnitary hFlow s).1† * H_s * (katoFlowUnitary hFlow s).1` commutes with `P0`. -/
theorem commute_P0_katoFlowUnitary_of_commute_P_flow {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    {P0 H_s : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site}
    {D_gen U_flow P_flow : ℝ → (ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site)}
    (hFlow : IsKatoHastingsFlowSystem P0 D_gen U_flow P_flow) (s : ℝ)
    (h_comm : Commute H_s (P_flow s)) :
    Commute ((katoFlowUnitary hFlow s).1† * H_s * (katoFlowUnitary hFlow s).1) P0 :=
  (kato_hastings_ode_flow P0 D_gen U_flow P_flow hFlow).2.2 s H_s h_comm

/-!
## 2. Local Approximation & Duhamel `condExp` Tail Bounds for `U_dress`
-/

/-- If `B_approx` is supported on `A_target`, then `condExp Site A_target B_approx = B_approx`, so
    $$\|U^\dagger B U - \mathbb{E}_{A_{\mathrm{target}}}(U^\dagger B U)\|
      \le 2 \|U^\dagger B U - B_{\mathrm{approx}}\|.$$ -/
theorem norm_unitary_conj_sub_condExp_le_two_mul_norm_sub_local_of_isSupportedOn {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    [∀ x, Nonempty (Site x)]
    (U_dress : unitary (ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site))
    {A_target : Finset (BoxD D L)}
    (B : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site)
    {B_approx : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site}
    (hB_approx_supp : IsSupportedOn Site A_target B_approx) :
    ‖U_dress.1† * B * U_dress.1 - condExp Site A_target (U_dress.1† * B * U_dress.1)‖ ≤
      2 * ‖U_dress.1† * B * U_dress.1 - B_approx‖ := by
  let Δ := U_dress.1† * B * U_dress.1 - B_approx
  have hB_ce : condExp Site A_target B_approx = B_approx :=
    condExp_eq_self_of_isSupportedOn hB_approx_supp
  have h_eq : U_dress.1† * B * U_dress.1 - condExp Site A_target (U_dress.1† * B * U_dress.1) =
      Δ - condExp Site A_target Δ := by
    dsimp [Δ]
    rw [condExp_sub_clm, hB_ce]
    abel
  rw [h_eq]
  exact norm_sub_condExp_le_two_mul_norm A_target Δ

/-- In particular, if `B_loc` is already supported on `A_target` (e.g. `IsSupportedOn Site A_bare B_loc`
    with `A_bare ⊆ A_target`), then
    $$\|U^\dagger B_{\mathrm{loc}} U - \mathbb{E}_{A_{\mathrm{target}}}(U^\dagger B_{\mathrm{loc}} U)\|
      \le 2 \|U^\dagger B_{\mathrm{loc}} U - B_{\mathrm{loc}}\|.$$ -/
theorem norm_unitary_conj_sub_condExp_le_two_mul_norm_sub_self_of_isSupportedOn {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    [∀ x, Nonempty (Site x)]
    (U_dress : unitary (ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site))
    {A_target : Finset (BoxD D L)}
    {B_loc : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site}
    (hB_supp : IsSupportedOn Site A_target B_loc) :
    ‖U_dress.1† * B_loc * U_dress.1 - condExp Site A_target (U_dress.1† * B_loc * U_dress.1)‖ ≤
      2 * ‖U_dress.1† * B_loc * U_dress.1 - B_loc‖ :=
  norm_unitary_conj_sub_condExp_le_two_mul_norm_sub_local_of_isSupportedOn U_dress B_loc hB_supp

/-- **Duhamel `condExp` Tail Bound along `IsKatoHastingsFlowSystem`
    (`norm_katoFlowUnitary_conj_sub_condExp_le_of_duhamel`)**:
    Along a Kato–Hastings flow `IsKatoHastingsFlowSystem P0 D_gen U_flow P_flow` at $s \ge 0$, if
    $B_{\mathrm{loc}}$ is supported on $A_{\mathrm{target}}$ and
    $\|[B_{\mathrm{loc}}, D_{\mathrm{gen}}(\tau)]\| \le C_{\mathrm{comm}} \|B_{\mathrm{loc}}\|$ for all
    $\tau \in [0, s]$, then:
    $$\|(U_{\mathrm{flow}}(s))^\dagger B_{\mathrm{loc}} U_{\mathrm{flow}}(s) -
      \mathbb{E}_{A_{\mathrm{target}}}((U_{\mathrm{flow}}(s))^\dagger B_{\mathrm{loc}} U_{\mathrm{flow}}(s))\|
      \le (2 s C_{\mathrm{comm}}) \|B_{\mathrm{loc}}\|.$$ -/
theorem norm_katoFlowUnitary_conj_sub_condExp_le_of_duhamel {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    [∀ x, Nonempty (Site x)]
    {P0 : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site}
    {D_gen U_flow P_flow : ℝ → (ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site)}
    (hFlow : IsKatoHastingsFlowSystem P0 D_gen U_flow P_flow)
    {s C_comm : ℝ} (hs : 0 ≤ s)
    {A_target : Finset (BoxD D L)}
    {B_loc : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site}
    (hB_supp : IsSupportedOn Site A_target B_loc)
    (h_comm : ∀ τ ∈ Set.Icc 0 s, ‖B_loc * D_gen τ - D_gen τ * B_loc‖ ≤ C_comm * ‖B_loc‖) :
    let U_s := katoFlowUnitary hFlow s
    ‖U_s.1† * B_loc * U_s.1 - condExp Site A_target (U_s.1† * B_loc * U_s.1)‖ ≤
      (2 * s * C_comm) * ‖B_loc‖ := by
  intro U_s
  have h_duh : ‖U_s.1† * B_loc * U_s.1 - B_loc‖ ≤ s * (C_comm * ‖B_loc‖) :=
    (duhamel_conjugation_bound P0 D_gen U_flow P_flow hFlow B_loc).2
      s (C_comm * ‖B_loc‖) hs h_comm
  have h_ce := norm_unitary_conj_sub_condExp_le_two_mul_norm_sub_self_of_isSupportedOn U_s hB_supp
  calc ‖U_s.1† * B_loc * U_s.1 - condExp Site A_target (U_s.1† * B_loc * U_s.1)‖
    _ ≤ 2 * ‖U_s.1† * B_loc * U_s.1 - B_loc‖ := h_ce
    _ ≤ 2 * (s * (C_comm * ‖B_loc‖)) := mul_le_mul_of_nonneg_left h_duh (by norm_num)
    _ = (2 * s * C_comm) * ‖B_loc‖ := by ring

/-- Inclusion `{v} ⊆ boxCube v r` whenever `1 ≤ r`. -/
lemma singleton_subset_boxCube {D L : ℕ} (v : BoxD D L) {r : ℕ} (hr : 1 ≤ r) :
    ({v} : Finset (BoxD D L)) ⊆ boxCube v r := by
  intro x hx
  rw [Finset.mem_singleton.mp hx]
  simp only [boxCube, Finset.mem_filter, Finset.mem_univ, true_and]
  intro μ
  exact ⟨le_refl _, by omega⟩

/-- Monotonicity of `boxCube u r` in `r`. -/
lemma boxCube_mono_local {D L : ℕ} (u : BoxD D L) {r₁ r₂ : ℕ} (hr : r₁ ≤ r₂) :
    boxCube u r₁ ⊆ boxCube u r₂ := by
  intro x hx
  simp only [boxCube, Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
  intro μ
  have hμ := hx μ
  exact ⟨hμ.1, by omega⟩

end
