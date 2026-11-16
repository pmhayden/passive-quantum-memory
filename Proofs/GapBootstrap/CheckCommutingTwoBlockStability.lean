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

import Proofs.KatoHastingsFlow.ConstructiveQuasiLocalQAC
import Proofs.DressedSafeSubspace.SectorFilteredAndDressedBHM

open scoped Classical InnerProduct ComplexConjugate BigOperators
open Filter Topology Asymptotics ContinuousLinearMap

noncomputable section

set_option maxRecDepth 200000
set_option maxHeartbeats 800000

/-!
# Check-Commuting Perturbations and Direct Sector-Filtered QAC Stability

Proves congruence of low-energy band and QAC stability predicates under equality of `V.totalPerturbation` (`hasSectorFilteredQACStability_congr_V_tot`), transfers check-projector commutation to `P0`, `localGroundProj`, and `syndromeProjector` (`commute_P0_of_commute_checkProj`, `commute_P_loc_of_commute_checkProj`, `commute_syndromeProjector_of_commute_checkProj`), and establishes `hasSectorFilteredQACStability_direct_of_commute_checkProj_and_form_bound`.

## References

* Part I, Section 7.1 (`subsec:single-cube-telescoping`), Lemma 7.1 (`lem:norm-transfer`)
* Part I, Section 7.2 (`subsec:gap-bootstrap`), Theorem 7.3 (`thm:gap-bootstrap`)
* Part II, Section 5.2 (`subsec:low-temp-crossover`), Proposition 5.2 (`prop:bhm-relative-form-bound`)
* Bravyi, Hastings, and Michalakis (2010), J. Math. Phys. 51, 093512
-/

/-!
## 1. Total-Perturbation Congruence for `HasSectorFilteredQACStability`
-/

/-- `IndexedHasStableLowEnergyBand sys V Δ_gap δ_split` depends on `V` only through `V.totalPerturbation`. -/
lemma indexedHasStableLowEnergyBand_congr_V_tot {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (sys : IndexedCommutingProjectorHamiltonian D L Site ι)
    {V₁ V₂ : QuasiLocalPerturbation D L Site}
    (hV_eq : V₁.totalPerturbation = V₂.totalPerturbation) (Δ_gap δ_split : ℝ) :
    IndexedHasStableLowEnergyBand sys V₁ Δ_gap δ_split ↔
      IndexedHasStableLowEnergyBand sys V₂ Δ_gap δ_split := by
  unfold IndexedHasStableLowEnergyBand
  simp only [hV_eq]

/-- `SatisfiesDressedEnergySandwich sys V U c_shift δ_split` depends on `V` only through `V.totalPerturbation`. -/
lemma satisfiesDressedEnergySandwich_congr_V_tot {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (sys : IndexedCommutingProjectorHamiltonian D L Site ι)
    {V₁ V₂ : QuasiLocalPerturbation D L Site}
    (hV_eq : V₁.totalPerturbation = V₂.totalPerturbation)
    (U : unitary (ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site))
    (c_shift δ_split : ℝ) :
    SatisfiesDressedEnergySandwich sys V₁ U c_shift δ_split ↔
      SatisfiesDressedEnergySandwich sys V₂ U c_shift δ_split := by
  unfold SatisfiesDressedEnergySandwich
  simp only [hV_eq]

/-- `HasSectorFilteredQACStability sys V δ_split` depends on `V` only through `V.totalPerturbation`. -/
theorem hasSectorFilteredQACStability_congr_V_tot {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (sys : IndexedCommutingProjectorHamiltonian D L Site ι)
    {V₁ V₂ : QuasiLocalPerturbation D L Site}
    (hV_eq : V₁.totalPerturbation = V₂.totalPerturbation) (δ_split : ℝ) :
    HasSectorFilteredQACStability sys V₁ δ_split ↔
      HasSectorFilteredQACStability sys V₂ δ_split := by
  unfold HasSectorFilteredQACStability
  rw [indexedHasStableLowEnergyBand_congr_V_tot sys hV_eq]
  refine and_congr_right' (exists_congr fun U => exists_congr fun c_shift => ?_)
  rw [hV_eq, satisfiesDressedEnergySandwich_congr_V_tot sys hV_eq U c_shift δ_split]

/-!
## 2. Commutativity Transfer from Check Projectors to `P0`, `localGroundProj`, and `syndromeProjector`
-/

/-- Any operator `M` that commutes with every element of a list `l` commutes with `l.prod`. -/
private lemma commute_list_prod_right_bhm {R : Type*} [Monoid R]
    (M : R) (l : List R) (h : ∀ x ∈ l, Commute M x) :
    Commute M l.prod := by
  induction l with
  | nil =>
    rw [List.prod_nil]
    exact Commute.one_right M
  | cons a tl ih =>
    rw [List.prod_cons]
    exact (h a List.mem_cons_self).mul_right
      (ih (fun x hx => h x (List.mem_cons_of_mem a hx)))

/-- If `M` commutes with every check projector `sys.checkProj i`, then `M` commutes with `sys.P0`. -/
theorem commute_P0_of_commute_checkProj {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (sys : IndexedCommutingProjectorHamiltonian D L Site ι)
    (M : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site)
    (h_comm : ∀ i : ι, Commute M (sys.checkProj i)) :
    Commute M sys.P0 := by
  unfold IndexedCommutingProjectorHamiltonian.P0 IndexedCommutingProjectorHamiltonian.groundProj
  apply commute_list_prod_right_bhm
  intro x hx
  rcases List.mem_map.mp hx with ⟨i, _, rfl⟩
  exact (Commute.one_right M).sub_right (h_comm i)

/-- The unperturbed Hamiltonian `sys.H0` commutes with `sys.P0`. -/
lemma commute_H0_P0_of_sys {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (sys : IndexedCommutingProjectorHamiltonian D L Site ι) :
    Commute sys.H0 sys.P0 := by
  unfold IndexedCommutingProjectorHamiltonian.H0
  refine Commute.sum_left Finset.univ _ _ fun j _ => ?_
  exact (commute_P0_of_commute_checkProj sys (sys.checkProj j)
    (fun i => sys.pairwise_commute j i)).smul_left _

/-- If `M` commutes with every check projector `sys.checkProj i`, then `M` commutes with `sys.P_loc B`. -/
theorem commute_P_loc_of_commute_checkProj {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (sys : IndexedCommutingProjectorHamiltonian D L Site ι)
    (M : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site)
    (h_comm : ∀ i : ι, Commute M (sys.checkProj i))
    (B : Finset (BoxD D L)) :
    Commute M (sys.localGroundProj B) := by
  unfold IndexedCommutingProjectorHamiltonian.localGroundProj
  apply commute_list_prod_right_bhm
  intro x hx
  rcases List.mem_map.mp hx with ⟨i, _, rfl⟩
  exact (Commute.one_right M).sub_right (h_comm i)

/-- If `M` commutes with every check projector `sys.checkProj i`, then `M` commutes with
    every syndrome projector `sys.syndromeProjector σ`. -/
theorem commute_syndromeProjector_of_commute_checkProj {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (sys : IndexedCommutingProjectorHamiltonian D L Site ι)
    (M : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site)
    (h_comm : ∀ i : ι, Commute M (sys.checkProj i))
    (σ : ι → Bool) :
    Commute M (sys.syndromeProjector σ) := by
  unfold IndexedCommutingProjectorHamiltonian.syndromeProjector
  apply commute_list_prod_right_bhm
  intro x hx
  rcases List.mem_map.mp hx with ⟨i, _, rfl⟩
  by_cases hσ : σ i
  · simp [hσ, h_comm i]
  · simp [hσ, (Commute.one_right M).sub_right (h_comm i)]

/-!
## 3. Direct Sector-Filtered QAC Stability under Check Commutativity
-/

/-- Direct `HasSectorFilteredQACStability sys V δ_split` whenever `V.totalPerturbation` commutes with all check
    projectors `sys.checkProj i` and satisfies the relative form bound against `sys.H0`. -/
theorem hasSectorFilteredQACStability_direct_of_commute_checkProj_and_form_bound
    {D L : ℕ} [NeZero D] [NeZero L]
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (sys : IndexedCommutingProjectorHamiltonian D L Site ι)
    (V : QuasiLocalPerturbation D L Site)
    (h_weight : ∀ i : ι, 1 ≤ sys.weight i)
    {δ_split E0 γ ε : ℝ}
    (hγ : γ ≤ 1 / 4) (h_gap : γ + 2 * ε ≤ 1 / 2) (h_split : 2 * ε ≤ δ_split)
    (h_comm_checks : ∀ i : ι, Commute V.totalPerturbation (sys.checkProj i))
    (h_form : ∀ ϕ : ManyBodyHilbertSpace Site,
      |RCLike.re (inner ℂ ϕ ((V.totalPerturbation - (E0 : ℂ) • 1) ϕ))| ≤
        γ * RCLike.re (inner ℂ ϕ (sys.H0 ϕ)) + ε * ‖ϕ‖ ^ 2) :
    HasSectorFilteredQACStability sys V δ_split := by
  have h_comm_V_P0 : Commute V.totalPerturbation sys.P0 :=
    commute_P0_of_commute_checkProj sys V.totalPerturbation h_comm_checks
  have h_comm_tot : Commute (sys.H0 + V.totalPerturbation) sys.P0 :=
    (commute_H0_P0_of_sys sys).add_left h_comm_V_P0
  exact hasSectorFilteredQACStability_of_commute_and_form_bound sys V h_weight
    hγ h_gap h_split h_comm_tot h_form

end
