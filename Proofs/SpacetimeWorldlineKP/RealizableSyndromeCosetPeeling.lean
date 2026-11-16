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

import Proofs.SpacetimeWorldlineKP.SpectralBoltzmannDuhamelIdentity
import Proofs.InhomogeneousPeierls.SyndromeSignAndPauliFlips
import Proofs.HierarchicalClusterDecoder.WalshFourierCosetAndHomology

noncomputable section

open scoped Classical BigOperators InnerProduct ComplexConjugate
open Filter Topology Asymptotics ContinuousLinearMap KMSPinchedGibbs PerturbedThermalBarrier

set_option linter.constructorNameAsVariable false
set_option linter.unusedVariables false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000

namespace SpacetimeWorldlineKP

/-!
# Realizable CSS Syndrome Subspaces and Bare Walsh–Hadamard Coset Peeling

Characterizes the F₂-linear subspace of realizable static CSS syndromes (`realizableSyndromes`, `realizableZeroOutsideSyndromes`) and proves constant trace multiplicity across realizable syndrome fibers (`hilbertTrace_syndromeProjector_eq_P0_of_ne_zero`). Establishes the Walsh–Hadamard affine coset energy inequality (`coset_syndromeEnergy_sum_le_of_syndromeXor_subspace`) and the bare static CSS witness Gibbs bound (`gibbsFailureProb_bare_staticCSS_positiveCheckWitnessProj_le`).

## References

* Part I, Section 5.3 (`subsec:walsh-fourier-peierls`), Theorem 5.5 (`thm:walsh-fourier-peierls`)
* Part II, Section 3.3 (`subsec:walsh-coset-peeling`), Proposition 3.5 (`prop:witness-coset-reduction`)
* Part II, Section 3.3 (`subsec:walsh-coset-peeling`), Proposition 3.6 (`prop:walsh-coset-dominance`)
-/

/-- **Pointwise Equality of `syndromeProjector` and `P0` with `staticCSSSystem`
    (`syndromeProjector_and_P0_eq_staticCSSSystem`)**:
    Whenever `sys.checkProj idx = staticCSSCheckProj D_field idx` for all `idx`, `sys.syndromeProjector`
    and `sys.P0` agree identically with those of `staticCSSSystem D_field h_valid`. -/
theorem syndromeProjector_and_P0_eq_staticCSSSystem
    {L q_code r_0 m_max : ℕ}
    (D_field : Box3D L → LocalCSSDescriptor q_code r_0 m_max)
    (h_valid : ValidDescriptorField D_field)
    (sys : IndexedCommutingProjectorHamiltonian 3 L
      (UniformSite3D L (CodeSlotConfig q_code))
      (StaticCSSCheckIdx L q_code m_max))
    (h_sys_checks : ∀ idx : StaticCSSCheckIdx L q_code m_max,
      sys.checkProj idx = staticCSSCheckProj D_field idx ∧
      sys.support idx = staticCSSCheckSupport D_field idx ∧
      sys.weight idx = 1) :
    (∀ σ : StaticCSSCheckIdx L q_code m_max → Bool,
      sys.syndromeProjector σ = (staticCSSSystem D_field h_valid).syndromeProjector σ) ∧
    sys.P0 = (staticCSSSystem D_field h_valid).P0 := by
  refine ⟨fun σ => ?_, ?_⟩
  · unfold IndexedCommutingProjectorHamiltonian.syndromeProjector
    congr 1
    exact List.map_congr_left fun i _ => by rw [(h_sys_checks i).1]; rfl
  · unfold IndexedCommutingProjectorHamiltonian.P0 IndexedCommutingProjectorHamiltonian.groundProj
    congr 1
    exact List.map_congr_left fun i _ => by rw [(h_sys_checks i).1]; rfl

/-- **Equal Sector Trace & Pauli Flip Realizability for Non-Zero Syndromes
    (`hilbertTrace_syndromeProjector_eq_P0_of_ne_zero`)**:
    By `exists_chains_of_syndromeProjector_ne_zero` (`SyndromeSignAndPauliFlips.lean`), every
    syndrome $\sigma$ with `sys.syndromeProjector σ ≠ 0` is realized by a Weyl–Pauli operator
    `σ = staticCSSPauliFlip D_field a b` and has sector trace equal to `hilbertTrace sys.P0`. -/
theorem hilbertTrace_syndromeProjector_eq_P0_of_ne_zero
    {L q_code r_0 m_max : ℕ}
    (D_field : Box3D L → LocalCSSDescriptor q_code r_0 m_max)
    (h_valid : ValidDescriptorField D_field)
    (sys : IndexedCommutingProjectorHamiltonian 3 L
      (UniformSite3D L (CodeSlotConfig q_code))
      (StaticCSSCheckIdx L q_code m_max))
    (h_sys_checks : ∀ idx : StaticCSSCheckIdx L q_code m_max,
      sys.checkProj idx = staticCSSCheckProj D_field idx ∧
      sys.support idx = staticCSSCheckSupport D_field idx ∧
      sys.weight idx = 1)
    (σ : StaticCSSCheckIdx L q_code m_max → Bool)
    (hσ : sys.syndromeProjector σ ≠ 0) :
    (∃ a b : BoxSlot3D L q_code → ZMod 2, σ = staticCSSPauliFlip D_field a b) ∧
    hilbertTrace (sys.syndromeProjector σ) = hilbertTrace sys.P0 := by
  have h_eq := syndromeProjector_and_P0_eq_staticCSSSystem D_field h_valid sys h_sys_checks
  rw [h_eq.1 σ] at hσ ⊢
  rw [h_eq.2]
  rcases exists_chains_of_syndromeProjector_ne_zero D_field h_valid σ hσ with ⟨a, b, hab, htr⟩
  exact ⟨⟨a, b, hab⟩, htr⟩

/-- **Equal Sector Trace for Every Pauli-Flipped Syndrome
    (`hilbertTrace_syndromeProjector_staticCSSPauliFlip_eq_P0`)**:
    Every syndrome in the image of `staticCSSPauliFlip D_field` has sector trace equal to
    `hilbertTrace sys.P0`. -/
theorem hilbertTrace_syndromeProjector_staticCSSPauliFlip_eq_P0
    {L q_code r_0 m_max : ℕ}
    (D_field : Box3D L → LocalCSSDescriptor q_code r_0 m_max)
    (h_valid : ValidDescriptorField D_field)
    (sys : IndexedCommutingProjectorHamiltonian 3 L
      (UniformSite3D L (CodeSlotConfig q_code))
      (StaticCSSCheckIdx L q_code m_max))
    (h_sys_checks : ∀ idx : StaticCSSCheckIdx L q_code m_max,
      sys.checkProj idx = staticCSSCheckProj D_field idx ∧
      sys.support idx = staticCSSCheckSupport D_field idx ∧
      sys.weight idx = 1)
    (a b : BoxSlot3D L q_code → ZMod 2) :
    hilbertTrace (sys.syndromeProjector (staticCSSPauliFlip D_field a b)) =
      hilbertTrace sys.P0 := by
  have h_eq := syndromeProjector_and_P0_eq_staticCSSSystem D_field h_valid sys h_sys_checks
  rw [h_eq.1 (staticCSSPauliFlip D_field a b), h_eq.2]
  exact hilbertTrace_syndromeProjector_staticCSSPauliFlip_eq D_field h_valid a b

/-- **Realizable Syndrome Subspace (`realizableSyndromes`)**:
    The $\mathbb{F}_2$-linear subspace of syndromes in the image of `staticCSSPauliFlip D_field`. -/
def realizableSyndromes {L q_code r_0 m_max : ℕ}
    (D_field : Box3D L → LocalCSSDescriptor q_code r_0 m_max) :
    Finset (StaticCSSCheckIdx L q_code m_max → Bool) :=
  Finset.univ.filter (fun σ =>
    ∃ a b : BoxSlot3D L q_code → ZMod 2, σ = staticCSSPauliFlip D_field a b)

/-- **Witness-Clean Realizable Syndrome Subspace (`realizableZeroOutsideSyndromes`)**:
    The $\mathbb{F}_2$-linear subspace $C_0(W) = \{c \in \mathrm{realizableSyndromes}\;D_{\mathrm{field}} \mid \forall i \in W,\, c(i) = \mathrm{false}\}$. -/
def realizableZeroOutsideSyndromes {L q_code r_0 m_max : ℕ}
    (D_field : Box3D L → LocalCSSDescriptor q_code r_0 m_max)
    (W : Finset (StaticCSSCheckIdx L q_code m_max)) :
    Finset (StaticCSSCheckIdx L q_code m_max → Bool) :=
  (realizableSyndromes D_field).filter (fun c => ∀ idx ∈ W, c idx = false)

private lemma zmod2_decide_add_ne_zero (x y : ZMod 2) :
    decide ((x + y) ≠ 0) = bne (decide (x ≠ 0)) (decide (y ≠ 0)) := by
  revert x y; decide

private lemma bool_and_bne_distrib_left (p q r : Bool) :
    (p && bne q r) = bne (p && q) (p && r) := by
  cases p <;> cases q <;> cases r <;> rfl

/-- **$\mathbb{F}_2$-Additivity of `staticCSSPauliFlip`
    (`staticCSSPauliFlip_add`)**:
    `staticCSSPauliFlip D_field` is an $\mathbb{F}_2$-linear map from Pauli exponent chains
    `(a, b)` to syndrome bitstrings under `syndromeXor`. -/
theorem staticCSSPauliFlip_add {L q_code r_0 m_max : ℕ}
    (D_field : Box3D L → LocalCSSDescriptor q_code r_0 m_max)
    (a₁ a₂ b₁ b₂ : BoxSlot3D L q_code → ZMod 2) :
    staticCSSPauliFlip D_field (a₁ + a₂) (b₁ + b₂) =
      syndromeXor (staticCSSPauliFlip D_field a₁ b₁) (staticCSSPauliFlip D_field a₂ b₂) := by
  ext i
  rcases i with ⟨v, s⟩ | ⟨v, idx⟩ | ⟨v, idx⟩
  · have h_sum : (∑ p, singleSlotChain v s p * (b₁ + b₂) p) =
        (∑ p, singleSlotChain v s p * b₁ p) + (∑ p, singleSlotChain v s p * b₂ p) := by
      simp_rw [Pi.add_apply, mul_add, Finset.sum_add_distrib]
    simp only [staticCSSPauliFlip, syndromeXor, h_sum, zmod2_decide_add_ne_zero,
      bool_and_bne_distrib_left]
  · have h_sum : (∑ p, (a₁ + a₂) p * descriptorCheckXChain D_field v idx p) =
        (∑ p, a₁ p * descriptorCheckXChain D_field v idx p) +
          (∑ p, a₂ p * descriptorCheckXChain D_field v idx p) := by
      simp_rw [Pi.add_apply, add_mul, Finset.sum_add_distrib]
    simp only [staticCSSPauliFlip, syndromeXor, h_sum, zmod2_decide_add_ne_zero,
      bool_and_bne_distrib_left]
  · have h_sum : (∑ p, descriptorCheckZChain D_field v idx p * (b₁ + b₂) p) =
        (∑ p, descriptorCheckZChain D_field v idx p * b₁ p) +
          (∑ p, descriptorCheckZChain D_field v idx p * b₂ p) := by
      simp_rw [Pi.add_apply, mul_add, Finset.sum_add_distrib]
    simp only [staticCSSPauliFlip, syndromeXor, h_sum, zmod2_decide_add_ne_zero,
      bool_and_bne_distrib_left]

/-- **$\mathbb{F}_2$-Subspace Closure of `realizableZeroOutsideSyndromes`
    (`zero_mem_and_syndromeXor_closed_realizableZeroOutsideSyndromes`)**:
    `realizableZeroOutsideSyndromes D_field W` contains the zero syndrome `fun _ => false` and is
    closed under `syndromeXor`. -/
theorem zero_mem_and_syndromeXor_closed_realizableZeroOutsideSyndromes
    {L q_code r_0 m_max : ℕ}
    (D_field : Box3D L → LocalCSSDescriptor q_code r_0 m_max)
    (W : Finset (StaticCSSCheckIdx L q_code m_max)) :
    (fun _ => false) ∈ realizableZeroOutsideSyndromes D_field W ∧
    ∀ c₁ ∈ realizableZeroOutsideSyndromes D_field W,
      ∀ c₂ ∈ realizableZeroOutsideSyndromes D_field W,
        syndromeXor c₁ c₂ ∈ realizableZeroOutsideSyndromes D_field W := by
  refine ⟨?_, fun c₁ hc₁ c₂ hc₂ => ?_⟩
  · rw [realizableZeroOutsideSyndromes, Finset.mem_filter, realizableSyndromes, Finset.mem_filter]
    refine ⟨⟨Finset.mem_univ _, 0, 0, ?_⟩, fun _ _ => rfl⟩
    ext i
    rcases i with ⟨v, s⟩ | ⟨v, idx⟩ | ⟨v, idx⟩ <;> simp [staticCSSPauliFlip]
  · rw [realizableZeroOutsideSyndromes, Finset.mem_filter, realizableSyndromes, Finset.mem_filter] at hc₁ hc₂ ⊢
    rcases hc₁ with ⟨⟨_, a₁, b₁, rfl⟩, hW₁⟩
    rcases hc₂ with ⟨⟨_, a₂, b₂, rfl⟩, hW₂⟩
    refine ⟨⟨Finset.mem_univ _, a₁ + a₂, b₁ + b₂,
      (staticCSSPauliFlip_add D_field a₁ a₂ b₁ b₂).symm⟩, fun idx hidx => ?_⟩
    unfold syndromeXor
    rw [hW₁ idx hidx, hW₂ idx hidx]
    rfl

/-- **Witness-Cleared Syndrome Projection (`witnessClearedSyndrome`)**:
    Sets all syndrome bits inside $W$ to `false` while preserving all bits outside $W$. -/
def witnessClearedSyndrome {ι : Type} [DecidableEq ι]
    (W : Finset ι) (σ : ι → Bool) : ι → Bool :=
  fun idx => if idx ∈ W then false else σ idx

/-- **Syndrome Energy Coset Splitting Along $W$
    (`syndromeEnergy_syndromeXor_witness_clear_eq`)**:
    For any unit-weight system `sys` (`∀ idx, sys.weight idx = 1`), any $\sigma_0$ satisfying
    $\forall i \in W,\, \sigma_0(i) = \mathrm{true}$, and any $c$ satisfying
    $\forall i \in W,\, c(i) = \mathrm{false}$,
    $$\mathrm{sys.syndromeEnergy}(\mathrm{syndromeXor}\;\sigma_0\;c)
      = (W.\mathrm{card} : \mathbb{R}) +
        \mathrm{sys.syndromeEnergy}\bigl(\mathrm{syndromeXor}\;(\mathrm{witnessClearedSyndrome}\;W\;\sigma_0)\;c\bigr).$$ -/
theorem syndromeEnergy_syndromeXor_witness_clear_eq
    {D L : ℕ} {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (sys : IndexedCommutingProjectorHamiltonian D L Site ι)
    (h_wt : ∀ idx : ι, sys.weight idx = 1)
    (W : Finset ι)
    {σ₀ c : ι → Bool}
    (hσ₀ : ∀ idx ∈ W, σ₀ idx = true)
    (hc : ∀ idx ∈ W, c idx = false) :
    sys.syndromeEnergy (syndromeXor σ₀ c) =
      (W.card : ℝ) + sys.syndromeEnergy (syndromeXor (witnessClearedSyndrome W σ₀) c) := by
  have h_disj : ∀ idx : ι,
      ¬((if idx ∈ W then true else false) = true ∧
        syndromeXor (witnessClearedSyndrome W σ₀) c idx = true) := by
    intro idx
    by_cases h_in : idx ∈ W
    · simp [witnessClearedSyndrome, syndromeXor, h_in, hc idx h_in]
    · simp [h_in]
  have h_xor_eq :
      syndromeXor σ₀ c =
        syndromeXor (fun idx => if idx ∈ W then true else false)
          (syndromeXor (witnessClearedSyndrome W σ₀) c) := by
    ext idx
    by_cases h_in : idx ∈ W
    · simp [witnessClearedSyndrome, syndromeXor, h_in, hσ₀ idx h_in, hc idx h_in]
    · simp [witnessClearedSyndrome, syndromeXor, h_in]
  rw [h_xor_eq, syndromeEnergy_syndromeXor_eq_add_of_disjoint sys h_disj]
  congr 1
  unfold IndexedCommutingProjectorHamiltonian.syndromeEnergy
  have h_filt :
      Finset.univ.filter (fun i : ι => (if i ∈ W then true else false) = true) = W := by
    ext i
    simp
  rw [h_filt]
  calc ∑ i ∈ W, sys.weight i
    _ = ∑ _i ∈ W, (1 : ℝ) := Finset.sum_congr rfl fun i _ => h_wt i
    _ = (W.card : ℝ) := by rw [Finset.sum_const, nsmul_eq_mul, mul_one]

def syndromeToZMod2 {ι : Type} (σ : ι → Bool) : ι → ZMod 2 :=
  fun i => if σ i then 1 else 0

lemma syndromeToZMod2_ne_zero_iff {ι : Type} (σ : ι → Bool) (i : ι) :
    syndromeToZMod2 σ i ≠ 0 ↔ σ i = true := by
  dsimp [syndromeToZMod2]
  cases σ i <;> decide

lemma bool_if_bne_zmod2 (b₁ b₂ : Bool) :
    (if bne b₁ b₂ then (1 : ZMod 2) else 0) =
      (if b₁ then 1 else 0) + (if b₂ then 1 else 0) := by
  revert b₁ b₂; decide

lemma syndromeToZMod2_syndromeXor {ι : Type} (σ₁ σ₂ : ι → Bool) :
    syndromeToZMod2 (syndromeXor σ₁ σ₂) = syndromeToZMod2 σ₁ + syndromeToZMod2 σ₂ := by
  ext i
  exact bool_if_bne_zmod2 (σ₁ i) (σ₂ i)

lemma syndromeEnergy_eq_bdl_syndromeWeight
    {D L : ℕ} {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (sys : IndexedCommutingProjectorHamiltonian D L Site ι)
    (h_wt : ∀ idx : ι, sys.weight idx = 1) (σ : ι → Bool) :
    sys.syndromeEnergy σ = WeldedHierarchy.syndromeWeight (syndromeToZMod2 σ) := by
  unfold IndexedCommutingProjectorHamiltonian.syndromeEnergy WeldedHierarchy.syndromeWeight
  have h_filt :
      Finset.univ.filter (fun i : ι => σ i = true) =
        Finset.univ.filter (fun i : ι => syndromeToZMod2 σ i ≠ 0) := by
    ext i
    simp [syndromeToZMod2_ne_zero_iff]
  rw [h_filt]
  calc ∑ i ∈ Finset.univ.filter (fun i : ι => syndromeToZMod2 σ i ≠ 0), sys.weight i
    _ = ∑ _i ∈ Finset.univ.filter (fun i : ι => syndromeToZMod2 σ i ≠ 0), (1 : ℝ) :=
      Finset.sum_congr rfl fun i _ => h_wt i
    _ = ((Finset.univ.filter (fun i : ι => syndromeToZMod2 σ i ≠ 0)).card : ℝ) := by
      rw [Finset.sum_const, nsmul_eq_mul, mul_one]

lemma syndromeXor_cancel_left {ι : Type} (σ₁ σ₂ : ι → Bool) :
    syndromeXor σ₁ (syndromeXor σ₁ σ₂) = σ₂ := by
  ext i
  dsimp [syndromeXor]
  cases σ₁ i <;> cases σ₂ i <;> rfl

lemma sum_subsetChar_syndromeXor_subspace_nonneg
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (C₀ : Finset (ι → Bool))
    (h0_mem : (fun _ => false) ∈ C₀)
    (h_closed : ∀ c₁ ∈ C₀, ∀ c₂ ∈ C₀, syndromeXor c₁ c₂ ∈ C₀)
    (T : Finset ι) :
    0 ≤ ∑ c ∈ C₀, WeldedHierarchy.subsetChar T (syndromeToZMod2 c) := by
  let S := ∑ c ∈ C₀, WeldedHierarchy.subsetChar T (syndromeToZMod2 c)
  have h_shift : ∀ c₁ ∈ C₀,
      ∑ c ∈ C₀, WeldedHierarchy.subsetChar T (syndromeToZMod2 c₁ + syndromeToZMod2 c) = S := by
    intro c₁ hc₁
    refine Finset.sum_bij (fun c _ => syndromeXor c₁ c) ?_ ?_ ?_ ?_
    · intro c hc
      exact h_closed c₁ hc₁ c hc
    · intro a _ b _ hab
      (try dsimp only at hab)
      rw [← syndromeXor_cancel_left c₁ a, ← syndromeXor_cancel_left c₁ b, hab]
    · intro b hb
      exact ⟨syndromeXor c₁ b, h_closed c₁ hc₁ b hb, syndromeXor_cancel_left c₁ b⟩
    · intro c _
      rw [← syndromeToZMod2_syndromeXor]
  have h_mul : ∀ c₁ ∈ C₀, WeldedHierarchy.subsetChar T (syndromeToZMod2 c₁) * S = S := by
    intro c₁ hc₁
    calc WeldedHierarchy.subsetChar T (syndromeToZMod2 c₁) * S
      _ = ∑ c ∈ C₀,
            WeldedHierarchy.subsetChar T (syndromeToZMod2 c₁) *
              WeldedHierarchy.subsetChar T (syndromeToZMod2 c) := Finset.mul_sum _ _ _
      _ = ∑ c ∈ C₀, WeldedHierarchy.subsetChar T (syndromeToZMod2 c₁ + syndromeToZMod2 c) :=
          Finset.sum_congr rfl fun c _ =>
            (WeldedHierarchy.subsetChar_add T (syndromeToZMod2 c₁) (syndromeToZMod2 c)).symm
      _ = S := h_shift c₁ hc₁
  have h_sq : S * S = (C₀.card : ℝ) * S := by
    calc S * S
      _ = ∑ c₁ ∈ C₀, WeldedHierarchy.subsetChar T (syndromeToZMod2 c₁) * S := Finset.sum_mul _ _ _
      _ = ∑ _c₁ ∈ C₀, S := Finset.sum_congr rfl h_mul
      _ = (C₀.card : ℝ) * S := by rw [Finset.sum_const, nsmul_eq_mul]
  have hC₀_pos : (0 : ℝ) < C₀.card := by
    exact_mod_cast Finset.card_pos.mpr ⟨fun _ => false, h0_mem⟩
  have hS_sq_nonneg : 0 ≤ S * S := mul_self_nonneg S
  nlinarith

/-- **Walsh–Hadamard Coset Domination on `syndromeXor`-Closed Subspaces
    (`coset_syndromeEnergy_sum_le_of_syndromeXor_subspace`)**:
    For any unit-weight system `sys` (`∀ idx, sys.weight idx = 1`), any $\beta_{\mathrm{eff}} \ge 0$,
    any `syndromeXor`-closed subset $C_0 \subseteq (\iota \to \mathrm{Bool})$ containing
    `fun _ => false`, and any shift $s_{\mathrm{out}} : \iota \to \mathrm{Bool}$,
    expanding $\exp(-\beta_{\mathrm{eff}} \cdot \mathrm{sys.syndromeEnergy}\;\sigma)$ in the
    high-temperature Walsh–Hadamard character basis (`exp_neg_beta_syndromeWeight_eq_sum_subsetChar`,
    `subsetChar_add`, `subsetChar_le_one`, `WalshFourierCosetAndHomology.lean`) and using that
    the character sum over the $\mathbb{F}_2$-linear subspace $C_0$ is non-negative yields:
    $$\sum_{c \in C_0} \exp\bigl(-\beta_{\mathrm{eff}} \cdot \mathrm{sys.syndromeEnergy}(\mathrm{syndromeXor}\;s_{\mathrm{out}}\;c)\bigr)
      \le \sum_{c \in C_0} \exp\bigl(-\beta_{\mathrm{eff}} \cdot \mathrm{sys.syndromeEnergy}\;c\bigr).$$ -/
theorem coset_syndromeEnergy_sum_le_of_syndromeXor_subspace
    {D L : ℕ} {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (sys : IndexedCommutingProjectorHamiltonian D L Site ι)
    (h_wt : ∀ idx : ι, sys.weight idx = 1)
    {β_eff : ℝ} (hβ_eff : 0 ≤ β_eff)
    (C₀ : Finset (ι → Bool))
    (h0_mem : (fun _ => false) ∈ C₀)
    (h_closed : ∀ c₁ ∈ C₀, ∀ c₂ ∈ C₀, syndromeXor c₁ c₂ ∈ C₀)
    (s_out : ι → Bool) :
    (∑ c ∈ C₀, Real.exp (-β_eff * sys.syndromeEnergy (syndromeXor s_out c))) ≤
      ∑ c ∈ C₀, Real.exp (-β_eff * sys.syndromeEnergy c) := by
  let a := (1 + Real.exp (-β_eff)) / 2
  let b := (1 - Real.exp (-β_eff)) / 2
  have hexp_le : Real.exp (-β_eff) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
  have hexp_pos : 0 < Real.exp (-β_eff) := Real.exp_pos _
  have ha_nonneg : 0 ≤ a := by dsimp [a]; linarith
  have hb_nonneg : 0 ≤ b := by dsimp [b]; linarith
  have h_lhs :
      (∑ c ∈ C₀, Real.exp (-β_eff * sys.syndromeEnergy (syndromeXor s_out c))) =
        ∑ T ∈ (Finset.univ : Finset ι).powerset,
          (b ^ T.card * a ^ ((Finset.univ : Finset ι) \ T).card) *
            (WeldedHierarchy.subsetChar T (syndromeToZMod2 s_out) *
              ∑ c ∈ C₀, WeldedHierarchy.subsetChar T (syndromeToZMod2 c)) := by
    trans (∑ c ∈ C₀, ∑ T ∈ (Finset.univ : Finset ι).powerset,
      (b ^ T.card * a ^ ((Finset.univ : Finset ι) \ T).card) *
        WeldedHierarchy.subsetChar T (syndromeToZMod2 s_out + syndromeToZMod2 c))
    · refine Finset.sum_congr rfl fun c _ => ?_
      rw [syndromeEnergy_eq_bdl_syndromeWeight sys h_wt (syndromeXor s_out c),
        syndromeToZMod2_syndromeXor]
      exact WeldedHierarchy.exp_neg_beta_syndromeWeight_eq_sum_subsetChar β_eff
        (syndromeToZMod2 s_out + syndromeToZMod2 c)
    · rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun T _ => ?_
      simp_rw [WeldedHierarchy.subsetChar_add T (syndromeToZMod2 s_out), ← mul_assoc, ← Finset.mul_sum]
  have h_rhs :
      (∑ c ∈ C₀, Real.exp (-β_eff * sys.syndromeEnergy c)) =
        ∑ T ∈ (Finset.univ : Finset ι).powerset,
          (b ^ T.card * a ^ ((Finset.univ : Finset ι) \ T).card) *
            (∑ c ∈ C₀, WeldedHierarchy.subsetChar T (syndromeToZMod2 c)) := by
    trans (∑ c ∈ C₀, ∑ T ∈ (Finset.univ : Finset ι).powerset,
      (b ^ T.card * a ^ ((Finset.univ : Finset ι) \ T).card) *
        WeldedHierarchy.subsetChar T (syndromeToZMod2 c))
    · refine Finset.sum_congr rfl fun c _ => ?_
      rw [syndromeEnergy_eq_bdl_syndromeWeight sys h_wt c]
      exact WeldedHierarchy.exp_neg_beta_syndromeWeight_eq_sum_subsetChar β_eff (syndromeToZMod2 c)
    · rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun T _ => ?_
      rw [← Finset.mul_sum]
  rw [h_lhs, h_rhs]
  refine Finset.sum_le_sum fun T _ => ?_
  have h_coeff : 0 ≤ b ^ T.card * a ^ ((Finset.univ : Finset ι) \ T).card :=
    mul_nonneg (pow_nonneg hb_nonneg _) (pow_nonneg ha_nonneg _)
  have h_sum_T : 0 ≤ ∑ c ∈ C₀, WeldedHierarchy.subsetChar T (syndromeToZMod2 c) :=
    sum_subsetChar_syndromeXor_subspace_nonneg C₀ h0_mem h_closed T
  have h_c_le : WeldedHierarchy.subsetChar T (syndromeToZMod2 s_out) ≤ 1 :=
    WeldedHierarchy.subsetChar_le_one T (syndromeToZMod2 s_out)
  have h_inner :
      WeldedHierarchy.subsetChar T (syndromeToZMod2 s_out) *
          (∑ c ∈ C₀, WeldedHierarchy.subsetChar T (syndromeToZMod2 c)) ≤
        ∑ c ∈ C₀, WeldedHierarchy.subsetChar T (syndromeToZMod2 c) := by
    nlinarith
  exact mul_le_mul_of_nonneg_left h_inner h_coeff

private lemma syndromeXor_closed_realizableSyndromes
    {L q_code r_0 m_max : ℕ}
    (D_field : Box3D L → LocalCSSDescriptor q_code r_0 m_max)
    {σ₁ σ₂ : StaticCSSCheckIdx L q_code m_max → Bool}
    (hσ₁ : σ₁ ∈ realizableSyndromes D_field)
    (hσ₂ : σ₂ ∈ realizableSyndromes D_field) :
    syndromeXor σ₁ σ₂ ∈ realizableSyndromes D_field := by
  rw [realizableSyndromes, Finset.mem_filter] at hσ₁ hσ₂ ⊢
  rcases hσ₁.2 with ⟨a₁, b₁, rfl⟩
  rcases hσ₂.2 with ⟨a₂, b₂, rfl⟩
  exact ⟨Finset.mem_univ _, a₁ + a₂, b₁ + b₂,
    (staticCSSPauliFlip_add D_field a₁ a₂ b₁ b₂).symm⟩

private lemma realizable_witness_syndromeEnergy_sum_le
    {L q_code r_0 m_max : ℕ}
    (D_field : Box3D L → LocalCSSDescriptor q_code r_0 m_max)
    (sys : IndexedCommutingProjectorHamiltonian 3 L
      (UniformSite3D L (CodeSlotConfig q_code))
      (StaticCSSCheckIdx L q_code m_max))
    (h_wt : ∀ idx : StaticCSSCheckIdx L q_code m_max, sys.weight idx = 1)
    {β_eff : ℝ} (hβ_eff : 0 ≤ β_eff)
    (W : Finset (StaticCSSCheckIdx L q_code m_max)) :
    (∑ σ ∈ (realizableSyndromes D_field).filter (fun σ => ∀ idx ∈ W, σ idx = true),
        Real.exp (-β_eff * sys.syndromeEnergy σ)) ≤
      Real.exp (-β_eff * (W.card : ℝ)) *
        ∑ σ ∈ realizableSyndromes D_field, Real.exp (-β_eff * sys.syndromeEnergy σ) := by
  let R := realizableSyndromes D_field
  let R_W := R.filter (fun σ => ∀ idx ∈ W, σ idx = true)
  let C₀ := realizableZeroOutsideSyndromes D_field W
  change (∑ σ ∈ R_W, Real.exp (-β_eff * sys.syndromeEnergy σ)) ≤
    Real.exp (-β_eff * (W.card : ℝ)) * ∑ σ ∈ R, Real.exp (-β_eff * sys.syndromeEnergy σ)
  have hC₀_props := zero_mem_and_syndromeXor_closed_realizableZeroOutsideSyndromes D_field W
  by_cases h_ne : R_W.Nonempty
  · rcases h_ne with ⟨σ₀, hσ₀_mem⟩
    rcases Finset.mem_filter.mp hσ₀_mem with ⟨hσ₀_R, hσ₀_W⟩
    have h_bij :
        (∑ σ ∈ R_W, Real.exp (-β_eff * sys.syndromeEnergy σ)) =
          ∑ c ∈ C₀, Real.exp (-β_eff * sys.syndromeEnergy (syndromeXor σ₀ c)) := by
      symm
      refine Finset.sum_bij (fun c _ => syndromeXor σ₀ c) ?_ ?_ ?_ ?_
      · intro c hc
        rcases Finset.mem_filter.mp hc with ⟨hc_R, hc_W⟩
        refine Finset.mem_filter.mpr ⟨syndromeXor_closed_realizableSyndromes D_field hσ₀_R hc_R, ?_⟩
        intro idx hidx; dsimp [syndromeXor]; rw [hσ₀_W idx hidx, hc_W idx hidx]; rfl
      · intro c₁ _ c₂ _ h_eq
        (try dsimp only at h_eq)
        rw [← syndromeXor_cancel_left σ₀ c₁, ← syndromeXor_cancel_left σ₀ c₂, h_eq]
      · intro σ hσ
        rcases Finset.mem_filter.mp hσ with ⟨hσ_R, hσ_W⟩
        refine ⟨syndromeXor σ₀ σ, Finset.mem_filter.mpr
          ⟨syndromeXor_closed_realizableSyndromes D_field hσ₀_R hσ_R, ?_⟩,
          syndromeXor_cancel_left σ₀ σ⟩
        intro idx hidx; dsimp [syndromeXor]; rw [hσ₀_W idx hidx, hσ_W idx hidx]; rfl
      · intro _ _; rfl
    have h_peel :
        (∑ c ∈ C₀, Real.exp (-β_eff * sys.syndromeEnergy (syndromeXor σ₀ c))) =
          Real.exp (-β_eff * (W.card : ℝ)) *
            ∑ c ∈ C₀, Real.exp (-β_eff *
              sys.syndromeEnergy (syndromeXor (witnessClearedSyndrome W σ₀) c)) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun c hc => ?_
      rw [syndromeEnergy_syndromeXor_witness_clear_eq sys h_wt W hσ₀_W (Finset.mem_filter.mp hc).2,
        mul_add, Real.exp_add]
    calc (∑ σ ∈ R_W, Real.exp (-β_eff * sys.syndromeEnergy σ))
      _ = Real.exp (-β_eff * (W.card : ℝ)) *
            ∑ c ∈ C₀, Real.exp (-β_eff *
              sys.syndromeEnergy (syndromeXor (witnessClearedSyndrome W σ₀) c)) :=
        h_bij.trans h_peel
      _ ≤ Real.exp (-β_eff * (W.card : ℝ)) *
            ∑ c ∈ C₀, Real.exp (-β_eff * sys.syndromeEnergy c) :=
        mul_le_mul_of_nonneg_left
          (coset_syndromeEnergy_sum_le_of_syndromeXor_subspace sys h_wt hβ_eff C₀
            hC₀_props.1 hC₀_props.2 (witnessClearedSyndrome W σ₀))
          (le_of_lt (Real.exp_pos _))
      _ ≤ Real.exp (-β_eff * (W.card : ℝ)) *
            ∑ σ ∈ R, Real.exp (-β_eff * sys.syndromeEnergy σ) :=
        mul_le_mul_of_nonneg_left
          (Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
            fun _ _ _ => le_of_lt (Real.exp_pos _))
          (le_of_lt (Real.exp_pos _))
  · rw [Finset.not_nonempty_iff_eq_empty.mp h_ne, Finset.sum_empty]
    exact mul_nonneg (le_of_lt (Real.exp_pos _))
      (Finset.sum_nonneg fun _ _ => le_of_lt (Real.exp_pos _))

private lemma gibbsFailureProb_bare_le_of_realizable_sum_le
    {D L : ℕ} {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    [∀ x, Nonempty (Site x)]
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (sys : IndexedCommutingProjectorHamiltonian D L Site ι)
    (β r : ℝ) (W : Finset ι) (R R_W : Finset (ι → Bool))
    (hR_W : ∀ σ : ι → Bool, σ ∈ R_W ↔ (∀ c ∈ W, σ c = true) ∧ σ ∈ R)
    (h_tr_mem : ∀ σ ∈ R, hilbertTrace (sys.syndromeProjector σ) = hilbertTrace sys.P0)
    (h_tr_not_mem : ∀ σ : ι → Bool, σ ∉ R → hilbertTrace (sys.syndromeProjector σ) = 0)
    (h_coset_le :
      (∑ σ ∈ R_W, Real.exp (-β * sys.syndromeEnergy σ)) ≤
        r * ∑ σ ∈ R, Real.exp (-β * sys.syndromeEnergy σ)) :
    gibbsFailureProb sys.H0 sys.isSelfAdjoint_H0 β (positiveCheckWitnessProj sys W) ≤ r := by
  have h_tr : ∀ σ : ι → Bool,
      hilbertTrace (sys.syndromeProjector σ) = if σ ∈ R then hilbertTrace sys.P0 else 0 := by
    intro σ
    by_cases h : σ ∈ R
    · rw [if_pos h]; exact h_tr_mem σ h
    · rw [if_neg h]; exact h_tr_not_mem σ h
  have hT0_nonneg : 0 ≤ hilbertTrace sys.P0 := by
    rw [← (_root_.syndrome_resolution_indexed sys).1]
    exact hilbertTrace_syndromeProjector_nonneg sys (fun _ => false)
  have h_num_eq :
      (∑ σ ∈ Finset.univ.filter (fun σ : ι → Bool => ∀ c ∈ W, σ c = true),
        Real.exp (-β * sys.syndromeEnergy σ) * hilbertTrace (sys.syndromeProjector σ)) =
        (∑ σ ∈ R_W, Real.exp (-β * sys.syndromeEnergy σ)) * hilbertTrace sys.P0 := by
    simp_rw [h_tr, mul_ite, mul_zero, ← Finset.sum_filter]
    have h_filt_eq :
        (Finset.univ.filter (fun σ : ι → Bool => ∀ c ∈ W, σ c = true)).filter
          (fun σ => σ ∈ R) = R_W := by
      ext σ; simp only [Finset.mem_filter, Finset.mem_univ, true_and, hR_W]
    rw [h_filt_eq, ← Finset.sum_mul]
  have h_den_eq :
      gibbsPartitionZ (opEigenvalues sys.H0 sys.isSelfAdjoint_H0) β =
        (∑ σ ∈ R, Real.exp (-β * sys.syndromeEnergy σ)) * hilbertTrace sys.P0 := by
    rw [gibbsPartitionZ_eq_sum_syndromeProjector sys β]
    simp_rw [h_tr, mul_ite, mul_zero, ← Finset.sum_filter]
    have h_filt_R : (Finset.univ : Finset (ι → Bool)).filter (fun σ => σ ∈ R) = R := by
      ext σ; simp
    rw [h_filt_R, ← Finset.sum_mul]
  have h_prob :
      gibbsFailureProb sys.H0 sys.isSelfAdjoint_H0 β (positiveCheckWitnessProj sys W) =
        (gibbsPartitionZ (opEigenvalues sys.H0 sys.isSelfAdjoint_H0) β)⁻¹ *
          ∑ σ ∈ Finset.univ.filter (fun σ : ι → Bool => ∀ c ∈ W, σ c = true),
            Real.exp (-β * sys.syndromeEnergy σ) * hilbertTrace (sys.syndromeProjector σ) := by
    unfold gibbsFailureProb positiveCheckWitnessProj
    rw [Finset.mul_sum, hilbertTrace_sum]
    refine (Finset.sum_congr rfl fun σ _ =>
      hilbertTrace_gibbsDensityOp_mul_syndromeProjector sys β σ).trans ?_
    rw [← Finset.mul_sum]
  have hZ_pos : 0 < gibbsPartitionZ (opEigenvalues sys.H0 sys.isSelfAdjoint_H0) β :=
    gibbsPartitionZ_pos (opEigenvalues sys.H0 sys.isSelfAdjoint_H0) β
  have h_le :
      (∑ σ ∈ Finset.univ.filter (fun σ : ι → Bool => ∀ c ∈ W, σ c = true),
          Real.exp (-β * sys.syndromeEnergy σ) * hilbertTrace (sys.syndromeProjector σ)) ≤
        r * gibbsPartitionZ (opEigenvalues sys.H0 sys.isSelfAdjoint_H0) β := by
    rw [h_num_eq, h_den_eq, ← mul_assoc]
    exact mul_le_mul_of_nonneg_right h_coset_le hT0_nonneg
  rw [h_prob]
  calc (gibbsPartitionZ (opEigenvalues sys.H0 sys.isSelfAdjoint_H0) β)⁻¹ *
        (∑ σ ∈ Finset.univ.filter (fun σ : ι → Bool => ∀ c ∈ W, σ c = true),
          Real.exp (-β * sys.syndromeEnergy σ) * hilbertTrace (sys.syndromeProjector σ))
    _ ≤ (gibbsPartitionZ (opEigenvalues sys.H0 sys.isSelfAdjoint_H0) β)⁻¹ *
          (r * gibbsPartitionZ (opEigenvalues sys.H0 sys.isSelfAdjoint_H0) β) :=
      mul_le_mul_of_nonneg_left h_le (inv_nonneg.mpr (le_of_lt hZ_pos))
    _ = r * ((gibbsPartitionZ (opEigenvalues sys.H0 sys.isSelfAdjoint_H0) β)⁻¹ *
          gibbsPartitionZ (opEigenvalues sys.H0 sys.isSelfAdjoint_H0) β) := by ring
    _ = r := by rw [inv_mul_cancel₀ (ne_of_gt hZ_pos), mul_one]

/-- **Bare Static CSS Positive-Check Witness Peeling Bound
    (`gibbsFailureProb_bare_staticCSS_positiveCheckWitnessProj_le`)**:
    Combines `hilbertTrace_syndromeProjector_eq_P0_of_ne_zero`,
    `hilbertTrace_syndromeProjector_staticCSSPauliFlip_eq_P0`,
    `zero_mem_and_syndromeXor_closed_realizableZeroOutsideSyndromes`,
    `syndromeEnergy_syndromeXor_witness_clear_eq`, and
    `coset_syndromeEnergy_sum_le_of_syndromeXor_subspace` on $C_0(W) = \mathrm{realizableZeroOutsideSyndromes}\;D_{\mathrm{field}}\;W$
    to bound:
    $$\mathrm{gibbsFailureProb}\bigl(\mathrm{sys}.H_0,\; \mathrm{sys.isSelfAdjoint\_H0},\;
      \beta_{\mathrm{eff}},\; \mathrm{positiveCheckWitnessProj}\;\mathrm{sys}\;W\bigr)
      \le \exp\bigl(-\beta_{\mathrm{eff}} \cdot (W.\mathrm{card} : \mathbb{R})\bigr).$$ -/
theorem gibbsFailureProb_bare_staticCSS_positiveCheckWitnessProj_le
    {L q_code r_0 m_max w_0 L_star : ℕ} [NeZero L]
    (D_field : Box3D L → LocalCSSDescriptor q_code r_0 m_max)
    (h_valid : ValidDescriptorField D_field)
    (sys : IndexedCommutingProjectorHamiltonian 3 L
      (UniformSite3D L (CodeSlotConfig q_code))
      (StaticCSSCheckIdx L q_code m_max))
    (h_sys_checks : ∀ idx : StaticCSSCheckIdx L q_code m_max,
      sys.checkProj idx = staticCSSCheckProj D_field idx ∧
      sys.support idx = staticCSSCheckSupport D_field idx ∧
      sys.weight idx = 1)
    (h_geom : sys.IsGeometricallyLocal r_0 w_0)
    {C_rca β_eff : ℝ}
    (hC_rca : 0 ≤ C_rca)
    (hβ_eff : 0 ≤ β_eff)
    (h_tqo1 : SatisfiesTQO1 sys L_star)
    (h_tqo2 : SatisfiesSectorFilteredLinearTQO2 sys 1 L_star C_rca)
    (W : Finset (StaticCSSCheckIdx L q_code m_max)) :
    gibbsFailureProb sys.H0 sys.isSelfAdjoint_H0 β_eff (positiveCheckWitnessProj sys W) ≤
      Real.exp (-β_eff * (W.card : ℝ)) := by
  have h_wt : ∀ idx : StaticCSSCheckIdx L q_code m_max, sys.weight idx = 1 :=
    fun idx => (h_sys_checks idx).2.2
  refine gibbsFailureProb_bare_le_of_realizable_sum_le sys β_eff
    (Real.exp (-β_eff * (W.card : ℝ))) W
    (realizableSyndromes D_field)
    ((realizableSyndromes D_field).filter (fun σ => ∀ idx ∈ W, σ idx = true))
    (fun σ => Finset.mem_filter.trans and_comm)
    (fun σ hR => ?_)
    (fun σ hR => ?_)
    (realizable_witness_syndromeEnergy_sum_le D_field sys h_wt hβ_eff W)
  · rw [realizableSyndromes, Finset.mem_filter] at hR
    rcases hR.2 with ⟨a, b, rfl⟩
    exact hilbertTrace_syndromeProjector_staticCSSPauliFlip_eq_P0 D_field h_valid sys h_sys_checks a b
  · have h_zero : sys.syndromeProjector σ = 0 := by
      by_contra h_ne
      obtain ⟨⟨a, b, hab⟩, _⟩ :=
        hilbertTrace_syndromeProjector_eq_P0_of_ne_zero D_field h_valid sys h_sys_checks σ h_ne
      exact hR (Finset.mem_filter.mpr ⟨Finset.mem_univ σ, a, b, hab⟩)
    rw [h_zero]; unfold hilbertTrace; simp

end SpacetimeWorldlineKP
end
