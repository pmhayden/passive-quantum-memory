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

import Proofs.SpacetimeWorldlineKP.PauliDiagonalCollarScalarTraces

noncomputable section

open scoped Classical BigOperators InnerProduct ComplexConjugate
open Filter Topology Asymptotics ContinuousLinearMap KMSPinchedGibbs PerturbedThermalBarrier

set_option linter.constructorNameAsVariable false
set_option linter.unusedVariables false
set_option maxRecDepth 200000
set_option maxHeartbeats 1600000

namespace SpacetimeWorldlineKP

/-!
# Walsh–Hadamard Positive-Cone Closure and Pauli-Diagonal Collar Witness Peeling

Establishes the exact coset reduction to witness-clean realizable syndromes (`witnessCleanRealizableSyndromes`, `pauliDiagonal_witness_coset_reduction_le`). Proves multiplicative closure of functions with non-negative Boolean Walsh–Fourier coefficients (`HasNonnegBoolWalsh`, `local_collar_boltzmann_factor_walsh_nonneg`) to obtain the Pauli-diagonal collar-peeled Gibbs witness bound (`gibbsFailureProb_pauliDiagonal_collar_peeling_le`).

## References

* Part II, Section 3.3 (`subsec:walsh-coset-peeling`), Proposition 3.5 (`prop:witness-coset-reduction`)
* Part II, Section 3.3 (`subsec:walsh-coset-peeling`), Proposition 3.6 (`prop:walsh-coset-dominance`), Lemma 3.7 (`lem:peierls-bogoliubov`)
-/

/-- **Witness-Clean Realizable Syndrome Subgroup (`witnessCleanRealizableSyndromes`)** -/
def witnessCleanRealizableSyndromes {L q_code r_0 m_max : ℕ}
    (D_field : Box3D L → LocalCSSDescriptor q_code r_0 m_max)
    (W : Finset (StaticCSSCheckIdx L q_code m_max)) :
    Finset (StaticCSSCheckIdx L q_code m_max → Bool) :=
  (realizableSyndromes D_field).filter (fun τ => ∀ idx ∈ W, τ idx = false)

/-- **Spectator Pauli-Diagonal Energy Outside a Witness Set (`spectatorPauliDiagonalEnergy`)** -/
def spectatorPauliDiagonalEnergy {L q_code m_max : ℕ} [NeZero L]
    (sys : IndexedCommutingProjectorHamiltonian 3 L
      (UniformSite3D L (CodeSlotConfig q_code)) (StaticCSSCheckIdx L q_code m_max))
    (C_rca : ℝ) (R_pert : ℕ)
    (d_loc : ℕ → Finset (Box3D L) → (StaticCSSCheckIdx L q_code m_max → Bool) → ℝ)
    (W : Finset (StaticCSSCheckIdx L q_code m_max))
    (η : StaticCSSCheckIdx L q_code m_max → Bool) : ℝ :=
  (((Finset.univ \ W).filter (fun c => η c = true)).card : ℝ) +
    ∑ r ∈ Finset.Icc 1 (min R_pert L),
      ∑ A ∈ (boxCubes 3 L r).filter (fun A => Disjoint (rcaCollarChecks sys C_rca r A) W),
        d_loc r A η

/-- **Local Collar Boltzmann Factor (`localCollarBoltzmannFactor`)** -/
def localCollarBoltzmannFactor {L q_code m_max : ℕ} [NeZero L]
    (sys : IndexedCommutingProjectorHamiltonian 3 L
      (UniformSite3D L (CodeSlotConfig q_code)) (StaticCSSCheckIdx L q_code m_max))
    (C_rca δ β : ℝ)
    (d_loc : ℕ → Finset (Box3D L) → (StaticCSSCheckIdx L q_code m_max → Bool) → ℝ)
    (r : ℕ) (A : Finset (Box3D L))
    (η : StaticCSSCheckIdx L q_code m_max → Bool) : ℝ :=
  Real.exp (-δ * (((rcaCollarChecks sys C_rca r A).filter (fun c => η c = true)).card : ℝ) -
    β * d_loc r A η)

private def staticCSSCheckAnchor {L q_code m_max : ℕ} :
    StaticCSSCheckIdx L q_code m_max → Box3D L
  | Sum.inl (v, _) => v | Sum.inr (Sum.inl (v, _)) => v | Sum.inr (Sum.inr (v, _)) => v

private lemma staticCSSCheckAnchor_mem_support {L q_code r_0 m_max : ℕ}
    (D_field : Box3D L → LocalCSSDescriptor q_code r_0 m_max)
    (c : StaticCSSCheckIdx L q_code m_max) :
    staticCSSCheckAnchor c ∈ staticCSSCheckSupport D_field c := by
  rcases c with ⟨v, s⟩ | ⟨v, idx⟩ | ⟨v, idx⟩
  · exact Finset.mem_singleton_self v
  · exact _root_.mem_boxBall_self v r_0
  · exact _root_.mem_boxBall_self v r_0

lemma card_filter_mem_rcaCollarChecks_le
    {L q_code r_0 m_max w_0 R_pert : ℕ} [NeZero L]
    (D_field : Box3D L → LocalCSSDescriptor q_code r_0 m_max)
    (sys : IndexedCommutingProjectorHamiltonian 3 L
      (UniformSite3D L (CodeSlotConfig q_code)) (StaticCSSCheckIdx L q_code m_max))
    (h_sys_checks : ∀ idx : StaticCSSCheckIdx L q_code m_max,
      sys.checkProj idx = staticCSSCheckProj D_field idx ∧
      sys.support idx = staticCSSCheckSupport D_field idx ∧ sys.weight idx = 1)
    {C_rca : ℝ} (hC_rca : 0 ≤ C_rca) {r : ℕ} (hr : r ∈ Finset.Icc 1 (min R_pert L))
    (c : StaticCSSCheckIdx L q_code m_max) :
    ((boxCubes 3 L r).filter (fun A => c ∈ rcaCollarChecks sys C_rca r A)).card ≤
      (2 * (R_pert + 2 * linearExpansionRadius C_rca R_pert + r_0) + 1) ^ 3 * (w_0 + 1) := by
  have hr_R : r ≤ R_pert := le_trans (Finset.mem_Icc.mp hr).2 (Nat.min_le_left R_pert L)
  have h_sub : (boxCubes 3 L r).filter (fun A => c ∈ rcaCollarChecks sys C_rca r A) ⊆
      (boxCubes 3 L r).filter (fun A => staticCSSCheckAnchor c ∈ rcaCollarCube C_rca r A) := by
    intro A hA; rw [Finset.mem_filter] at hA ⊢
    refine ⟨hA.1, (Finset.mem_filter.mp hA.2).2 ?_⟩
    rw [(h_sys_checks c).2.1]; exact staticCSSCheckAnchor_mem_support D_field c
  have h_c1 : ((boxCubes 3 L r).filter (fun A => c ∈ rcaCollarChecks sys C_rca r A)).card ≤
      (2 * linearExpansionRadius C_rca r) ^ 3 :=
    le_trans (Finset.card_le_card h_sub)
      (card_filter_mem_enclosingBoxCube_le_pow r (linearExpansionRadius C_rca r) (staticCSSCheckAnchor c))
  have h_rad : linearExpansionRadius C_rca r ≤ linearExpansionRadius C_rca R_pert :=
    Nat.ceil_mono (mul_le_mul_of_nonneg_left (Nat.cast_le.mpr hr_R) hC_rca)
  have h_base : 2 * linearExpansionRadius C_rca r ≤
      2 * (R_pert + 2 * linearExpansionRadius C_rca R_pert + r_0) + 1 := by omega
  exact le_trans h_c1 (le_trans (Nat.pow_le_pow_left h_base 3)
    (Nat.le_mul_of_pos_right _ (Nat.succ_pos w_0)))

/-- **Witness Coset and Active-Collar Peeling Reduction (`pauliDiagonal_witness_coset_reduction_le`, Part II, Proposition 3.5 (`prop:witness-coset-reduction`))** -/
theorem pauliDiagonal_witness_coset_reduction_le
    {L q_code r_0 m_max w_0 R_pert : ℕ} [NeZero L]
    (D_field : Box3D L → LocalCSSDescriptor q_code r_0 m_max)
    (sys : IndexedCommutingProjectorHamiltonian 3 L
      (UniformSite3D L (CodeSlotConfig q_code)) (StaticCSSCheckIdx L q_code m_max))
    (h_sys_checks : ∀ idx : StaticCSSCheckIdx L q_code m_max,
      sys.checkProj idx = staticCSSCheckProj D_field idx ∧
      sys.support idx = staticCSSCheckSupport D_field idx ∧ sys.weight idx = 1)
    (h_geom : sys.IsGeometricallyLocal r_0 w_0)
    {C_rca J β : ℝ} (hC_rca : 0 ≤ C_rca) (hβ_pos : 0 < β) (hJ_nn : 0 ≤ J)
    (hJ_le : J ≤ collarWalshCouplingThreshold R_pert r_0 w_0 C_rca)
    (V : QuasiLocalPerturbation 3 L (UniformSite3D L (CodeSlotConfig q_code)))
    (e_loc : ℕ → Finset (Box3D L) → ℝ)
    (d_loc : ℕ → Finset (Box3D L) → (StaticCSSCheckIdx L q_code m_max → Bool) → ℝ)
    (h_scalar : IsLocalCollarScalarFamily D_field sys R_pert C_rca J V e_loc d_loc)
    (W : Finset (StaticCSSCheckIdx L q_code m_max)) :
    ((realizableSyndromes D_field).filter (fun σ => ∀ idx ∈ W, σ idx = true) = ∅ ∨
      ∃ σ₀ ∈ (realizableSyndromes D_field).filter (fun σ => ∀ idx ∈ W, σ idx = true),
        (∑ σ ∈ (realizableSyndromes D_field).filter (fun σ => ∀ idx ∈ W, σ idx = true),
            Real.exp (-β * pauliDiagonalSectorEnergy sys R_pert d_loc σ)) ≤
          Real.exp (-(7 / 8 : ℝ) * β * (W.card : ℝ)) *
            ∑ τ ∈ witnessCleanRealizableSyndromes D_field W,
              Real.exp (-β * spectatorPauliDiagonalEnergy sys C_rca R_pert d_loc W
                (syndromeXor σ₀ τ))) ∧
    (∑ τ ∈ witnessCleanRealizableSyndromes D_field W,
        Real.exp (-β * spectatorPauliDiagonalEnergy sys C_rca R_pert d_loc W τ)) ≤
      Real.exp ((1 / 8 : ℝ) * β * (W.card : ℝ)) *
        ∑ σ ∈ realizableSyndromes D_field,
          Real.exp (-β * pauliDiagonalSectorEnergy sys R_pert d_loc σ) := by
  let K_geom : ℕ :=
    (2 * (R_pert + 2 * linearExpansionRadius C_rca R_pert + r_0) + 1) ^ 3 * (w_0 + 1)
  have h_split : ∀ η : StaticCSSCheckIdx L q_code m_max → Bool,
      pauliDiagonalSectorEnergy sys R_pert d_loc η =
        spectatorPauliDiagonalEnergy sys C_rca R_pert d_loc W η +
          ((W.filter (fun c => η c = true)).card : ℝ) +
          ∑ r ∈ Finset.Icc 1 (min R_pert L),
            ∑ A ∈ (boxCubes 3 L r).filter (fun A => ¬Disjoint (rcaCollarChecks sys C_rca r A) W),
              d_loc r A η := by
    intro η
    unfold pauliDiagonalSectorEnergy spectatorPauliDiagonalEnergy
      IndexedCommutingProjectorHamiltonian.syndromeEnergy
    have h_wt_sum : (∑ c ∈ Finset.univ.filter (fun c => η c = true), sys.weight c) =
        ((Finset.univ.filter (fun c => η c = true)).card : ℝ) := by
      calc ∑ c ∈ Finset.univ.filter (fun c => η c = true), sys.weight c
        _ = ∑ _c ∈ Finset.univ.filter (fun c => η c = true), (1 : ℝ) :=
            Finset.sum_congr rfl fun c _ => (h_sys_checks c).2.2
        _ = ((Finset.univ.filter (fun c => η c = true)).card : ℝ) := by
            rw [Finset.sum_const, nsmul_eq_mul, mul_one]
    have h_card_split : (Finset.univ.filter (fun c => η c = true)).card =
        (W.filter (fun c => η c = true)).card +
          ((Finset.univ \ W).filter (fun c => η c = true)).card := by
      rw [← Finset.card_union_of_disjoint
        (Finset.disjoint_filter_filter disjoint_sdiff_self_right),
        ← Finset.filter_union, Finset.union_sdiff_of_subset (Finset.subset_univ W)]
    have h_cube_split : (∑ r ∈ Finset.Icc 1 (min R_pert L), ∑ A ∈ boxCubes 3 L r, d_loc r A η) =
        (∑ r ∈ Finset.Icc 1 (min R_pert L),
          ∑ A ∈ (boxCubes 3 L r).filter (fun A => Disjoint (rcaCollarChecks sys C_rca r A) W),
            d_loc r A η) +
        (∑ r ∈ Finset.Icc 1 (min R_pert L),
          ∑ A ∈ (boxCubes 3 L r).filter (fun A => ¬Disjoint (rcaCollarChecks sys C_rca r A) W),
            d_loc r A η) := by
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun r _ =>
        (Finset.sum_filter_add_sum_filter_not (boxCubes 3 L r) _ _).symm
    rw [h_wt_sum, h_card_split, Nat.cast_add, h_cube_split]; ring
  have h_act_abs : ∀ η : StaticCSSCheckIdx L q_code m_max → Bool,
      |∑ r ∈ Finset.Icc 1 (min R_pert L),
        ∑ A ∈ (boxCubes 3 L r).filter (fun A => ¬Disjoint (rcaCollarChecks sys C_rca r A) W),
          d_loc r A η| ≤ (1 / 8 : ℝ) * (W.card : ℝ) := by
    intro η
    have h_r_le : ∀ r ∈ Finset.Icc 1 (min R_pert L),
        |∑ A ∈ (boxCubes 3 L r).filter (fun A => ¬Disjoint (rcaCollarChecks sys C_rca r A) W),
          d_loc r A η| ≤ ((W.card * K_geom : ℕ) : ℝ) * (2 * J) := by
      intro r hr
      have h_sub : (boxCubes 3 L r).filter (fun A => ¬Disjoint (rcaCollarChecks sys C_rca r A) W) ⊆
          W.biUnion (fun c => (boxCubes 3 L r).filter (fun A => c ∈ rcaCollarChecks sys C_rca r A)) := by
        intro A hA
        rcases Finset.mem_filter.mp hA with ⟨hA_mem, h_nd⟩
        rcases Finset.not_disjoint_iff.mp h_nd with ⟨c, hc_col, hc_W⟩
        exact Finset.mem_biUnion.mpr ⟨c, hc_W, Finset.mem_filter.mpr ⟨hA_mem, hc_col⟩⟩
      have h_card :
          ((boxCubes 3 L r).filter (fun A => ¬Disjoint (rcaCollarChecks sys C_rca r A) W)).card ≤
            W.card * K_geom := by
        calc ((boxCubes 3 L r).filter (fun A => ¬Disjoint (rcaCollarChecks sys C_rca r A) W)).card
          _ ≤ (W.biUnion (fun c => (boxCubes 3 L r).filter (fun A => c ∈ rcaCollarChecks sys C_rca r A))).card :=
              Finset.card_le_card h_sub
          _ ≤ ∑ c ∈ W, ((boxCubes 3 L r).filter (fun A => c ∈ rcaCollarChecks sys C_rca r A)).card :=
              Finset.card_biUnion_le
          _ ≤ W.card • K_geom := Finset.sum_le_card_nsmul W _ K_geom fun c _ =>
              card_filter_mem_rcaCollarChecks_le D_field sys h_sys_checks hC_rca hr c
          _ = W.card * K_geom := smul_eq_mul _ _
      refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
      refine le_trans (Finset.sum_le_card_nsmul _ _ (2 * J) fun A hA =>
        (h_scalar r hr A (Finset.mem_filter.mp hA).1).1.2 η) ?_
      rw [nsmul_eq_mul]
      exact mul_le_mul_of_nonneg_right (by exact_mod_cast h_card) (by linarith)
    have h_sum_r := le_trans (Finset.abs_sum_le_sum_abs _ _)
      (Finset.sum_le_card_nsmul (Finset.Icc 1 (min R_pert L)) _
        (((W.card * K_geom : ℕ) : ℝ) * (2 * J)) h_r_le)
    rw [nsmul_eq_mul] at h_sum_r
    have h_card_Icc : ((Finset.Icc 1 (min R_pert L)).card : ℝ) ≤ (R_pert : ℝ) := by
      have h_nat : (Finset.Icc 1 (min R_pert L)).card ≤ R_pert := by
        rw [Nat.card_Icc]; have := Nat.min_le_left R_pert L; omega
      exact_mod_cast h_nat
    have h_first : |∑ r ∈ Finset.Icc 1 (min R_pert L),
        ∑ A ∈ (boxCubes 3 L r).filter (fun A => ¬Disjoint (rcaCollarChecks sys C_rca r A) W),
          d_loc r A η| ≤ 2 * rcaDiagonalCoercivityConstant 3 R_pert r_0 w_0 C_rca * J * (W.card : ℝ) := by
      refine le_trans h_sum_r (le_trans (mul_le_mul_of_nonneg_right h_card_Icc (by positivity)) ?_)
      unfold rcaDiagonalCoercivityConstant; dsimp [K_geom]; push_cast; linarith
    exact le_trans h_first (mul_le_mul_of_nonneg_right
      (two_mul_rcaDiagonalCoercivityConstant_mul_le_eighth_of_le_collarWalshCouplingThreshold hJ_nn hJ_le)
      (Nat.cast_nonneg W.card))
  have h_xor_R : ∀ {σ₁ σ₂ : StaticCSSCheckIdx L q_code m_max → Bool},
      σ₁ ∈ realizableSyndromes D_field → σ₂ ∈ realizableSyndromes D_field →
      syndromeXor σ₁ σ₂ ∈ realizableSyndromes D_field := by
    intro σ₁ σ₂ h₁ h₂
    rw [realizableSyndromes, Finset.mem_filter] at h₁ h₂ ⊢
    rcases h₁.2 with ⟨a₁, b₁, rfl⟩; rcases h₂.2 with ⟨a₂, b₂, rfl⟩
    exact ⟨Finset.mem_univ _, a₁ + a₂, b₁ + b₂, (staticCSSPauliFlip_add D_field a₁ a₂ b₁ b₂).symm⟩
  refine ⟨?_, ?_⟩
  · by_cases h_ne : ((realizableSyndromes D_field).filter (fun σ => ∀ idx ∈ W, σ idx = true)).Nonempty
    · right
      rcases h_ne with ⟨σ₀, hσ₀_mem⟩
      rcases Finset.mem_filter.mp hσ₀_mem with ⟨hσ₀_R, hσ₀_W⟩
      refine ⟨σ₀, hσ₀_mem, ?_⟩
      have h_bij :
          (∑ σ ∈ (realizableSyndromes D_field).filter (fun σ => ∀ idx ∈ W, σ idx = true),
            Real.exp (-β * pauliDiagonalSectorEnergy sys R_pert d_loc σ)) =
          ∑ τ ∈ witnessCleanRealizableSyndromes D_field W,
            Real.exp (-β * pauliDiagonalSectorEnergy sys R_pert d_loc (syndromeXor σ₀ τ)) := by
        symm
        refine Finset.sum_bij (fun τ _ => syndromeXor σ₀ τ) ?_ ?_ ?_ ?_
        · intro τ hτ
          rcases Finset.mem_filter.mp hτ with ⟨hτ_R, hτ_W⟩
          refine Finset.mem_filter.mpr ⟨h_xor_R hσ₀_R hτ_R, fun idx hidx => ?_⟩
          dsimp [syndromeXor]; rw [hσ₀_W idx hidx, hτ_W idx hidx]; rfl
        · intro τ₁ _ τ₂ _ h_eq; (try dsimp only at h_eq)
          rw [← syndromeXor_cancel_left σ₀ τ₁, ← syndromeXor_cancel_left σ₀ τ₂, h_eq]
        · intro σ hσ
          rcases Finset.mem_filter.mp hσ with ⟨hσ_R, hσ_W⟩
          refine ⟨syndromeXor σ₀ σ, Finset.mem_filter.mpr ⟨h_xor_R hσ₀_R hσ_R, fun idx hidx => ?_⟩,
            syndromeXor_cancel_left σ₀ σ⟩
          dsimp [syndromeXor]; rw [hσ₀_W idx hidx, hσ_W idx hidx]; rfl
        · intro _ _; rfl
      rw [h_bij, Finset.mul_sum]
      refine Finset.sum_le_sum fun τ hτ => ?_
      have hτ_W := (Finset.mem_filter.mp hτ).2
      have h_filt_W : W.filter (fun c => syndromeXor σ₀ τ c = true) = W :=
        Finset.filter_eq_self.mpr fun idx hidx => by
          dsimp [syndromeXor]; rw [hσ₀_W idx hidx, hτ_W idx hidx]; rfl
      have h_en := h_split (syndromeXor σ₀ τ)
      rw [h_filt_W] at h_en
      have h_lb := (abs_le.mp (h_act_abs (syndromeXor σ₀ τ))).1
      rw [← Real.exp_add]
      exact Real.exp_le_exp.mpr (by nlinarith)
    · left; exact Finset.not_nonempty_iff_eq_empty.mp h_ne
  · calc (∑ τ ∈ witnessCleanRealizableSyndromes D_field W,
          Real.exp (-β * spectatorPauliDiagonalEnergy sys C_rca R_pert d_loc W τ))
      _ ≤ ∑ τ ∈ witnessCleanRealizableSyndromes D_field W,
            Real.exp ((1 / 8 : ℝ) * β * (W.card : ℝ)) *
              Real.exp (-β * pauliDiagonalSectorEnergy sys R_pert d_loc τ) := by
          refine Finset.sum_le_sum fun τ hτ => ?_
          have hτ_W := (Finset.mem_filter.mp hτ).2
          have h_filt_W : W.filter (fun c => τ c = true) = ∅ :=
            Finset.filter_eq_empty_iff.mpr fun idx hidx => by rw [hτ_W idx hidx]; decide
          have h_en := h_split τ
          rw [h_filt_W, Finset.card_empty, Nat.cast_zero] at h_en
          have h_ub := (abs_le.mp (h_act_abs τ)).2
          rw [← Real.exp_add]
          exact Real.exp_le_exp.mpr (by nlinarith)
      _ = Real.exp ((1 / 8 : ℝ) * β * (W.card : ℝ)) *
            ∑ τ ∈ witnessCleanRealizableSyndromes D_field W,
              Real.exp (-β * pauliDiagonalSectorEnergy sys R_pert d_loc τ) := by
          rw [← Finset.mul_sum]
      _ ≤ Real.exp ((1 / 8 : ℝ) * β * (W.card : ℝ)) *
            ∑ σ ∈ realizableSyndromes D_field,
              Real.exp (-β * pauliDiagonalSectorEnergy sys R_pert d_loc σ) :=
          mul_le_mul_of_nonneg_left
            (Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
              fun _ _ _ => le_of_lt (Real.exp_pos _))
            (le_of_lt (Real.exp_pos _))

theorem card_rcaCollarChecks_add_one_le
    {L q_code r_0 m_max w_0 R_pert : ℕ} [NeZero L]
    (D_field : Box3D L → LocalCSSDescriptor q_code r_0 m_max)
    (sys : IndexedCommutingProjectorHamiltonian 3 L
      (UniformSite3D L (CodeSlotConfig q_code)) (StaticCSSCheckIdx L q_code m_max))
    (h_sys_checks : ∀ idx : StaticCSSCheckIdx L q_code m_max,
      sys.checkProj idx = staticCSSCheckProj D_field idx ∧
      sys.support idx = staticCSSCheckSupport D_field idx ∧ sys.weight idx = 1)
    (h_geom : sys.IsGeometricallyLocal r_0 w_0)
    {C_rca : ℝ} (hC_rca : 0 ≤ C_rca)
    {r : ℕ} (hr : r ∈ Finset.Icc 1 (min R_pert L))
    (A : Finset (Box3D L)) :
    (rcaCollarChecks sys C_rca r A).card ≤ collarMaxCheckCard R_pert r_0 w_0 C_rca := by
  have hL_pos : 0 < L := NeZero.pos L
  have hr_R : r ≤ R_pert := le_trans (Finset.mem_Icc.mp hr).2 (Nat.min_le_left R_pert L)
  let R := linearExpansionRadius C_rca r
  let B := rcaCollarCube C_rca r A
  let xB : Box3D L := fun i =>
    ⟨(anchorOfCube r A i).val - (R - r) / 2, Nat.sub_lt_of_lt (anchorOfCube r A i).isLt⟩
  have hB_eq : boxCube xB R = B := rfl
  let g : (Fin 3 → Fin R) → Box3D L := fun k i =>
    ⟨min (L - 1) ((xB i).val + (k i).val),
      Nat.lt_of_le_of_lt (Nat.min_le_left _ _) (Nat.sub_lt hL_pos zero_lt_one)⟩
  have hB_sub : B ⊆ Finset.univ.image g := by
    intro y hy
    rw [← hB_eq, mem_boxCube] at hy
    have hk_lt : ∀ i : Fin 3, (y i).val - (xB i).val < R := fun i => by
      have := (hy i).1; have := (hy i).2; omega
    let k : Fin 3 → Fin R := fun i => ⟨(y i).val - (xB i).val, hk_lt i⟩
    have hy_eq : g k = y := by
      funext i; apply Fin.ext; have := (hy i).1; have := (y i).isLt; dsimp [g, k]; omega
    exact Finset.mem_image.mpr ⟨k, Finset.mem_univ k, hy_eq⟩
  have hB_card : B.card ≤ R ^ 3 := by
    calc B.card
      _ ≤ (Finset.univ.image g).card := Finset.card_le_card hB_sub
      _ ≤ (Finset.univ : Finset (Fin 3 → Fin R)).card := Finset.card_image_le
      _ = R ^ 3 := by rw [Finset.card_univ, Fintype.card_fun, Fintype.card_fin, Fintype.card_fin]
  have h_col_sub : rcaCollarChecks sys C_rca r A ⊆
      B.biUnion (fun y => Finset.univ.filter (fun c => y ∈ sys.support c)) := by
    intro c hc
    have hc_supp : sys.support c ⊆ B := (Finset.mem_filter.mp hc).2
    have h_anc : staticCSSCheckAnchor c ∈ sys.support c := by
      rw [(h_sys_checks c).2.1]; exact staticCSSCheckAnchor_mem_support D_field c
    exact Finset.mem_biUnion.mpr ⟨staticCSSCheckAnchor c, hc_supp h_anc,
      Finset.mem_filter.mpr ⟨Finset.mem_univ c, h_anc⟩⟩
  have h_card_col : (rcaCollarChecks sys C_rca r A).card ≤ B.card * w_0 := by
    calc (rcaCollarChecks sys C_rca r A).card
      _ ≤ (B.biUnion (fun y => Finset.univ.filter (fun c => y ∈ sys.support c))).card :=
          Finset.card_le_card h_col_sub
      _ ≤ ∑ y ∈ B, (Finset.univ.filter (fun c => y ∈ sys.support c)).card := Finset.card_biUnion_le
      _ ≤ B.card • w_0 := Finset.sum_le_card_nsmul B _ w_0 (fun y _ => h_geom.2 y)
      _ = B.card * w_0 := smul_eq_mul _ _
  have h_rad : R ≤ linearExpansionRadius C_rca R_pert :=
    Nat.ceil_mono (mul_le_mul_of_nonneg_left (Nat.cast_le.mpr hr_R) hC_rca)
  have h_base : R ≤ 2 * (R_pert + 2 * linearExpansionRadius C_rca R_pert + r_0) + 1 := by omega
  have h_mul : B.card * w_0 ≤
      (2 * (R_pert + 2 * linearExpansionRadius C_rca R_pert + r_0) + 1) ^ 3 * (w_0 + 1) :=
    Nat.mul_le_mul (le_trans hB_card (Nat.pow_le_pow_left h_base 3)) (Nat.le_succ w_0)
  unfold collarMaxCheckCard
  exact le_trans h_card_col (le_trans h_mul (Nat.le_succ _))

/-- **Non-Negativity of Local Collar Boltzmann Factor Walsh–Hadamard Coefficients
    (`local_collar_boltzmann_factor_walsh_nonneg`, Part II, Proposition 3.6 (`prop:walsh-coset-dominance`))** -/
theorem local_collar_boltzmann_factor_walsh_nonneg
    {L q_code r_0 m_max w_0 R_pert : ℕ} [NeZero L]
    (D_field : Box3D L → LocalCSSDescriptor q_code r_0 m_max)
    (sys : IndexedCommutingProjectorHamiltonian 3 L
      (UniformSite3D L (CodeSlotConfig q_code)) (StaticCSSCheckIdx L q_code m_max))
    (h_sys_checks : ∀ idx : StaticCSSCheckIdx L q_code m_max,
      sys.checkProj idx = staticCSSCheckProj D_field idx ∧
      sys.support idx = staticCSSCheckSupport D_field idx ∧ sys.weight idx = 1)
    (h_geom : sys.IsGeometricallyLocal r_0 w_0)
    {C_rca β_c J β : ℝ} (hC_rca : 0 ≤ C_rca) (hβc_ge : 16 ≤ β_c) (hβ : β > β_c)
    (hJ_nn : 0 ≤ J) (hJ_le : J ≤ collarWalshCouplingThreshold R_pert r_0 w_0 C_rca)
    (V : QuasiLocalPerturbation 3 L (UniformSite3D L (CodeSlotConfig q_code)))
    (e_loc : ℕ → Finset (Box3D L) → ℝ)
    (d_loc : ℕ → Finset (Box3D L) → (StaticCSSCheckIdx L q_code m_max → Bool) → ℝ)
    (h_scalar : IsLocalCollarScalarFamily D_field sys R_pert C_rca J V e_loc d_loc)
    {r : ℕ} (hr : r ∈ Finset.Icc 1 (min R_pert L))
    {A : Finset (Box3D L)} (hA : A ∈ boxCubes 3 L r)
    (S : Finset (StaticCSSCheckIdx L q_code m_max)) :
    let δ := β / (8 * (rcaDiagonalCoercivityConstant 3 R_pert r_0 w_0 C_rca + 1))
    0 ≤ ∑ η : StaticCSSCheckIdx L q_code m_max → Bool,
      ((-1 : ℝ) ^ ((S.filter (fun c => η c = true)).card)) *
        localCollarBoltzmannFactor sys C_rca δ β d_loc r A η := by
  intro δ
  let ι := StaticCSSCheckIdx L q_code m_max
  let K := rcaCollarChecks sys C_rca r A
  let g (η : ι → Bool) : ℝ := localCollarBoltzmannFactor sys C_rca δ β d_loc r A η
  let χ (η : ι → Bool) : ℝ := (-1 : ℝ) ^ ((S.filter (fun c => η c = true)).card)
  have hχ_prod : ∀ η : ι → Bool, χ η = ∏ c ∈ S, if η c = true then (-1 : ℝ) else 1 := fun η => by
    dsimp [χ]; rw [Finset.prod_ite, Finset.prod_const, Finset.prod_const_one, mul_one]
  by_cases hSK : S ⊆ K
  · let indS (T : Finset ι) : ι → Bool := fun c => decide (c ∈ T)
    let termK (T : Finset ι) : ℝ :=
      (-1 : ℝ) ^ ((S ∩ T).card) * Real.exp (-δ * (T.card : ℝ) - β * d_loc r A (indS T))
    have h_factor_out :
        (∑ η : ι → Bool, χ η * g η) =
          (((Finset.univ \ K).powerset.card : ℝ)) * ∑ T ∈ K.powerset, termK T := by
      let P := K.powerset ×ˢ (Finset.univ \ K).powerset
      have h_bij : (∑ η : ι → Bool, χ η * g η) = ∑ p ∈ P, termK p.1 := by
        symm
        refine Finset.sum_bij (fun p _ => indS (p.1 ∪ p.2))
          (fun _ _ => Finset.mem_univ _) ?_ ?_ ?_
        · intro p₁ hp₁ p₂ hp₂ h_eq
          rcases Finset.mem_product.mp hp₁ with ⟨hT₁, hU₁⟩
          rcases Finset.mem_product.mp hp₂ with ⟨hT₂, hU₂⟩
          rw [Finset.mem_powerset] at hT₁ hU₁ hT₂ hU₂
          have h_mem : ∀ c : ι, c ∈ p₁.1 ∪ p₁.2 ↔ c ∈ p₂.1 ∪ p₂.2 :=
            fun c => decide_eq_decide.mp (congr_fun h_eq c)
          ext c
          · constructor <;> intro hc
            · exact (Finset.mem_union.mp ((h_mem c).mp (Finset.mem_union_left _ hc))).resolve_right
                fun h2 => (Finset.mem_sdiff.mp (hU₂ h2)).2 (hT₁ hc)
            · exact (Finset.mem_union.mp ((h_mem c).mpr (Finset.mem_union_left _ hc))).resolve_right
                fun h1 => (Finset.mem_sdiff.mp (hU₁ h1)).2 (hT₂ hc)
          · constructor <;> intro hc
            · exact (Finset.mem_union.mp ((h_mem c).mp (Finset.mem_union_right _ hc))).resolve_left
                fun h2 => (Finset.mem_sdiff.mp (hU₁ hc)).2 (hT₂ h2)
            · exact (Finset.mem_union.mp ((h_mem c).mpr (Finset.mem_union_right _ hc))).resolve_left
                fun h1 => (Finset.mem_sdiff.mp (hU₂ hc)).2 (hT₁ h1)
        · intro η _
          refine ⟨(K.filter (fun c => η c = true), (Finset.univ \ K).filter (fun c => η c = true)),
            Finset.mem_product.mpr ⟨Finset.mem_powerset.mpr (Finset.filter_subset _ _),
              Finset.mem_powerset.mpr (Finset.filter_subset _ _)⟩, ?_⟩
          ext c; dsimp [indS]
          by_cases hcK : c ∈ K <;> cases hη : η c <;> simp [hcK, hη]
        · intro p hp
          rcases Finset.mem_product.mp hp with ⟨hT, hU⟩
          rw [Finset.mem_powerset] at hT hU
          have h_K_agree : ∀ c ∈ K, indS (p.1 ∪ p.2) c = indS p.1 c := fun c hcK => by
            have hcU : c ∉ p.2 := fun h => (Finset.mem_sdiff.mp (hU h)).2 hcK
            simp [indS, hcU]
          have h_filt_K : K.filter (fun c => indS (p.1 ∪ p.2) c = true) = p.1 := by
            ext c; simp only [Finset.mem_filter]
            constructor
            · intro h; rw [h_K_agree c h.1] at h; simpa [indS] using h.2
            · intro hc1; exact ⟨hT hc1, by rw [h_K_agree c (hT hc1)]; simpa [indS] using hc1⟩
          have h_filt_S : S.filter (fun c => indS (p.1 ∪ p.2) c = true) = S ∩ p.1 := by
            ext c; simp only [Finset.mem_filter, Finset.mem_inter]
            constructor
            · intro h; rw [h_K_agree c (hSK h.1)] at h; exact ⟨h.1, by simpa [indS] using h.2⟩
            · intro h; rw [h_K_agree c (hSK h.1)]; exact ⟨h.1, by simpa [indS] using h.2⟩
          have hd_eq : d_loc r A (indS (p.1 ∪ p.2)) = d_loc r A (indS p.1) :=
            (h_scalar r hr A hA).2.2 _ _ h_K_agree
          dsimp [termK, χ, g, localCollarBoltzmannFactor]
          rw [h_filt_S, h_filt_K, hd_eq]
      rw [h_bij, Finset.sum_product]
      simp_rw [Finset.sum_const, nsmul_eq_mul, ← Finset.mul_sum]
    rw [h_factor_out]
    refine mul_nonneg (Nat.cast_nonneg _) ?_
    let Δ := rcaDiagonalCoercivityConstant 3 R_pert r_0 w_0 C_rca
    let N_max := collarMaxCheckCard R_pert r_0 w_0 C_rca
    let E := Real.exp (-8 * (Δ + 1) * ((N_max : ℝ) + 1) * (16 + (Δ + 1)))
    have hΔ_nn : 0 ≤ Δ := by dsimp [Δ, rcaDiagonalCoercivityConstant]; positivity
    have hβ_pos : 0 < β := by linarith
    have hδ_pos : 0 < δ := by dsimp [δ]; positivity
    have hK_le : K.card ≤ N_max :=
      card_rcaCollarChecks_add_one_le D_field sys h_sys_checks h_geom hC_rca hr A
    have hK_real_le : (K.card : ℝ) ≤ (N_max : ℝ) := by exact_mod_cast hK_le
    have hN_nn : (0 : ℝ) ≤ (N_max : ℝ) := Nat.cast_nonneg N_max
    have hΔN_nn : 0 ≤ Δ * (N_max : ℝ) := mul_nonneg hΔ_nn hN_nn
    have h_δ_eq : δ * (8 * (Δ + 1)) = β := div_mul_cancel₀ β (by dsimp [Δ]; positivity)
    have hJ_E : J ≤ E :=
      (two_mul_rcaDiagonalCoercivityConstant_mul_J_le_exp_collarMaxCheckCard_of_le_collarWalshCouplingThreshold
        hJ_nn hJ_le).1
    have h2_le_exp1 : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp 1]
    have h_card_powerset : (K.powerset.card : ℝ) ≤ Real.exp (N_max : ℝ) := by
      rw [Finset.card_powerset, Nat.cast_pow, Nat.cast_ofNat]
      calc (2 : ℝ) ^ K.card
        _ ≤ (2 : ℝ) ^ N_max := pow_le_pow_right₀ (by norm_num) hK_le
        _ ≤ (Real.exp 1) ^ N_max := pow_le_pow_left₀ (by norm_num) h2_le_exp1 N_max
        _ = Real.exp ((N_max : ℝ) * 1) := (Real.exp_nat_mul 1 N_max).symm
        _ = Real.exp (N_max : ℝ) := by ring_nf
    rcases le_total (16 * (Δ + 1) * ((N_max : ℝ) + 1)) β with hβ_large | hβ_mod
    · have hE_le_32 : E * (32 * (Δ + 1)) ≤ 1 := by
        have h_exp32 : E ≤ Real.exp (-(32 * (Δ + 1))) := by
          apply Real.exp_le_exp.mpr
          have : 0 ≤ (Δ + 1) * ((N_max : ℝ) + 1) * (Δ + 1) := by positivity
          linarith
        have h32 : 32 * (Δ + 1) ≤ Real.exp (32 * (Δ + 1)) := by
          linarith [Real.add_one_le_exp (32 * (Δ + 1))]
        calc E * (32 * (Δ + 1))
          _ ≤ Real.exp (-(32 * (Δ + 1))) * Real.exp (32 * (Δ + 1)) :=
              mul_le_mul h_exp32 h32 (by positivity) (le_of_lt (Real.exp_pos _))
          _ = 1 := by rw [← Real.exp_add, neg_add_cancel, Real.exp_zero]
      have h2βJ_le : 2 * β * J ≤ δ / 2 := by
        have hJ_32 : J * (32 * (Δ + 1)) ≤ 1 :=
          le_trans (mul_le_mul_of_nonneg_right hJ_E (by positivity)) hE_le_32
        nlinarith [h_δ_eq]
      have hN_le_δ2 : (N_max : ℝ) + 1 ≤ δ / 2 := by
        nlinarith [h_δ_eq]
      have h_empty_mem : (∅ : Finset ι) ∈ K.powerset :=
        Finset.mem_powerset.mpr (Finset.empty_subset K)
      rw [← Finset.add_sum_erase K.powerset termK h_empty_mem]
      have h_ind_empty : indS (∅ : Finset ι) = (fun _ => false) := by ext c; rfl
      have h_term_empty : termK ∅ = 1 := by
        dsimp [termK]
        rw [Finset.inter_empty, Finset.card_empty, pow_zero, Nat.cast_zero, mul_zero,
          h_ind_empty, (h_scalar r hr A hA).2.1 (fun _ => false) (fun _ _ => rfl),
          mul_zero, sub_zero, Real.exp_zero, mul_one]
      have h_erase_term : ∀ T ∈ K.powerset.erase ∅,
          -Real.exp (-((N_max : ℝ) + 1)) ≤ termK T := by
        intro T hT
        have hT_pos : (1 : ℝ) ≤ (T.card : ℝ) := by
          exact_mod_cast Finset.card_pos.mpr
            (Finset.nonempty_iff_ne_empty.mpr (Finset.ne_of_mem_erase hT))
        have hd_abs := (abs_le.mp ((h_scalar r hr A hA).1.2 (indS T))).1
        have h_exp_le : Real.exp (-δ * (T.card : ℝ) - β * d_loc r A (indS T)) ≤
            Real.exp (-((N_max : ℝ) + 1)) := by
          apply Real.exp_le_exp.mpr; nlinarith
        have h_sign : -1 ≤ (-1 : ℝ) ^ ((S ∩ T).card) :=
          neg_le_of_abs_le (by rw [abs_pow, abs_neg, abs_one, one_pow])
        dsimp [termK]
        nlinarith [Real.exp_pos (-δ * (T.card : ℝ) - β * d_loc r A (indS T))]
      have h_sum_erase :
          -(((K.powerset.erase ∅).card : ℝ) * Real.exp (-((N_max : ℝ) + 1))) ≤
            ∑ T ∈ K.powerset.erase ∅, termK T := by
        calc -(((K.powerset.erase ∅).card : ℝ) * Real.exp (-((N_max : ℝ) + 1)))
          _ = ∑ _T ∈ K.powerset.erase ∅, (-Real.exp (-((N_max : ℝ) + 1))) := by
              rw [Finset.sum_const, nsmul_eq_mul]; ring
          _ ≤ ∑ T ∈ K.powerset.erase ∅, termK T := Finset.sum_le_sum h_erase_term
      have h_card_erase : ((K.powerset.erase ∅).card : ℝ) ≤ Real.exp ((N_max : ℝ) + 1) :=
        le_trans (by exact_mod_cast Finset.card_erase_le)
          (le_trans h_card_powerset (Real.exp_le_exp.mpr (by linarith)))
      have h_prod_one : ((K.powerset.erase ∅).card : ℝ) * Real.exp (-((N_max : ℝ) + 1)) ≤ 1 := by
        calc ((K.powerset.erase ∅).card : ℝ) * Real.exp (-((N_max : ℝ) + 1))
          _ ≤ Real.exp ((N_max : ℝ) + 1) * Real.exp (-((N_max : ℝ) + 1)) :=
              mul_le_mul_of_nonneg_right h_card_erase (le_of_lt (Real.exp_pos _))
          _ = 1 := by rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]
      linarith
    · let mainK (T : Finset ι) : ℝ := (-1 : ℝ) ^ ((S ∩ T).card) * Real.exp (-δ * (T.card : ℝ))
      let errK (T : Finset ι) : ℝ := mainK T * (Real.exp (-β * d_loc r A (indS T)) - 1)
      have h_split_T : (∑ T ∈ K.powerset, termK T) =
          (∑ T ∈ K.powerset, mainK T) + (∑ T ∈ K.powerset, errK T) := by
        rw [← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun T _ => ?_
        dsimp [termK, mainK, errK]; rw [sub_eq_add_neg, Real.exp_add]; ring
      have h_main_lb : Real.exp (-((N_max : ℝ) * (Δ + 1))) ≤ ∑ T ∈ K.powerset, mainK T := by
        have h_prod_id : (∑ T ∈ K.powerset, mainK T) =
            ∏ c ∈ K, ((if c ∈ S then (-1 : ℝ) else 1) * Real.exp (-δ) + 1) := by
          rw [Finset.prod_add]; refine Finset.sum_congr rfl fun T _ => ?_
          rw [Finset.prod_const_one, mul_one, Finset.prod_mul_distrib, Finset.prod_const]
          have h_ite : (∏ x ∈ T, if x ∈ S then (-1 : ℝ) else 1) =
              (-1 : ℝ) ^ (S ∩ T).card := by
            have h1 : (∏ x ∈ T, if x ∈ S then (-1 : ℝ) else 1) =
                ∏ x ∈ T, if decide (x ∈ S) = true then (-1 : ℝ) else 1 :=
              Finset.prod_congr rfl fun x _ => by simp
            rw [h1, Finset.prod_ite, Finset.prod_const, Finset.prod_const_one, mul_one]
            congr 2
            ext x; simp [Finset.mem_inter, and_comm]
          have h_exp_pow : (Real.exp (-δ)) ^ T.card = Real.exp (-δ * (T.card : ℝ)) := by
            rw [← Real.exp_nat_mul]; congr 1; ring
          dsimp [mainK]
          rw [h_ite, h_exp_pow]
        let u := 2 / (Δ + 1)
        have hu_le_δ : u ≤ δ := by
          dsimp [u, δ]; rw [div_le_div_iff₀ (by positivity) (by positivity)]; nlinarith
        have h_u_exp : (u + 1) * Real.exp (-δ) ≤ 1 := by
          calc (u + 1) * Real.exp (-δ)
            _ ≤ Real.exp u * Real.exp (-δ) :=
                mul_le_mul_of_nonneg_right (Real.add_one_le_exp u) (le_of_lt (Real.exp_pos _))
            _ ≤ Real.exp δ * Real.exp (-δ) :=
                mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr hu_le_δ) (le_of_lt (Real.exp_pos _))
            _ = 1 := by rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]
        have h_u_id : (Δ + 1) * (u + 1) = Δ + 3 := by dsimp [u]; field_simp; ring
        have h_lhs_ge2 : 2 ≤ (Δ + 3) * (1 - Real.exp (-δ)) := by
          have h_mul := mul_le_mul_of_nonneg_left h_u_exp (by positivity : 0 ≤ Δ + 1)
          nlinarith [h_u_id]
        have h_rhs_le2 : (Δ + 3) * Real.exp (-(Δ + 1)) ≤ 2 := by
          calc (Δ + 3) * Real.exp (-(Δ + 1))
            _ ≤ (2 * (Δ + 1 + 1)) * Real.exp (-(Δ + 1)) :=
                mul_le_mul_of_nonneg_right (by linarith) (le_of_lt (Real.exp_pos _))
            _ ≤ (2 * Real.exp (Δ + 1)) * Real.exp (-(Δ + 1)) :=
                mul_le_mul_of_nonneg_right
                  (mul_le_mul_of_nonneg_left (Real.add_one_le_exp (Δ + 1)) (by norm_num))
                  (le_of_lt (Real.exp_pos _))
            _ = 2 := by rw [mul_assoc, ← Real.exp_add, add_neg_cancel, Real.exp_zero, mul_one]
        have h_base_lb : Real.exp (-(Δ + 1)) ≤ 1 - Real.exp (-δ) := by nlinarith
        have h_prod_ge : (∏ _c ∈ K, Real.exp (-(Δ + 1))) ≤
            ∏ c ∈ K, ((if c ∈ S then (-1 : ℝ) else 1) * Real.exp (-δ) + 1) := by
          refine Finset.prod_le_prod₀ (fun _ _ => le_of_lt (Real.exp_pos _)) fun c _ => ?_
          refine le_trans h_base_lb ?_; have := Real.exp_pos (-δ); split_ifs <;> linarith
        rw [h_prod_id]; refine le_trans ?_ h_prod_ge
        rw [Finset.prod_const, ← Real.exp_nat_mul]
        exact Real.exp_le_exp.mpr (by nlinarith)
      let M := Real.exp (-96 * (Δ + 1) * ((N_max : ℝ) + 1))
      have hM_nn : 0 ≤ M := le_of_lt (Real.exp_pos _)
      have hM_half : M ≤ 1 / 2 := by
        have h_le2 : M ≤ Real.exp (-2) := Real.exp_le_exp.mpr (by linarith)
        have h2_exp : (2 : ℝ) ≤ Real.exp 2 := by linarith [Real.add_one_le_exp 2]
        have h_prod : M * 2 ≤ 1 := by
          calc M * 2
            _ ≤ Real.exp (-2) * Real.exp 2 := mul_le_mul h_le2 h2_exp (by norm_num) (le_of_lt (Real.exp_pos _))
            _ = 1 := by rw [← Real.exp_add, neg_add_cancel, Real.exp_zero]
        linarith
      have h2βJ_le_M : 2 * β * J ≤ M := by
        have h2β_exp : 2 * β ≤ Real.exp (32 * (Δ + 1) * ((N_max : ℝ) + 1)) := by
          linarith [Real.add_one_le_exp (32 * (Δ + 1) * ((N_max : ℝ) + 1))]
        have h_extra_nn : 0 ≤ (Δ + 1) * ((N_max : ℝ) + 1) * (Δ + 1) := by positivity
        calc 2 * β * J
          _ ≤ Real.exp (32 * (Δ + 1) * ((N_max : ℝ) + 1)) * E :=
              mul_le_mul h2β_exp hJ_E hJ_nn (le_of_lt (Real.exp_pos _))
          _ = Real.exp (32 * (Δ + 1) * ((N_max : ℝ) + 1) +
                (-8 * (Δ + 1) * ((N_max : ℝ) + 1) * (16 + (Δ + 1)))) := (Real.exp_add _ _).symm
          _ ≤ M := Real.exp_le_exp.mpr (by linarith)
      have h_err_term : ∀ T ∈ K.powerset, -(2 * M) ≤ errK T := by
        intro T _
        let x := -β * d_loc r A (indS T)
        have hx_abs : |x| ≤ M := by
          have hd := (h_scalar r hr A hA).1.2 (indS T)
          have : |x| ≤ 2 * β * J := by dsimp [x]; rw [abs_mul, abs_neg, abs_of_pos hβ_pos]; nlinarith
          exact le_trans this h2βJ_le_M
        rcases abs_le.mp hx_abs with ⟨hx_lb, hx_ub⟩
        have hexp_lb : -(2 * M) ≤ Real.exp x - 1 := by linarith [Real.add_one_le_exp x]
        have hexp_ub : Real.exp x - 1 ≤ 2 * M := by
          have h1 : (1 - M) * Real.exp x ≤ 1 := by
            calc (1 - M) * Real.exp x
              _ ≤ (-x + 1) * Real.exp x := mul_le_mul_of_nonneg_right (by linarith) (le_of_lt (Real.exp_pos _))
              _ ≤ Real.exp (-x) * Real.exp x :=
                  mul_le_mul_of_nonneg_right (Real.add_one_le_exp (-x)) (le_of_lt (Real.exp_pos _))
              _ = 1 := by rw [← Real.exp_add, neg_add_cancel, Real.exp_zero]
          have h2 : 1 ≤ (1 - M) * (1 + 2 * M) := by nlinarith
          nlinarith
        have h_abs_exp : |Real.exp x - 1| ≤ 2 * M := abs_le.mpr ⟨hexp_lb, hexp_ub⟩
        have h_abs_main : |mainK T| ≤ 1 := by
          dsimp [mainK]
          rw [abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul,
            abs_of_pos (Real.exp_pos _), Real.exp_le_one_iff]
          have : (0 : ℝ) ≤ (T.card : ℝ) := Nat.cast_nonneg T.card
          nlinarith
        have h_abs_err : |errK T| ≤ 2 * M := by
          dsimp [errK]; rw [abs_mul]
          calc |mainK T| * |Real.exp x - 1|
            _ ≤ 1 * (2 * M) := mul_le_mul h_abs_main h_abs_exp (abs_nonneg _) (by norm_num)
            _ = 2 * M := one_mul _
        exact (abs_le.mp h_abs_err).1
      have h_sum_err : -((K.powerset.card : ℝ) * (2 * M)) ≤ ∑ T ∈ K.powerset, errK T := by
        calc -((K.powerset.card : ℝ) * (2 * M))
          _ = ∑ _T ∈ K.powerset, -(2 * M) := by rw [Finset.sum_const, nsmul_eq_mul]; ring
          _ ≤ ∑ T ∈ K.powerset, errK T := Finset.sum_le_sum h_err_term
      have h_err_bound : (K.powerset.card : ℝ) * (2 * M) ≤ Real.exp (-((N_max : ℝ) * (Δ + 1))) := by
        calc (K.powerset.card : ℝ) * (2 * M)
          _ ≤ Real.exp (N_max : ℝ) * (Real.exp 1 * M) :=
              mul_le_mul h_card_powerset (mul_le_mul_of_nonneg_right h2_le_exp1 hM_nn)
                (by positivity) (le_of_lt (Real.exp_pos _))
          _ = Real.exp ((N_max : ℝ) + 1 + (-96 * (Δ + 1) * ((N_max : ℝ) + 1))) := by
              dsimp [M]; rw [← mul_assoc, ← Real.exp_add, ← Real.exp_add]
          _ ≤ Real.exp (-((N_max : ℝ) * (Δ + 1))) :=
              Real.exp_le_exp.mpr (by linarith)
      rw [h_split_T]; linarith
  · rcases Finset.not_subset.mp hSK with ⟨c₀, hc₀_S, hc₀_K⟩
    let flip (η : ι → Bool) : ι → Bool := Function.update η c₀ (!η c₀)
    have h_inv : ∀ η : ι → Bool, flip (flip η) = η := fun η => by
      ext c; by_cases h : c = c₀ <;> simp [flip, h]
    have h_neg : ∀ η : ι → Bool, χ (flip η) * g (flip η) = -(χ η * g η) := fun η => by
      have h_agree : ∀ c ∈ K, flip η c = η c := fun c hc => by
        simp [flip, ne_of_mem_of_not_mem hc hc₀_K]
      have h_filt : K.filter (fun c => flip η c = true) = K.filter (fun c => η c = true) :=
        Finset.filter_congr fun c hc => by rw [h_agree c hc]
      have hd_eq : d_loc r A (flip η) = d_loc r A η :=
        (h_scalar r hr A hA).2.2 _ _ h_agree
      have hg_eq : g (flip η) = g η := by
        dsimp [g, localCollarBoltzmannFactor]; rw [h_filt, hd_eq]
      have hχ_neg : χ (flip η) = -χ η := by
        rw [hχ_prod (flip η), hχ_prod η,
          ← Finset.mul_prod_erase S _ hc₀_S,
          ← Finset.mul_prod_erase S (fun c => if η c = true then (-1 : ℝ) else 1) hc₀_S]
        have h_c0 : (if flip η c₀ = true then (-1 : ℝ) else 1) =
            -(if η c₀ = true then (-1 : ℝ) else 1) := by
          simp [flip]; cases η c₀ <;> norm_num
        have h_erase :
            (∏ c ∈ S.erase c₀, if flip η c = true then (-1 : ℝ) else 1) =
              ∏ c ∈ S.erase c₀, if η c = true then (-1 : ℝ) else 1 :=
          Finset.prod_congr rfl fun c hc => by simp [flip, Finset.ne_of_mem_erase hc]
        rw [h_c0, h_erase, neg_mul]
      rw [hχ_neg, hg_eq, neg_mul]
    have h_sum_neg : (∑ η : ι → Bool, χ η * g η) = -(∑ η : ι → Bool, χ η * g η) := by
      calc (∑ η : ι → Bool, χ η * g η)
        _ = ∑ η : ι → Bool, χ (flip η) * g (flip η) := by
            symm
            refine Finset.sum_bij (fun η _ => flip η)
              (fun _ _ => Finset.mem_univ _)
              (fun a _ b _ h => by (try dsimp only at h); rw [← h_inv a, ← h_inv b, h])
              (fun b _ => ⟨flip b, Finset.mem_univ _, h_inv b⟩)
              (fun _ _ => rfl)
        _ = ∑ η : ι → Bool, -(χ η * g η) := Finset.sum_congr rfl fun η _ => h_neg η
        _ = -(∑ η : ι → Bool, χ η * g η) := by rw [Finset.sum_neg_distrib]
    linarith

/-- **Reduction of Pauli-Diagonal Gibbs Failure Probability to Classical Realizable-Syndrome Ratio** -/
theorem gibbsFailureProb_pauliDiagonal_le_of_realizable_sectorEnergy_sum
    {D L : ℕ} {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    [∀ x, Nonempty (Site x)] {ι : Type} [Fintype ι] [DecidableEq ι]
    (H_diag : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site)
    (hH_diag : IsSelfAdjoint H_diag) (β : ℝ)
    (P : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site)
    (R R_W : Finset (ι → Bool)) (E_diag : (ι → Bool) → ℝ) {K c : ℝ} (hK_nn : 0 ≤ K)
    (h_num :
      hilbertTrace (gibbsBoltzmannOp (opEigenbasis H_diag hH_diag)
        (opEigenvalues H_diag hH_diag) β * P) =
        K * ∑ σ ∈ R_W, Real.exp (-β * E_diag σ))
    (h_den :
      gibbsPartitionZ (opEigenvalues H_diag hH_diag) β =
        K * ∑ σ ∈ R, Real.exp (-β * E_diag σ))
    (h_sum_le :
      (∑ σ ∈ R_W, Real.exp (-β * E_diag σ)) ≤
        c * ∑ σ ∈ R, Real.exp (-β * E_diag σ)) :
    gibbsFailureProb H_diag hH_diag β P ≤ c := by
  have hZ_pos : 0 < gibbsPartitionZ (opEigenvalues H_diag hH_diag) β :=
    gibbsPartitionZ_pos (opEigenvalues H_diag hH_diag) β
  have h_eq :
      gibbsFailureProb H_diag hH_diag β P =
        hilbertTrace (gibbsBoltzmannOp (opEigenbasis H_diag hH_diag)
          (opEigenvalues H_diag hH_diag) β * P) /
          gibbsPartitionZ (opEigenvalues H_diag hH_diag) β := by
    rw [perturbed_gibbsFailureProb_eq_inv_gibbsPartitionZ_mul_boltzmann_trace H_diag hH_diag β P,
      div_eq_inv_mul]
  rw [h_eq, div_le_iff₀ hZ_pos, h_num, h_den]
  have h_mul := mul_le_mul_of_nonneg_left h_sum_le hK_nn
  linarith

private def boolChar {ι : Type} [Fintype ι] (a η : ι → Bool) : ℝ :=
  ∏ c : ι, if a c && η c then (-1 : ℝ) else 1

private lemma boolChar_mul_left {ι : Type} [Fintype ι] (a₁ a₂ η : ι → Bool) :
    boolChar a₁ η * boolChar a₂ η = boolChar (syndromeXor a₁ a₂) η := by
  unfold boolChar syndromeXor; rw [← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun c _ => ?_
  cases a₁ c <;> cases a₂ c <;> cases η c <;> norm_num

private lemma boolChar_syndromeXor_right {ι : Type} [Fintype ι] (a η₁ η₂ : ι → Bool) :
    boolChar a (syndromeXor η₁ η₂) = boolChar a η₁ * boolChar a η₂ := by
  unfold boolChar syndromeXor; rw [← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun c _ => ?_
  cases a c <;> cases η₁ c <;> cases η₂ c <;> norm_num

private lemma boolChar_eq_neg_one_pow_and_subsetChar {ι : Type} [Fintype ι] [DecidableEq ι]
    (a η : ι → Bool) :
    let S := Finset.univ.filter (fun c => a c = true)
    boolChar a η = (-1 : ℝ) ^ ((S.filter (fun c => η c = true)).card) ∧
      boolChar a η = WeldedHierarchy.subsetChar S (syndromeToZMod2 η) := by
  intro S
  have h1 : boolChar a η = (-1 : ℝ) ^ ((S.filter (fun c => η c = true)).card) := by
    unfold boolChar
    rw [Finset.prod_ite, Finset.prod_const, Finset.prod_const_one, mul_one]
    congr 2; ext c; simp [S, Bool.and_eq_true]
  refine ⟨h1, h1.trans ?_⟩
  unfold WeldedHierarchy.subsetChar
  have h10 : (1 : ZMod 2) ≠ 0 := by decide
  have h_prod : (∏ c ∈ S, WeldedHierarchy.zmod2Char (syndromeToZMod2 η c)) =
      ∏ c ∈ S, if η c = true then (-1 : ℝ) else 1 := by
    refine Finset.prod_congr rfl fun c _ => ?_
    dsimp [WeldedHierarchy.zmod2Char, syndromeToZMod2]; cases η c <;> simp [h10]
  rw [h_prod, Finset.prod_ite, Finset.prod_const, Finset.prod_const_one, mul_one]

private lemma sum_boolChar_mul_boolChar {ι : Type} [Fintype ι] [DecidableEq ι]
    (η η₀ : ι → Bool) :
    (∑ a : ι → Bool, boolChar a η * boolChar a η₀) =
      if η = η₀ then (2 : ℝ) ^ Fintype.card ι else 0 := by
  have h_combine : (∑ a : ι → Bool, boolChar a η * boolChar a η₀) =
      ∏ c : ι, ∑ b : Bool, (if b && syndromeXor η η₀ c then (-1 : ℝ) else 1) := by
    simp_rw [← boolChar_syndromeXor_right]
    exact (Fintype.prod_sum (fun c b => if b && syndromeXor η η₀ c then (-1 : ℝ) else 1)).symm
  rw [h_combine]
  by_cases h_eq : η = η₀
  · subst h_eq; rw [if_pos rfl]
    have h_two : ∀ c ∈ (Finset.univ : Finset ι),
        (∑ b : Bool, if b && syndromeXor η η c then (-1 : ℝ) else 1) = 2 := by
      intro c _; rw [Fintype.sum_bool]; unfold syndromeXor; cases η c <;> norm_num
    rw [Finset.prod_congr rfl h_two, Finset.prod_const, Finset.card_univ]
  · rw [if_neg h_eq]
    have h_ex : ∃ c : ι, η c ≠ η₀ c := by
      by_contra h_all; push_neg at h_all; exact h_eq (funext h_all)
    rcases h_ex with ⟨c₀, hc₀⟩
    refine Finset.prod_eq_zero (Finset.mem_univ c₀) ?_
    rw [Fintype.sum_bool]; unfold syndromeXor
    revert hc₀; cases η c₀ <;> cases η₀ c₀ <;> intro hc₀ <;> first | contradiction | norm_num

private def HasNonnegBoolWalsh {ι : Type} [Fintype ι] [DecidableEq ι]
    (f : (ι → Bool) → ℝ) : Prop :=
  ∃ w : (ι → Bool) → ℝ, (∀ a, 0 ≤ w a) ∧ ∀ η, f η = ∑ a : ι → Bool, w a * boolChar a η

private lemma hasNonnegBoolWalsh_one {ι : Type} [Fintype ι] [DecidableEq ι] :
    HasNonnegBoolWalsh (fun _ : ι → Bool => (1 : ℝ)) := by
  refine ⟨fun a => if a = (fun _ => false) then 1 else 0,
    fun a => by (try dsimp only); split_ifs <;> norm_num, fun η => ?_⟩
  (try dsimp only)
  simp only [ite_mul, one_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  unfold boolChar; simp

private lemma hasNonnegBoolWalsh_mul {ι : Type} [Fintype ι] [DecidableEq ι]
    {f g : (ι → Bool) → ℝ} (hf : HasNonnegBoolWalsh f) (hg : HasNonnegBoolWalsh g) :
    HasNonnegBoolWalsh (fun η => f η * g η) := by
  rcases hf with ⟨w₁, hw₁, hf_eq⟩; rcases hg with ⟨w₂, hw₂, hg_eq⟩
  refine ⟨fun a => ∑ a₁ : ι → Bool, w₁ a₁ * w₂ (syndromeXor a₁ a),
    fun a => Finset.sum_nonneg fun a₁ _ => mul_nonneg (hw₁ a₁) (hw₂ _), fun η => ?_⟩
  (try dsimp only)
  rw [hf_eq η, hg_eq η, Finset.sum_mul]
  simp_rw [Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm (s := Finset.univ) (t := Finset.univ)
    (f := fun a a₁ => w₁ a₁ * w₂ (syndromeXor a₁ a) * boolChar a η)]
  refine Finset.sum_congr rfl fun a₁ _ => ?_
  refine Finset.sum_bij (fun a₂ _ => syndromeXor a₁ a₂)
    (fun _ _ => Finset.mem_univ _)
    (fun x _ y _ h => by (try dsimp only at h); rw [← syndromeXor_cancel_left a₁ x, ← syndromeXor_cancel_left a₁ y, h])
    (fun b _ => ⟨syndromeXor a₁ b, Finset.mem_univ _, syndromeXor_cancel_left a₁ b⟩)
    fun a₂ _ => ?_
  (try dsimp only)
  rw [syndromeXor_cancel_left, ← boolChar_mul_left]; ring

private lemma hasNonnegBoolWalsh_prod {ι α : Type} [Fintype ι] [DecidableEq ι]
    (s : Finset α) (F : α → (ι → Bool) → ℝ)
    (hF : ∀ x ∈ s, HasNonnegBoolWalsh (F x)) :
    HasNonnegBoolWalsh (fun η => ∏ x ∈ s, F x η) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using hasNonnegBoolWalsh_one
  | @insert x s hx ih =>
    simp_rw [Finset.prod_insert hx]
    exact hasNonnegBoolWalsh_mul (hF x (Finset.mem_insert_self x s))
      (ih fun y hy => hF y (Finset.mem_insert_of_mem hy))

private lemma hasNonnegBoolWalsh_of_walsh_nonneg {ι : Type} [Fintype ι] [DecidableEq ι]
    {f : (ι → Bool) → ℝ}
    (h_nn : ∀ S : Finset ι, 0 ≤ ∑ η : ι → Bool,
      ((-1 : ℝ) ^ ((S.filter (fun c => η c = true)).card)) * f η) :
    HasNonnegBoolWalsh f := by
  let N : ℝ := (2 : ℝ) ^ Fintype.card ι
  have hN_pos : 0 < N := by positivity
  refine ⟨fun a => N⁻¹ * ∑ η : ι → Bool, boolChar a η * f η, fun a => ?_, fun η₀ => ?_⟩
  · (try dsimp only)
    refine mul_nonneg (inv_nonneg.mpr (le_of_lt hN_pos)) ?_
    have h_eq : (∑ η : ι → Bool, boolChar a η * f η) =
        ∑ η : ι → Bool, ((-1 : ℝ) ^ (((Finset.univ.filter (fun c => a c = true)).filter
          (fun c => η c = true)).card)) * f η :=
      Finset.sum_congr rfl fun η _ => by rw [(boolChar_eq_neg_one_pow_and_subsetChar a η).1]
    rw [h_eq]; exact h_nn _
  · (try dsimp only)
    have h_swap : (∑ a : ι → Bool, (N⁻¹ * ∑ η : ι → Bool, boolChar a η * f η) * boolChar a η₀) =
        N⁻¹ * ∑ η : ι → Bool, f η * (∑ a : ι → Bool, boolChar a η * boolChar a η₀) := by
      calc (∑ a : ι → Bool, (N⁻¹ * ∑ η : ι → Bool, boolChar a η * f η) * boolChar a η₀)
        _ = ∑ a : ι → Bool, ∑ η : ι → Bool, N⁻¹ * (f η * (boolChar a η * boolChar a η₀)) :=
            Finset.sum_congr rfl fun a _ => by
              rw [Finset.mul_sum, Finset.sum_mul]
              exact Finset.sum_congr rfl fun η _ => by ring
        _ = ∑ η : ι → Bool, ∑ a : ι → Bool, N⁻¹ * (f η * (boolChar a η * boolChar a η₀)) :=
            Finset.sum_comm
        _ = N⁻¹ * ∑ η : ι → Bool, f η * (∑ a : ι → Bool, boolChar a η * boolChar a η₀) := by
            rw [Finset.mul_sum]
            exact Finset.sum_congr rfl fun η _ => by rw [← Finset.mul_sum, ← Finset.mul_sum]
    have h_eval : (∑ η : ι → Bool, f η * (∑ a : ι → Bool, boolChar a η * boolChar a η₀)) =
        f η₀ * N := by
      simp_rw [sum_boolChar_mul_boolChar, mul_ite, mul_zero, Finset.sum_ite_eq']
      simp [N]
    symm
    rw [h_swap, h_eval, mul_comm (f η₀) N, ← mul_assoc, inv_mul_cancel₀ (ne_of_gt hN_pos), one_mul]

private lemma hasNonnegBoolWalsh_single_check_exp {ι : Type} [Fintype ι] [DecidableEq ι]
    (c : ι) {α : ℝ} (hα : 0 ≤ α) :
    HasNonnegBoolWalsh (fun η : ι → Bool => Real.exp (-α * if η c = true then 1 else 0)) := by
  have hexp_le : Real.exp (-α) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
  have hexp_pos : 0 < Real.exp (-α) := Real.exp_pos _
  let a₀ : ι → Bool := fun _ => false
  let a₁ : ι → Bool := fun i => decide (i = c)
  refine ⟨fun a => (if a = a₀ then (1 + Real.exp (-α)) / 2 else 0) +
      (if a = a₁ then (1 - Real.exp (-α)) / 2 else 0),
    fun a => by (try dsimp only); exact add_nonneg (by split_ifs <;> linarith) (by split_ifs <;> linarith),
    fun η => ?_⟩
  (try dsimp only)
  simp only [add_mul, Finset.sum_add_distrib, ite_mul, zero_mul, Finset.sum_ite_eq',
    Finset.mem_univ, if_true]
  have h0 : boolChar a₀ η = 1 := by unfold boolChar; simp [a₀]
  have h1 : boolChar a₁ η = if η c = true then -1 else 1 := by
    unfold boolChar; dsimp [a₁]
    rw [Finset.prod_eq_single c]
    · simp
    · intro i _ hi; simp [hi]
    · intro hc; exact False.elim (hc (Finset.mem_univ c))
  rw [h0, h1]; cases η c <;> simp <;> ring

/-- **Subgroup Coset Sum Inequality for Spectator Pauli-Diagonal Energy
    (`spectator_pauliDiagonal_coset_sum_le`, Part II, Proposition 3.6 (`prop:walsh-coset-dominance`), Lemma 3.7 (`lem:peierls-bogoliubov`))** -/
theorem spectator_pauliDiagonal_coset_sum_le
    {L q_code r_0 m_max w_0 R_pert : ℕ} [NeZero L]
    (D_field : Box3D L → LocalCSSDescriptor q_code r_0 m_max)
    (sys : IndexedCommutingProjectorHamiltonian 3 L
      (UniformSite3D L (CodeSlotConfig q_code)) (StaticCSSCheckIdx L q_code m_max))
    (h_sys_checks : ∀ idx : StaticCSSCheckIdx L q_code m_max,
      sys.checkProj idx = staticCSSCheckProj D_field idx ∧
      sys.support idx = staticCSSCheckSupport D_field idx ∧ sys.weight idx = 1)
    (h_geom : sys.IsGeometricallyLocal r_0 w_0)
    {C_rca β_c J β : ℝ} (hC_rca : 0 ≤ C_rca) (hβc_ge : 16 ≤ β_c) (hβ : β > β_c)
    (hJ_nn : 0 ≤ J) (hJ_le : J ≤ collarWalshCouplingThreshold R_pert r_0 w_0 C_rca)
    (V : QuasiLocalPerturbation 3 L (UniformSite3D L (CodeSlotConfig q_code)))
    (e_loc : ℕ → Finset (Box3D L) → ℝ)
    (d_loc : ℕ → Finset (Box3D L) → (StaticCSSCheckIdx L q_code m_max → Bool) → ℝ)
    (h_scalar : IsLocalCollarScalarFamily D_field sys R_pert C_rca J V e_loc d_loc)
    (h_walsh : ∀ r ∈ Finset.Icc 1 (min R_pert L), ∀ A ∈ boxCubes 3 L r,
      ∀ S : Finset (StaticCSSCheckIdx L q_code m_max),
        let δ := β / (8 * (rcaDiagonalCoercivityConstant 3 R_pert r_0 w_0 C_rca + 1))
        0 ≤ ∑ η : StaticCSSCheckIdx L q_code m_max → Bool,
          ((-1 : ℝ) ^ ((S.filter (fun c => η c = true)).card)) *
            localCollarBoltzmannFactor sys C_rca δ β d_loc r A η)
    (W : Finset (StaticCSSCheckIdx L q_code m_max))
    (σ₀ : StaticCSSCheckIdx L q_code m_max → Bool) :
    (∑ τ ∈ witnessCleanRealizableSyndromes D_field W,
        Real.exp (-β * spectatorPauliDiagonalEnergy sys C_rca R_pert d_loc W
          (syndromeXor σ₀ τ))) ≤
      ∑ τ ∈ witnessCleanRealizableSyndromes D_field W,
        Real.exp (-β * spectatorPauliDiagonalEnergy sys C_rca R_pert d_loc W τ) := by
  let Δ := rcaDiagonalCoercivityConstant 3 R_pert r_0 w_0 C_rca
  let δ := β / (8 * (Δ + 1))
  have hβ_pos : 0 < β := by linarith
  have hΔ_nn : 0 ≤ Δ := by dsimp [Δ, rcaDiagonalCoercivityConstant]; positivity
  have hδ_nn : 0 ≤ δ := by dsimp [δ]; positivity
  let specCubes (r : ℕ) :=
    (boxCubes 3 L r).filter (fun A => Disjoint (rcaCollarChecks sys C_rca r A) W)
  let N_spec (c : StaticCSSCheckIdx L q_code m_max) : ℝ :=
    ∑ r ∈ Finset.Icc 1 (min R_pert L),
      (((specCubes r).filter (fun A => c ∈ rcaCollarChecks sys C_rca r A)).card : ℝ)
  have hN_spec_le : ∀ c, N_spec c ≤ Δ := by
    intro c
    let K_geom : ℕ :=
      (2 * (R_pert + 2 * linearExpansionRadius C_rca R_pert + r_0) + 1) ^ 3 * (w_0 + 1)
    have h_r : ∀ r ∈ Finset.Icc 1 (min R_pert L),
        (((specCubes r).filter (fun A => c ∈ rcaCollarChecks sys C_rca r A)).card : ℝ) ≤
          (K_geom : ℝ) := by
      intro r hr
      have h_sub : (specCubes r).filter (fun A => c ∈ rcaCollarChecks sys C_rca r A) ⊆
          (boxCubes 3 L r).filter (fun A => c ∈ rcaCollarChecks sys C_rca r A) :=
        Finset.filter_subset_filter _ (Finset.filter_subset _ _)
      exact_mod_cast le_trans (Finset.card_le_card h_sub)
        (card_filter_mem_rcaCollarChecks_le D_field sys h_sys_checks hC_rca hr c)
    have h_sum := Finset.sum_le_card_nsmul (Finset.Icc 1 (min R_pert L)) _ (K_geom : ℝ) h_r
    rw [nsmul_eq_mul] at h_sum
    have h_Icc : ((Finset.Icc 1 (min R_pert L)).card : ℝ) ≤ (R_pert : ℝ) := by
      have h_nat : (Finset.Icc 1 (min R_pert L)).card ≤ R_pert := by
        rw [Nat.card_Icc]; have := Nat.min_le_left R_pert L; omega
      exact_mod_cast h_nat
    refine le_trans h_sum (le_trans (mul_le_mul_of_nonneg_right h_Icc (Nat.cast_nonneg K_geom)) ?_)
    dsimp [Δ, rcaDiagonalCoercivityConstant, K_geom]; push_cast; linarith
  have h_rem_nn : ∀ c, 0 ≤ β - δ * N_spec c := by
    intro c
    have h1 : δ * N_spec c ≤ δ * Δ := mul_le_mul_of_nonneg_left (hN_spec_le c) hδ_nn
    have h2 : δ * Δ ≤ β / 8 := by
      dsimp [δ]; rw [div_mul_eq_mul_div, div_le_div_iff₀ (by linarith) (by norm_num)]; linarith
    linarith
  have h_factor_eq : ∀ η : StaticCSSCheckIdx L q_code m_max → Bool,
      Real.exp (-β * spectatorPauliDiagonalEnergy sys C_rca R_pert d_loc W η) =
        (∏ c ∈ Finset.univ \ W,
          Real.exp (-(β - δ * N_spec c) * if η c = true then 1 else 0)) *
        (∏ r ∈ Finset.Icc 1 (min R_pert L),
          ∏ A ∈ specCubes r, localCollarBoltzmannFactor sys C_rca δ β d_loc r A η) := by
    intro η
    unfold localCollarBoltzmannFactor spectatorPauliDiagonalEnergy
    simp_rw [← Real.exp_sum, ← Real.exp_add]
    congr 1
    have h_card_Wc : (((Finset.univ \ W).filter (fun c => η c = true)).card : ℝ) =
        ∑ c ∈ Finset.univ \ W, if η c = true then (1 : ℝ) else 0 := by
      rw [Finset.sum_boole]
    have h_collar_sum :
        ∀ r ∈ Finset.Icc 1 (min R_pert L),
          (∑ A ∈ specCubes r,
            (-δ * (((rcaCollarChecks sys C_rca r A).filter (fun c => η c = true)).card : ℝ) -
              β * d_loc r A η)) =
          (∑ c ∈ Finset.univ \ W,
            -δ * (((specCubes r).filter (fun A => c ∈ rcaCollarChecks sys C_rca r A)).card : ℝ) *
              (if η c = true then (1 : ℝ) else 0)) -
          ∑ A ∈ specCubes r, β * d_loc r A η := by
      intro r _
      rw [Finset.sum_sub_distrib]
      congr 1
      have h_A : ∀ A ∈ specCubes r,
          -δ * (((rcaCollarChecks sys C_rca r A).filter (fun c => η c = true)).card : ℝ) =
          ∑ c ∈ Finset.univ \ W,
            (if c ∈ rcaCollarChecks sys C_rca r A then (1 : ℝ) else 0) *
              (-δ * if η c = true then (1 : ℝ) else 0) := by
        intro A hA
        have h_disj : Disjoint (rcaCollarChecks sys C_rca r A) W := (Finset.mem_filter.mp hA).2
        have h_sub_Wc : rcaCollarChecks sys C_rca r A ⊆ Finset.univ \ W := fun c hc =>
          Finset.mem_sdiff.mpr ⟨Finset.mem_univ c, Finset.disjoint_left.mp h_disj hc⟩
        have h_inter : (Finset.univ \ W).filter (fun c => c ∈ rcaCollarChecks sys C_rca r A) =
            rcaCollarChecks sys C_rca r A := by
          ext c; simp only [Finset.mem_filter]
          exact ⟨fun h => h.2, fun h => ⟨h_sub_Wc h, h⟩⟩
        rw [← h_inter, Finset.card_eq_sum_ones, Nat.cast_sum, Finset.sum_filter,
          Finset.sum_filter, Finset.mul_sum]
        refine Finset.sum_congr rfl fun c hc => ?_
        simp only [Finset.mem_filter, hc, true_and]
        split_ifs <;> ring
      rw [Finset.sum_congr rfl h_A, Finset.sum_comm]
      refine Finset.sum_congr rfl fun c _ => ?_
      have h_boole2 :
          (((specCubes r).filter (fun A => c ∈ rcaCollarChecks sys C_rca r A)).card : ℝ) =
          ∑ i ∈ specCubes r, if c ∈ rcaCollarChecks sys C_rca r i then (1 : ℝ) else 0 := by
        rw [Finset.card_eq_sum_ones, Nat.cast_sum, Finset.sum_filter]
        refine Finset.sum_congr rfl fun i _ => by split_ifs <;> ring
      rw [← Finset.sum_mul, ← h_boole2]
      ring
    rw [Finset.sum_congr rfl h_collar_sum, Finset.sum_sub_distrib, Finset.sum_comm]
    have h_c_combine :
        (∑ c ∈ Finset.univ \ W, -(β - δ * N_spec c) * if η c = true then (1 : ℝ) else 0) +
          (∑ c ∈ Finset.univ \ W, ∑ x ∈ Finset.Icc 1 (min R_pert L),
            -δ * (((specCubes x).filter (fun A => c ∈ rcaCollarChecks sys C_rca x A)).card : ℝ) *
              if η c = true then (1 : ℝ) else 0) =
        -β * ∑ c ∈ Finset.univ \ W, if η c = true then (1 : ℝ) else 0 := by
      rw [← Finset.sum_add_distrib, Finset.mul_sum]
      refine Finset.sum_congr rfl fun c _ => ?_
      have h_nspec_sum :
          (∑ x ∈ Finset.Icc 1 (min R_pert L),
            -δ * (((specCubes x).filter (fun A => c ∈ rcaCollarChecks sys C_rca x A)).card : ℝ) *
              if η c = true then (1 : ℝ) else 0) =
          -δ * N_spec c * if η c = true then (1 : ℝ) else 0 := by
        dsimp [N_spec]; rw [Finset.mul_sum, Finset.sum_mul]
      rw [h_nspec_sum]; ring
    rw [← add_sub_assoc, h_c_combine, ← h_card_Wc]
    dsimp [specCubes]; simp_rw [← Finset.mul_sum]; ring
  have h_cone : HasNonnegBoolWalsh
      (fun η => Real.exp (-β * spectatorPauliDiagonalEnergy sys C_rca R_pert d_loc W η)) := by
    have h_prod_cone : HasNonnegBoolWalsh (fun η =>
        (∏ c ∈ Finset.univ \ W,
          Real.exp (-(β - δ * N_spec c) * if η c = true then 1 else 0)) *
        (∏ r ∈ Finset.Icc 1 (min R_pert L),
          ∏ A ∈ specCubes r, localCollarBoltzmannFactor sys C_rca δ β d_loc r A η)) :=
      hasNonnegBoolWalsh_mul
        (hasNonnegBoolWalsh_prod (Finset.univ \ W) _ fun c _ =>
          hasNonnegBoolWalsh_single_check_exp c (h_rem_nn c))
        (hasNonnegBoolWalsh_prod (Finset.Icc 1 (min R_pert L)) _ fun r hr =>
          hasNonnegBoolWalsh_prod (specCubes r) _ fun A hA =>
            hasNonnegBoolWalsh_of_walsh_nonneg (h_walsh r hr A (Finset.mem_filter.mp hA).1))
    rcases h_prod_cone with ⟨w, hw, h_eq⟩
    exact ⟨w, hw, fun η => (h_factor_eq η).trans (h_eq η)⟩
  rcases h_cone with ⟨w, hw_nn, hw_eq⟩
  have hC₀ := zero_mem_and_syndromeXor_closed_realizableZeroOutsideSyndromes D_field W
  have h_lhs :
      (∑ τ ∈ witnessCleanRealizableSyndromes D_field W,
        Real.exp (-β * spectatorPauliDiagonalEnergy sys C_rca R_pert d_loc W (syndromeXor σ₀ τ))) =
      ∑ a : StaticCSSCheckIdx L q_code m_max → Bool,
        w a * (boolChar a σ₀ * ∑ τ ∈ witnessCleanRealizableSyndromes D_field W, boolChar a τ) := by
    simp_rw [hw_eq, boolChar_syndromeXor_right]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun a _ => ?_
    simp_rw [← mul_assoc, ← Finset.mul_sum]
  have h_rhs :
      (∑ τ ∈ witnessCleanRealizableSyndromes D_field W,
        Real.exp (-β * spectatorPauliDiagonalEnergy sys C_rca R_pert d_loc W τ)) =
      ∑ a : StaticCSSCheckIdx L q_code m_max → Bool,
        w a * (∑ τ ∈ witnessCleanRealizableSyndromes D_field W, boolChar a τ) := by
    simp_rw [hw_eq]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun a _ => (Finset.mul_sum _ _ _).symm
  rw [h_lhs, h_rhs]
  refine Finset.sum_le_sum fun a _ => ?_
  let S_a := Finset.univ.filter (fun c => a c = true)
  have h_char_eq : ∀ η, boolChar a η = WeldedHierarchy.subsetChar S_a (syndromeToZMod2 η) :=
    fun η => (boolChar_eq_neg_one_pow_and_subsetChar a η).2
  have h_sub_sum_nn : 0 ≤ ∑ τ ∈ witnessCleanRealizableSyndromes D_field W, boolChar a τ := by
    simp_rw [h_char_eq]
    exact sum_subsetChar_syndromeXor_subspace_nonneg
      (witnessCleanRealizableSyndromes D_field W) hC₀.1 hC₀.2 S_a
  have h_le_one : boolChar a σ₀ ≤ 1 := by
    rw [h_char_eq]; exact WeldedHierarchy.subsetChar_le_one S_a (syndromeToZMod2 σ₀)
  exact mul_le_mul_of_nonneg_left (by nlinarith) (hw_nn a)

/-- **Realizable-Syndrome Sector Energy Peeling Bound
    (`realizable_pauliDiagonalSectorEnergy_witness_sum_le`)** -/
theorem realizable_pauliDiagonalSectorEnergy_witness_sum_le
    {L q_code r_0 m_max w_0 L_star R_pert : ℕ} [NeZero L]
    (D_field : Box3D L → LocalCSSDescriptor q_code r_0 m_max) (h_valid : ValidDescriptorField D_field)
    (sys : IndexedCommutingProjectorHamiltonian 3 L
      (UniformSite3D L (CodeSlotConfig q_code)) (StaticCSSCheckIdx L q_code m_max))
    (h_sys_checks : ∀ idx : StaticCSSCheckIdx L q_code m_max,
      sys.checkProj idx = staticCSSCheckProj D_field idx ∧
      sys.support idx = staticCSSCheckSupport D_field idx ∧ sys.weight idx = 1)
    (h_geom : sys.IsGeometricallyLocal r_0 w_0)
    {C_rca β_c J β : ℝ} (hR_pos : 1 ≤ R_pert) (hR_le : R_pert ≤ L_star) (hC_rca : 0 ≤ C_rca)
    (hβc_ge : 16 ≤ β_c) (hβ : β > β_c) (hJ_nn : 0 ≤ J)
    (hJ_le : J ≤ collarWalshCouplingThreshold R_pert r_0 w_0 C_rca)
    (h_tqo1 : SatisfiesTQO1 sys L_star)
    (h_tqo2 : SatisfiesSectorFilteredLinearTQO2 sys 1 L_star C_rca)
    (V : QuasiLocalPerturbation 3 L (UniformSite3D L (CodeSlotConfig q_code)))
    (e_loc : ℕ → Finset (Box3D L) → ℝ)
    (d_loc : ℕ → Finset (Box3D L) → (StaticCSSCheckIdx L q_code m_max → Bool) → ℝ)
    (h_scalar : IsLocalCollarScalarFamily D_field sys R_pert C_rca J V e_loc d_loc)
    (W : Finset (StaticCSSCheckIdx L q_code m_max)) (hW_ne : W.Nonempty) :
    (∑ σ ∈ (realizableSyndromes D_field).filter (fun σ => ∀ idx ∈ W, σ idx = true),
        Real.exp (-β * pauliDiagonalSectorEnergy sys R_pert d_loc σ)) ≤
      Real.exp (-((β_c / 2 + min (β - β_c) 1 + 3) * (W.card : ℝ))) *
        ∑ σ ∈ realizableSyndromes D_field,
          Real.exp (-β * pauliDiagonalSectorEnergy sys R_pert d_loc σ) := by
  have hβ_pos : 0 < β := by linarith
  obtain ⟨h_num_or, h_den_le⟩ :=
    pauliDiagonal_witness_coset_reduction_le D_field sys h_sys_checks h_geom
      hC_rca hβ_pos hJ_nn hJ_le V e_loc d_loc h_scalar W
  have h_sum_nn :
      0 ≤ ∑ σ ∈ realizableSyndromes D_field,
        Real.exp (-β * pauliDiagonalSectorEnergy sys R_pert d_loc σ) :=
    Finset.sum_nonneg fun _ _ => le_of_lt (Real.exp_pos _)
  rcases h_num_or with h_empty | ⟨σ₀, _, h_num_le⟩
  · rw [h_empty, Finset.sum_empty]
    exact mul_nonneg (le_of_lt (Real.exp_pos _)) h_sum_nn
  · have h_coset :=
      spectator_pauliDiagonal_coset_sum_le D_field sys h_sys_checks h_geom
        hC_rca hβc_ge hβ hJ_nn hJ_le V e_loc d_loc h_scalar
        (fun r hr A hA S => local_collar_boltzmann_factor_walsh_nonneg
          D_field sys h_sys_checks h_geom hC_rca hβc_ge hβ hJ_nn hJ_le V e_loc d_loc h_scalar hr hA S)
        W σ₀
    have h_step1 :
        (∑ σ ∈ (realizableSyndromes D_field).filter (fun σ => ∀ idx ∈ W, σ idx = true),
            Real.exp (-β * pauliDiagonalSectorEnergy sys R_pert d_loc σ)) ≤
          Real.exp (-(7 / 8 : ℝ) * β * (W.card : ℝ)) *
            (Real.exp ((1 / 8 : ℝ) * β * (W.card : ℝ)) *
              ∑ σ ∈ realizableSyndromes D_field,
                Real.exp (-β * pauliDiagonalSectorEnergy sys R_pert d_loc σ)) :=
      le_trans h_num_le
        (mul_le_mul_of_nonneg_left (le_trans h_coset h_den_le) (le_of_lt (Real.exp_pos _)))
    have h_exp_combine :
        Real.exp (-(7 / 8 : ℝ) * β * (W.card : ℝ)) *
          Real.exp ((1 / 8 : ℝ) * β * (W.card : ℝ)) =
          Real.exp (-((3 / 4 : ℝ) * β * (W.card : ℝ))) := by
      rw [← Real.exp_add]; congr 1; ring
    have h_rate := (three_quarters_beta_ge_target_witness_rate hβc_ge hβ W.card).2.2
    calc (∑ σ ∈ (realizableSyndromes D_field).filter (fun σ => ∀ idx ∈ W, σ idx = true),
            Real.exp (-β * pauliDiagonalSectorEnergy sys R_pert d_loc σ))
      _ ≤ (Real.exp (-(7 / 8 : ℝ) * β * (W.card : ℝ)) *
            Real.exp ((1 / 8 : ℝ) * β * (W.card : ℝ))) *
            ∑ σ ∈ realizableSyndromes D_field,
              Real.exp (-β * pauliDiagonalSectorEnergy sys R_pert d_loc σ) := by
          linarith [h_step1]
      _ = Real.exp (-((3 / 4 : ℝ) * β * (W.card : ℝ))) *
            ∑ σ ∈ realizableSyndromes D_field,
              Real.exp (-β * pauliDiagonalSectorEnergy sys R_pert d_loc σ) := by
          rw [h_exp_combine]
      _ ≤ Real.exp (-((β_c / 2 + min (β - β_c) 1 + 3) * (W.card : ℝ))) *
            ∑ σ ∈ realizableSyndromes D_field,
              Real.exp (-β * pauliDiagonalSectorEnergy sys R_pert d_loc σ) :=
          mul_le_mul_of_nonneg_right h_rate h_sum_nn

/-- **Pauli-Diagonal Local Collar Cluster and Spectator Cancellation Bound
    (`gibbsFailureProb_pauliDiagonal_collar_peeling_le`)** -/
theorem gibbsFailureProb_pauliDiagonal_collar_peeling_le
    {L q_code r_0 m_max w_0 L_star R_pert : ℕ} [NeZero L]
    (D_field : Box3D L → LocalCSSDescriptor q_code r_0 m_max) (h_valid : ValidDescriptorField D_field)
    (sys : IndexedCommutingProjectorHamiltonian 3 L
      (UniformSite3D L (CodeSlotConfig q_code)) (StaticCSSCheckIdx L q_code m_max))
    (h_sys_checks : ∀ idx : StaticCSSCheckIdx L q_code m_max,
      sys.checkProj idx = staticCSSCheckProj D_field idx ∧
      sys.support idx = staticCSSCheckSupport D_field idx ∧ sys.weight idx = 1)
    (h_geom : sys.IsGeometricallyLocal r_0 w_0)
    {C_rca β_c J β E_vac : ℝ} (hR_pos : 1 ≤ R_pert) (hR_le : R_pert ≤ L_star) (hC_rca : 0 ≤ C_rca)
    (hβc_ge : 16 ≤ β_c) (hβ : β > β_c) (hJ_nn : 0 ≤ J)
    (hJ_le : J ≤ collarWalshCouplingThreshold R_pert r_0 w_0 C_rca)
    (h_tqo1 : SatisfiesTQO1 sys L_star)
    (h_tqo2 : SatisfiesSectorFilteredLinearTQO2 sys 1 L_star C_rca)
    (V : QuasiLocalPerturbation 3 L (UniformSite3D L (CodeSlotConfig q_code)))
    (hV_range : HasFiniteRangeBound V R_pert J)
    (hH_diag_sa :
      IsSelfAdjoint (sys.H0 + pauliDiagonalPart sys V R_pert - ((E_vac : ℝ) : ℂ) • 1))
    (hH_diag_comm : ∀ σ : StaticCSSCheckIdx L q_code m_max → Bool,
      Commute (sys.H0 + pauliDiagonalPart sys V R_pert - ((E_vac : ℝ) : ℂ) • 1)
        (sys.syndromeProjector σ))
    (W : Finset (StaticCSSCheckIdx L q_code m_max)) :
    gibbsFailureProb (sys.H0 + pauliDiagonalPart sys V R_pert - ((E_vac : ℝ) : ℂ) • 1)
      hH_diag_sa β (positiveCheckWitnessProj sys W) ≤
      Real.exp (-((β_c / 2 + min (β - β_c) 1 + 3) * (W.card : ℝ))) := by
  by_cases hW_ne : W.Nonempty
  · rcases exists_pauliDiagonal_local_collar_decomposition
        D_field sys h_sys_checks hR_le h_tqo2 V hV_range with ⟨e_loc, he_decomp⟩
    rcases exists_local_collar_scalar_family_of_tqo2
        D_field h_valid sys h_sys_checks h_geom hR_pos hR_le hC_rca hJ_nn
        h_tqo1 h_tqo2 V hV_range e_loc he_decomp with ⟨d_loc, h_scalar⟩
    obtain ⟨hK_nn, h_num, h_den⟩ :=
      boltzmann_trace_and_partitionZ_eq_realizable_sectorEnergy_sum
        D_field h_valid sys h_sys_checks (β := β) (E_vac := E_vac)
        V e_loc he_decomp d_loc h_scalar hH_diag_sa hH_diag_comm W
    have h_sum_le :=
      realizable_pauliDiagonalSectorEnergy_witness_sum_le
        D_field h_valid sys h_sys_checks h_geom hR_pos hR_le hC_rca hβc_ge hβ
        hJ_nn hJ_le h_tqo1 h_tqo2 V e_loc d_loc h_scalar W hW_ne
    exact gibbsFailureProb_pauliDiagonal_le_of_realizable_sectorEnergy_sum
      (sys.H0 + pauliDiagonalPart sys V R_pert - ((E_vac : ℝ) : ℂ) • 1)
      hH_diag_sa β (positiveCheckWitnessProj sys W)
      (realizableSyndromes D_field)
      ((realizableSyndromes D_field).filter (fun σ => ∀ idx ∈ W, σ idx = true))
      (pauliDiagonalSectorEnergy sys R_pert d_loc)
      hK_nn h_num h_den h_sum_le
  · rw [Finset.not_nonempty_iff_eq_empty] at hW_ne
    subst hW_ne
    rw [positiveCheckWitnessProj_empty_eq_one sys,
      gibbsFailureProb_one_eq_one _ hH_diag_sa β]
    simp only [Finset.card_empty, Nat.cast_zero, mul_zero, neg_zero, Real.exp_zero, le_rfl]

end SpacetimeWorldlineKP
end
