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

import Proofs.DirectWorldlineCluster.ScaleSplitAndDiagonalPeeling
import Proofs.DirectWorldlineCluster.WorldlineDysonUrsellBridge
import Proofs.DressedThermalDuhamel.PerturbedKMSLindbladODEBounds

/-!
# Scale-Split Master Gibbs Bound, Fixed-Temperature Stability, and Low-Temperature Crossover

Synthesizes native-scale worldline factorization and tube-local Ursell erasure (`worldline_factorization_and_ursell_erasure`) to prove the scale-split master Gibbs failure inequality (`scale_split_master_gibbs_bound`). Derives uniform fixed-temperature bare safe-subspace Gibbs stability below `directWorldlineThreshold` (`fixed_temp_window_gibbs_stability`) as well as the low-temperature cooling window and QAC-dressed BHM relative-form crossover (`low_temp_window_and_bhm_crossover`).

## References

* Part II, Section 6.3 (`subsec:main-theorems`), Theorem 6.3 (`thm:main-A`)
* Part II, Section 6.3 (`subsec:main-theorems`), Theorem 6.4 (`thm:main-B`)
* Part II, Section 5.1 (`subsec:direct-worldline-synthesis`), Theorem 5.1 (`thm:direct-worldline-intact-cluster-erasure`)
* Part II, Section 5.2 (`subsec:low-temp-crossover`), Theorem 5.3 (`thm:low-temperature-window-and-crossover`)
-/

noncomputable section

open scoped Classical BigOperators InnerProduct ComplexConjugate
open Filter Topology Asymptotics ContinuousLinearMap KMSPinchedGibbs PerturbedThermalBarrier
open SpacetimeWorldlineKP

set_option linter.unusedVariables false
set_option maxRecDepth 200000
set_option maxHeartbeats 1600000

namespace DirectWorldlineCluster

local notation "SiteCSS[" L ", " q_code "]" => UniformSite3D L (CodeSlotConfig q_code)
local notation "ℋ_CSS[" L ", " q_code "]" => ManyBodyHilbertSpace (SiteCSS[L, q_code])
local notation "ℬ_CSS[" L ", " q_code "]" => ℋ_CSS[L, q_code] →L[ℂ] ℋ_CSS[L, q_code]
local notation "IdxCSS[" L ", " q_code ", " m_max "]" => StaticCSSCheckIdx L q_code m_max
local notation "SysCSS[" L ", " q_code ", " m_max "]" =>
  IndexedCommutingProjectorHamiltonian 3 L (SiteCSS[L, q_code]) (IdxCSS[L, q_code, m_max])

/-- **Worldline Factorization and Time-Reversal Non-Negativity (`worldline_factorization_and_time_reversal_nonneg`)** (Part II, Section 3.5 (`subsec:worldline-expansion`), Lemma 3.9 (`lem:worldline-factorization-time-reversal`)):
For any Hermitian off-diagonal jump matrix `K` (`K τ σ = star (K σ τ)`), the time-reversal paired
2-jump weight `‖K σ τ‖^2 * exp(-β * (E σ + E τ) / 2)` is non-negative, and for any finite family
of disjoint spacetime tubes `T ∈ tubes` with non-negative local weights `Z_tube T ≥ 0`, the
product of tube partition factors satisfies `∏ T ∈ tubes, (1 + Z_tube T) ≤ exp(∑ T ∈ tubes, Z_tube T)`. -/
theorem worldline_factorization_and_time_reversal_nonneg
    {ι_synd ι_tube : Type*}
    (K : ι_synd → ι_synd → ℂ) (E_diag : ι_synd → ℝ) (β : ℝ)
    (tubes : Finset ι_tube) (Z_tube : ι_tube → ℝ)
    (h_herm : ∀ σ τ : ι_synd, K τ σ = star (K σ τ))
    (hZ_nonneg : ∀ T ∈ tubes, 0 ≤ Z_tube T) :
    (∀ σ τ : ι_synd, 0 ≤ ‖K σ τ‖ ^ 2 * Real.exp (-β * (E_diag σ + E_diag τ) / 2)) ∧
    (∏ T ∈ tubes, (1 + Z_tube T)) ≤ Real.exp (∑ T ∈ tubes, Z_tube T) := by
  refine ⟨fun σ τ => by positivity, ?_⟩
  rw [Real.exp_sum]
  refine Finset.prod_le_prod₀ (fun T hT => by linarith [hZ_nonneg T hT]) (fun T _ => ?_)
  linarith [Real.add_one_le_exp (Z_tube T)]

private lemma sum_biUnion_le_of_nonneg {α β_t : Type*} [DecidableEq β_t] (s : Finset α) (t : α → Finset β_t) (g : β_t → ℝ) (hg : ∀ b, 0 ≤ g b) :
    (∑ b ∈ s.biUnion t, g b) ≤ ∑ a ∈ s, ∑ b ∈ t a, g b := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    rw [Finset.biUnion_insert, Finset.sum_insert ha]
    linarith [Finset.sum_union_inter (s₁ := t a) (s₂ := s.biUnion t) (f := g), Finset.sum_nonneg fun b (_ : b ∈ t a ∩ s.biUnion t) => hg b]

/-- **Tube-Local Ursell Erasure Log-Ratio Bound (`tubeLocal_ursell_erasure_log_ratio_le`)** (Part II, Section 3.5 (`subsec:worldline-expansion`), Proposition 3.10 (`prop:tube-local-ursell-erasure`), Equations `eq:ursell-partition-sigma`–`eq:touching-ursell-bound`):
When `0 ≤ J ≤ worldlineSpanningThreshold Δ_RCA C_wl c_wl β f R_cut` with positive parameters
`Δ_RCA, C_wl, c_wl, β > 0` and `0 < worldlineNativeKPSum f C_wl c_wl β R_cut`, the scaled
Kotecký–Preiss polymer sum `64 * exp 1 * max 1 β * J * worldlineNativeKPSum f C_wl c_wl β R_cut`
is at most `1`. For any witness `W` and cluster polymer family `(polySupport, w_ursell)` where
`Z_full = Z_erased * exp(Phi_corr_W)` and `|Phi_corr_W|` is bounded by the sum of `|w_ursell γ|`
over polymers intersecting `W` (with each pinned sum `u ∈ W` bounded by the native KP sum),
double counting over `u ∈ W` yields
`|Phi_corr_W| ≤ (64 * exp 1 * max 1 β * J * worldlineNativeKPSum f C_wl c_wl β R_cut) * W.card`
and `Z_full / Z_erased ≤ exp(W.card)`. -/
theorem tubeLocal_ursell_erasure_log_ratio_le
    {ι_chk ι_poly : Type*} [DecidableEq ι_chk] [Fintype ι_poly] [DecidableEq ι_poly]
    (W : Finset ι_chk) (polySupport : ι_poly → Finset ι_chk) (w_ursell : ι_poly → ℝ)
    (f : ℕ → ℝ) (R_cut : ℕ) (Δ_RCA C_wl c_wl β J Z_full Z_erased Phi_corr_W : ℝ)
    (hΔ_RCA : 0 < Δ_RCA) (hβ : 0 < β) (hJ : 0 ≤ J)
    (h_sum_pos : 0 < worldlineNativeKPSum f C_wl c_wl β R_cut)
    (h_thresh : J ≤ worldlineSpanningThreshold Δ_RCA C_wl c_wl β f R_cut)
    (hZ_erased : 0 < Z_erased)
    (h_ursell_id : Z_full = Z_erased * Real.exp Phi_corr_W)
    (h_phi_bound : |Phi_corr_W| ≤
      ∑ γ ∈ Finset.univ.filter (fun γ => ¬ Disjoint (polySupport γ) W), |w_ursell γ|)
    (h_pinned_sum : ∀ u ∈ W,
      (∑ γ ∈ Finset.univ.filter (fun γ => u ∈ polySupport γ), |w_ursell γ|) ≤
        64 * Real.exp 1 * max 1 β * J * worldlineNativeKPSum f C_wl c_wl β R_cut) :
    64 * Real.exp 1 * max 1 β * J * worldlineNativeKPSum f C_wl c_wl β R_cut ≤ 1 ∧
    |Phi_corr_W| ≤
      64 * Real.exp 1 * max 1 β * J * worldlineNativeKPSum f C_wl c_wl β R_cut * (W.card : ℝ) ∧
    Z_full / Z_erased ≤ Real.exp (W.card : ℝ) := by
  have hJ_le : J ≤ 1 / (64 * Real.exp 1 * max 1 β * worldlineNativeKPSum f C_wl c_wl β R_cut) :=
    le_trans h_thresh (min_le_right _ _)
  have hD_pos : 0 < 64 * Real.exp 1 * max 1 β * worldlineNativeKPSum f C_wl c_wl β R_cut := by positivity
  have h_eq : 64 * Real.exp 1 * max 1 β * J * worldlineNativeKPSum f C_wl c_wl β R_cut =
      J * (64 * Real.exp 1 * max 1 β * worldlineNativeKPSum f C_wl c_wl β R_cut) := by ring
  have h_kp_le_one : 64 * Real.exp 1 * max 1 β * J * worldlineNativeKPSum f C_wl c_wl β R_cut ≤ 1 := by
    rw [h_eq]; exact (le_div_iff₀ hD_pos).mp hJ_le
  have h_subset : Finset.univ.filter (fun γ => ¬ Disjoint (polySupport γ) W) ⊆
      W.biUnion (fun u => Finset.univ.filter (fun γ => u ∈ polySupport γ)) := fun γ hγ => by
    obtain ⟨u, hu_poly, hu_W⟩ := Finset.not_disjoint_iff.mp (Finset.mem_filter.mp hγ).2
    exact Finset.mem_biUnion.mpr ⟨u, hu_W, Finset.mem_filter.mpr ⟨Finset.mem_univ γ, hu_poly⟩⟩
  have h_phi_le : |Phi_corr_W| ≤
      64 * Real.exp 1 * max 1 β * J * worldlineNativeKPSum f C_wl c_wl β R_cut * (W.card : ℝ) := by
    calc |Phi_corr_W|
      _ ≤ ∑ γ ∈ W.biUnion (fun u => Finset.univ.filter (fun γ => u ∈ polySupport γ)), |w_ursell γ| :=
          le_trans h_phi_bound (Finset.sum_le_sum_of_subset_of_nonneg h_subset (fun _ _ _ => abs_nonneg _))
      _ ≤ ∑ u ∈ W, 64 * Real.exp 1 * max 1 β * J * worldlineNativeKPSum f C_wl c_wl β R_cut :=
          le_trans (sum_biUnion_le_of_nonneg W _ _ (fun _ => abs_nonneg _)) (Finset.sum_le_sum h_pinned_sum)
      _ = 64 * Real.exp 1 * max 1 β * J * worldlineNativeKPSum f C_wl c_wl β R_cut * (W.card : ℝ) := by
          rw [Finset.sum_const, nsmul_eq_mul, mul_comm]
  have hm_le : Phi_corr_W ≤ (W.card : ℝ) := by
    calc Phi_corr_W ≤ |Phi_corr_W| := le_abs_self _
      _ ≤ 1 * (W.card : ℝ) := le_trans h_phi_le (mul_le_mul_of_nonneg_right h_kp_le_one (Nat.cast_nonneg W.card))
      _ = (W.card : ℝ) := one_mul (W.card : ℝ)
  refine ⟨h_kp_le_one, h_phi_le, ?_⟩
  rw [h_ursell_id, mul_div_cancel_left₀ _ hZ_erased.ne']; exact Real.exp_le_exp.mpr hm_le

/-- **Truncated Direct Worldline Gibbs Failure Bound (`directWorldline_truncated_gibbsFailureProb_le`)** (Part II, Section 5.1 (`subsec:direct-worldline-synthesis`), Theorem 5.1 (`thm:direct-worldline-intact-cluster-erasure`), Equation `eq:worldline-intact-final`):
At spatial truncation cutoff `R_cut`, under the diagonal coupling threshold
`J ≤ worldlineCouplingThreshold Δ_0 Δ_RCA` and the off-diagonal Kotecký–Preiss spanning threshold
`J ≤ worldlineSpanningThreshold Δ_RCA C_wl c_wl β f R_cut` with `criticalInverseTempHier Δ_0 < β`,
if `W_cover` covers `S_safe` and each witness `W ∈ W_cover` satisfies the factorized worldline
bound (diagonal coset factor `exp(-β * (2 * Δ_0 - 6 * J * Δ_RCA) * W.card)` times the off-diagonal
Ursell erasure factor `exp(64 * e * max 1 β * J * worldlineNativeKPSum f C_wl c_wl β R_cut * W.card)`),
then combining `tubeLocal_ursell_erasure_log_ratio_le`, `walshHadamard_coset_effective_energy_gap_ge`,
`positiveWitness_gibbs_defect_sum_le`, `klarner_animal_shell_sum_bound`, and
`klarner_animal_peierls_geometric_series_bound` bounds
`gibbsFailureProb H_trunc hH_trunc β (1 - indexedBareFailureProjector sys S_safe)` by both
`2 * exp(-worldlineSuppressionRate c_wt Δ_0 Δ_RCA β J * ((L^3 : ℝ)^η))` and
`2 * exp(-(c_wt * (3 / 2) * Δ_0 * (β - criticalInverseTempHier Δ_0)) * ((L^3 : ℝ)^η))`. -/
theorem directWorldline_truncated_gibbsFailureProb_le {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    [∀ x, Nonempty (Site x)]
    {ι_chk : Type} [Fintype ι_chk] [DecidableEq ι_chk]
    (sys : IndexedCommutingProjectorHamiltonian D L Site ι_chk)
    (H_trunc : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site)
    (hH_trunc : IsSelfAdjoint H_trunc)
    (f : ℕ → ℝ) (R_cut d_min : ℕ)
    (η c_wt Δ_0 Δ_RCA C_wl c_wl β J : ℝ)
    (S_safe : Finset (ι_chk → Bool))
    (W_cover : Finset (Finset ι_chk))
    (hc_wt : 0 < c_wt) (hΔ_0 : 0 < Δ_0) (hΔ_RCA : 0 < Δ_RCA)
    (hJ_nonneg : 0 ≤ J)
    (hJ_wl : J ≤ worldlineCouplingThreshold Δ_0 Δ_RCA)
    (hJ_span : J ≤ worldlineSpanningThreshold Δ_RCA C_wl c_wl β f R_cut)
    (h_sum_pos : 0 < worldlineNativeKPSum f C_wl c_wl β R_cut)
    (hβ : criticalInverseTempHier Δ_0 < β)
    (hd_min : c_wt * (((L ^ 3 : ℕ) : ℝ) ^ η) ≤ (d_min : ℝ))
    (h_cover : IsPositiveCheckWitnessCover S_safe W_cover)
    (h_witness_raw : ∀ W ∈ W_cover,
      gibbsFailureProb H_trunc hH_trunc β (positiveCheckWitnessProj sys W) ≤
        Real.exp (-β * (2 * Δ_0 - 6 * J * Δ_RCA) * (W.card : ℝ)) *
          Real.exp (64 * Real.exp 1 * max 1 β * J *
            worldlineNativeKPSum f C_wl c_wl β R_cut * (W.card : ℝ)))
    (h_min_card : ∀ W ∈ W_cover, d_min ≤ W.card)
    (h_klarner_shell : ∀ s : ℕ,
      ((W_cover.filter (fun W => W.card = d_min + s)).card : ℝ) ≤
        klarnerAnimalConst ^ (d_min + s)) :
    gibbsFailureProb H_trunc hH_trunc β (1 - indexedBareFailureProjector sys S_safe) ≤
      2 * Real.exp (-worldlineSuppressionRate c_wt Δ_0 Δ_RCA β J * (((L ^ 3 : ℕ) : ℝ) ^ η)) ∧
    gibbsFailureProb H_trunc hH_trunc β (1 - indexedBareFailureProjector sys S_safe) ≤
      2 * Real.exp (-(c_wt * (3 / 2 : ℝ) * Δ_0 * (β - criticalInverseTempHier Δ_0)) *
        (((L ^ 3 : ℕ) : ℝ) ^ η)) := by
  have hβ_pos : 0 < β := by
    have h_gt : (1 : ℝ) < klarnerAnimalConst := by
      unfold klarnerAnimalConst; have := Real.one_le_exp zero_le_one; linarith
    have h_log : 0 < Real.log klarnerAnimalConst := Real.log_pos h_gt
    exact lt_trans (by unfold criticalInverseTempHier; positivity : 0 < criticalInverseTempHier Δ_0) hβ
  have h_kp_le_one : 64 * Real.exp 1 * max 1 β * J * worldlineNativeKPSum f C_wl c_wl β R_cut ≤ 1 := by
    have hJ_le : J ≤ 1 / (64 * Real.exp 1 * max 1 β * worldlineNativeKPSum f C_wl c_wl β R_cut) :=
      le_trans hJ_span (min_le_right _ _)
    have hD_pos : 0 < 64 * Real.exp 1 * max 1 β * worldlineNativeKPSum f C_wl c_wl β R_cut := by positivity
    have h_eq : 64 * Real.exp 1 * max 1 β * J * worldlineNativeKPSum f C_wl c_wl β R_cut =
        J * (64 * Real.exp 1 * max 1 β * worldlineNativeKPSum f C_wl c_wl β R_cut) := by ring
    rw [h_eq]; exact (le_div_iff₀ hD_pos).mp hJ_le
  have h_witness_peel : ∀ W ∈ W_cover,
      gibbsFailureProb H_trunc hH_trunc β (positiveCheckWitnessProj sys W) ≤
        Real.exp (-(worldlineSuppressionRate c_wt Δ_0 Δ_RCA β J / c_wt +
          Real.log klarnerAnimalConst) * (W.card : ℝ)) := fun W hW => by
    have h_ursell : Real.exp (64 * Real.exp 1 * max 1 β * J *
        worldlineNativeKPSum f C_wl c_wl β R_cut * (W.card : ℝ)) ≤ Real.exp (W.card : ℝ) := by
      apply Real.exp_le_exp.mpr
      calc 64 * Real.exp 1 * max 1 β * J * worldlineNativeKPSum f C_wl c_wl β R_cut * (W.card : ℝ)
        _ ≤ 1 * (W.card : ℝ) := mul_le_mul_of_nonneg_right h_kp_le_one (Nat.cast_nonneg W.card)
        _ = (W.card : ℝ) := one_mul (W.card : ℝ)
    have h_prod := mul_le_mul_of_nonneg_left h_ursell
      (Real.exp_pos (-β * (2 * Δ_0 - 6 * J * Δ_RCA) * (W.card : ℝ))).le
    have h_exp_eq : Real.exp (-β * (2 * Δ_0 - 6 * J * Δ_RCA) * (W.card : ℝ)) * Real.exp (W.card : ℝ) =
        Real.exp (-(worldlineSuppressionRate c_wt Δ_0 Δ_RCA β J / c_wt +
          Real.log klarnerAnimalConst) * (W.card : ℝ)) := by
      rw [← Real.exp_add]; congr 1; unfold worldlineSuppressionRate; field_simp [hc_wt.ne']; ring
    exact le_trans (h_witness_raw W hW) (h_exp_eq ▸ h_prod)
  have h_gap := walshHadamard_coset_effective_energy_gap_ge c_wt Δ_0 Δ_RCA β J hc_wt hΔ_0 hΔ_RCA hJ_wl hβ
  let κ := worldlineSuppressionRate c_wt Δ_0 Δ_RCA β J / c_wt + Real.log klarnerAnimalConst
  have h_animal_count := (klarner_animal_shell_sum_bound W_cover d_min κ h_min_card h_klarner_shell h_gap.2.2).1
  have h_klarner := (klarner_animal_peierls_geometric_series_bound d_min κ h_gap.2.2).2
  have h_sum := positiveWitness_gibbs_defect_sum_le sys H_trunc hH_trunc β S_safe W_cover
    (fun W => Real.exp (-κ * (W.card : ℝ))) h_cover h_witness_peel
  have h_rate_pos : 0 < worldlineSuppressionRate c_wt Δ_0 Δ_RCA β J := by
    have h_sub_pos : 0 < β - criticalInverseTempHier Δ_0 := sub_pos.mpr hβ
    exact lt_of_lt_of_le (by positivity : 0 < c_wt * (3 / 2 : ℝ) * Δ_0 * (β - criticalInverseTempHier Δ_0)) h_gap.2.1
  have h_div_nonneg : 0 ≤ worldlineSuppressionRate c_wt Δ_0 Δ_RCA β J / c_wt := div_nonneg h_rate_pos.le hc_wt.le
  have h_dmin_le : 2 * Real.exp (-(κ - Real.log klarnerAnimalConst) * (d_min : ℝ)) ≤
      2 * Real.exp (-worldlineSuppressionRate c_wt Δ_0 Δ_RCA β J * (((L ^ 3 : ℕ) : ℝ) ^ η)) := by
    have h_κ_sub : κ - Real.log klarnerAnimalConst = worldlineSuppressionRate c_wt Δ_0 Δ_RCA β J / c_wt := by dsimp [κ]; ring
    rw [h_κ_sub]
    have h1 := mul_le_mul_of_nonneg_left hd_min h_div_nonneg
    have h_eq : (worldlineSuppressionRate c_wt Δ_0 Δ_RCA β J / c_wt) * (c_wt * (((L ^ 3 : ℕ) : ℝ) ^ η)) =
        worldlineSuppressionRate c_wt Δ_0 Δ_RCA β J * (((L ^ 3 : ℕ) : ℝ) ^ η) := by field_simp [hc_wt.ne']
    exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by linarith)) (by norm_num)
  have h_main := le_trans h_sum (le_trans h_animal_count (le_trans h_klarner h_dmin_le))
  have h_vol_nonneg : (0 : ℝ) ≤ (((L ^ 3 : ℕ) : ℝ) ^ η) := by positivity
  have h_exp_le : 2 * Real.exp (-worldlineSuppressionRate c_wt Δ_0 Δ_RCA β J * (((L ^ 3 : ℕ) : ℝ) ^ η)) ≤
      2 * Real.exp (-(c_wt * (3 / 2 : ℝ) * Δ_0 * (β - criticalInverseTempHier Δ_0)) * (((L ^ 3 : ℕ) : ℝ) ^ η)) :=
    mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right (neg_le_neg h_gap.2.1) h_vol_nonneg)) (by norm_num)
  exact ⟨h_main, le_trans h_main h_exp_le⟩

/-- **Logical Character Orthogonality and Prüfer Rooted-Tree Bound (`worldline_character_projection_and_prufer_tree_bound`)**
(Part II, Section 3.5 (`subsec:worldline-expansion`), Lemma 3.9 (`lem:worldline-factorization-time-reversal`) and Proposition 3.10 (`prop:tube-local-ursell-erasure`)):
Establishes the logical character-twisted polymer weight modulus preservation
`|characterTwistedPolymerWeight w_poly μ_char ν γ| = |w_poly γ|`, the $\mathbb{Z}_2 \times \mathbb{Z}_2$
orthogonality identity `(1 / 4) * ∑ ν, logicalCharSign ν μ_0 = if μ_0 = (0, 0) then 1 else 0`,
the native collar size lower bound `(1 / 8) * |nativeCollarSupport collarChecks γ_set| ≤ worldlinePolymerSize collarChecks γ_set`,
and the Prüfer rooted-tree degree-sum identity `(pruferRootedTreeDegreeSum d_deg : ℝ) = (Nat.factorial (m_tree + 1) : ℝ)`. -/
theorem worldline_character_projection_and_prufer_tree_bound
    {ι_chk ι_poly ι_mon : Type*} [DecidableEq ι_chk] [DecidableEq ι_mon]
    (w_poly : ι_poly → ℝ)
    (μ_char : ι_poly → LogicalPauliChar) (μ_0 : LogicalPauliChar)
    (collarChecks : ι_mon → Finset ι_chk)
    (m_tree : ℕ) (d_deg : Fin (m_tree + 2) → ℕ)
    (h_deg_sum : (∑ i : Fin (m_tree + 2), d_deg i) = m_tree + 1) :
    (∀ ν : LogicalPauliChar, ∀ γ : ι_poly,
      |characterTwistedPolymerWeight w_poly μ_char ν γ| = |w_poly γ|) ∧
    (1 / 4 : ℝ) * (∑ ν : LogicalPauliChar, logicalCharSign ν μ_0) =
      (if μ_0 = (0, 0) then 1 else 0) ∧
    (∀ γ_set : Finset ι_mon,
      (1 / 8 : ℝ) * ((nativeCollarSupport collarChecks γ_set).card : ℝ) ≤
        worldlinePolymerSize collarChecks γ_set) ∧
    (pruferRootedTreeDegreeSum d_deg : ℝ) = (Nat.factorial (m_tree + 1) : ℝ) := by
  refine ⟨fun ν γ => by unfold characterTwistedPolymerWeight logicalCharSign; rw [abs_mul, abs_neg_one_pow, one_mul], ?_, ?_, ?_⟩
  · have h_univ : (Finset.univ : Finset (ZMod 2)) = {0, 1} := by decide
    have h2 : (2 : ZMod 2).val = 0 := by decide
    rw [Fintype.sum_prod_type, h_univ]; simp only [Finset.sum_pair (by decide : (0 : ZMod 2) ≠ 1)]
    rcases μ_0 with ⟨a, b⟩
    have ha : a = 0 ∨ a = 1 := by revert a; decide
    have hb : b = 0 ∨ b = 1 := by revert b; decide
    rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;> norm_num [logicalCharSign, ZMod.val_zero, ZMod.val_one, h2]
  · intro γ_set; unfold nativeCollarSupport worldlinePolymerSize
    have h_card : ((γ_set.biUnion collarChecks).card : ℝ) ≤ ∑ X ∈ γ_set, ((collarChecks X).card : ℝ) := by
      exact_mod_cast Finset.card_biUnion_le (s := γ_set) (t := collarChecks)
    have h_mul := mul_le_mul_of_nonneg_left h_card (by positivity : (0 : ℝ) ≤ 1 / 8)
    rwa [Finset.mul_sum] at h_mul
  · unfold pruferRootedTreeDegreeSum; rw [← Finset.sum_mul, h_deg_sum, ← Nat.factorial_succ]

/-- Partition erasure bound in terms of the raw polymer weight sum `∑ γ ∈ I, w γ`. -/
theorem polymerPartitionZ_sdiff_le_exp_sum_weight {Polymer : Type*} [Fintype Polymer] [DecidableEq Polymer]
    {compat : Polymer → Polymer → Prop} {w a d : Polymer → ℝ}
    (h_kp : SatisfiesKoteckyPreissCondition compat w a d)
    (Λ I : Finset Polymer) :
    polymerPartitionZ compat w Λ ≤
      Real.exp (∑ γ ∈ I, w γ) * polymerPartitionZ compat w (Λ \ I) := by
  have h_single : ∀ (S : Finset Polymer) (γ₀ : Polymer),
      polymerPartitionZ compat w S ≤ Real.exp (w γ₀) * polymerPartitionZ compat w (S.erase γ₀) := fun S γ₀ => by
    rcases h_kp with ⟨h_symm, h_irrefl, h_nonneg, _⟩
    have hw : ∀ γ : Polymer, 0 ≤ w γ := fun γ => (h_nonneg γ).1
    have hZ_erase_pos : 0 < polymerPartitionZ compat w (S.erase γ₀) := polymerPartitionZ_pos compat hw (S.erase γ₀)
    by_cases hγ₀ : γ₀ ∈ S
    · have h_rec := polymerPartitionZ_eq_erase_add compat w h_symm h_irrefl S hγ₀
      have h_sub : S.filter (fun γ => compat γ₀ γ) ⊆ S.erase γ₀ := fun γ hγ =>
        Finset.mem_erase.mpr ⟨fun h_eq => h_irrefl γ₀ (h_eq ▸ (Finset.mem_filter.mp hγ).2), (Finset.mem_filter.mp hγ).1⟩
      have hZ_mono := polymerPartitionZ_mono compat hw h_sub
      have h_one_add : 1 + w γ₀ ≤ Real.exp (w γ₀) := by linarith [Real.add_one_le_exp (w γ₀)]
      calc polymerPartitionZ compat w S
        _ = polymerPartitionZ compat w (S.erase γ₀) + w γ₀ * polymerPartitionZ compat w (S.filter (fun γ => compat γ₀ γ)) := h_rec
        _ ≤ (1 + w γ₀) * polymerPartitionZ compat w (S.erase γ₀) := by nlinarith [hw γ₀]
        _ ≤ Real.exp (w γ₀) * polymerPartitionZ compat w (S.erase γ₀) := mul_le_mul_of_nonneg_right h_one_add (le_of_lt hZ_erase_pos)
    · rw [Finset.erase_eq_of_notMem hγ₀]
      have h_one_le : 1 ≤ Real.exp (w γ₀) := Real.one_le_exp (hw γ₀)
      have hZ_nn : 0 ≤ polymerPartitionZ compat w S := le_of_lt (polymerPartitionZ_pos compat hw S)
      nlinarith
  induction I using Finset.induction_on generalizing Λ with
  | empty => simp
  | @insert γ₀ I hγ₀ ih =>
    have h_sdiff : Λ \ insert γ₀ I = (Λ.erase γ₀) \ I := by
      ext x; simp only [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_erase, not_or]; tauto
    calc polymerPartitionZ compat w Λ
      _ ≤ Real.exp (w γ₀) * polymerPartitionZ compat w (Λ.erase γ₀) := h_single Λ γ₀
      _ ≤ Real.exp (w γ₀) * (Real.exp (∑ γ ∈ I, w γ) * polymerPartitionZ compat w ((Λ.erase γ₀) \ I)) :=
          mul_le_mul_of_nonneg_left (ih (Λ.erase γ₀)) (le_of_lt (Real.exp_pos _))
      _ = Real.exp (∑ γ ∈ insert γ₀ I, w γ) * polymerPartitionZ compat w (Λ \ insert γ₀ I) := by
          rw [Finset.sum_insert hγ₀, Real.exp_add, mul_assoc, h_sdiff]

/-- **Core Direct Worldline KP and Tube-Local Ursell Erasure Witness Bound (`directWorldline_truncated_css_witness_core_bound`)**
(Part II, Section 3.5 (`subsec:worldline-expansion`), Proposition 3.10 (`prop:tube-local-ursell-erasure`) and Section 5.1 (`subsec:direct-worldline-synthesis`), Theorem 5.1 (`thm:direct-worldline-intact-cluster-erasure`)):
For any positive check witness `W` in a static 3D CSS system satisfying `TQO1` and sector-filtered
linear `TQO2`, under `J ≤ collarWalshCouplingThreshold R_cut r_0 w_0 C_RCA`,
`J ≤ worldlineCouplingThreshold (1 / 4) Δ_RCA`, and
`J ≤ worldlineSpanningThreshold Δ_RCA C_wl c_wl β f R_cut` with `16 < β`,
the Gibbs expectation of `positiveCheckWitnessProj sys W` under the scale-split truncated Hamiltonian
`sys.H0 + scaleSplitTruncatedOp V R_cut` is bounded by
`Real.exp (-(((3 / 4 : ℝ) * β - 1) * (W.card : ℝ)))`. -/
lemma directWorldline_truncated_css_witness_core_bound
    {L q_code r_0 m_max w_0 L_star R_cut : ℕ} [NeZero L]
    {C_RCA β Δ_RCA C_wl c_wl J : ℝ}
    (D_field : Box3D L → LocalCSSDescriptor q_code r_0 m_max) (h_valid : ValidDescriptorField D_field)
    (sys : SysCSS[L, q_code, m_max])
    (h_sys_checks : ∀ idx, sys.checkProj idx = staticCSSCheckProj D_field idx ∧
      sys.support idx = staticCSSCheckSupport D_field idx ∧ sys.weight idx = 1)
    (h_geom : sys.IsGeometricallyLocal r_0 w_0)
    (h_tqo1 : SatisfiesTQO1 sys L_star) (h_tqo2 : SatisfiesSectorFilteredLinearTQO2 sys 1 L_star C_RCA)
    (V : QuasiLocalPerturbation 3 L (SiteCSS[L, q_code])) (f : ℕ → ℝ)
    (hf_nn : ∀ r, 0 ≤ f r) (hf_le_one : ∀ r, f r ≤ 1)
    (hV_norm : ∀ r ∈ Finset.Icc 1 (min R_cut L), ∀ A ∈ boxCubes 3 L r, ‖V.term r A‖ ≤ J * f r)
    (hH_trunc : IsSelfAdjoint (sys.H0 + scaleSplitTruncatedOp V R_cut))
    (hR_cut : 1 ≤ R_cut) (hR_le : R_cut ≤ L_star) (h_scale_cal : SatisfiesWorldlineScaleCalibration L L_star R_cut r_0 C_RCA) (hC_RCA : 0 ≤ C_RCA)
    (h_rca_cal : rcaDiagonalCoercivityConstant 3 R_cut r_0 w_0 C_RCA ≤ Δ_RCA)
    (hC_wl_cal : (kpCollarMaxCheckCard R_cut r_0 w_0 C_RCA : ℝ) ≤ C_wl)
    (hc_wl_cal : (kpCollarMaxCheckCard R_cut r_0 w_0 C_RCA : ℝ) ≤ c_wl)
    (hΔ_RCA : 0 < Δ_RCA) (hβ : 16 < β) (hJ : 0 ≤ J)
    (h_sum_pos : 0 < worldlineNativeKPSum f C_wl c_wl β R_cut)
    (hJ_walsh : J ≤ collarWalshCouplingThreshold R_cut r_0 w_0 C_RCA)
    (hJ_wl : J ≤ worldlineCouplingThreshold (1 / 4) Δ_RCA)
    (h_thresh : J ≤ worldlineSpanningThreshold Δ_RCA C_wl c_wl β f R_cut)
    (W : Finset (IdxCSS[L, q_code, m_max]))
    (hW_valid : (fun idx => decide (idx ∈ W)) ∈ realizableSyndromes D_field) :
    gibbsFailureProb (sys.H0 + scaleSplitTruncatedOp V R_cut) hH_trunc β
      (positiveCheckWitnessProj sys W) ≤
      Real.exp (-(((3 / 4 : ℝ) * β - 1) * (W.card : ℝ))) :=
  worldline_zero_spillover_witness_gibbs_bound
    D_field h_valid sys h_sys_checks h_geom h_tqo1 h_tqo2 V f hf_nn hf_le_one hV_norm hH_trunc
    hR_cut hR_le h_scale_cal hC_RCA h_rca_cal hC_wl_cal hc_wl_cal hΔ_RCA hβ hJ h_sum_pos hJ_walsh hJ_wl h_thresh W hW_valid

/-- **Direct Worldline KP and Tube-Local Ursell Erasure Witness Bound (`directWorldline_truncated_css_witness_exp_bound`)**
(Part II, Section 3.5 (`subsec:worldline-expansion`), Proposition 3.10 (`prop:tube-local-ursell-erasure`) and Section 5.1 (`subsec:direct-worldline-synthesis`), Theorem 5.1 (`thm:direct-worldline-intact-cluster-erasure`)):
For any positive check witness `W` in a static 3D CSS system satisfying `TQO1` and sector-filtered
linear `TQO2`, under `J ≤ collarWalshCouplingThreshold R_cut r_0 w_0 C_RCA`,
`J ≤ worldlineCouplingThreshold Δ_0 Δ_RCA`, and
`J ≤ worldlineSpanningThreshold Δ_RCA C_wl c_wl β f R_cut` with `criticalInverseTempHier Δ_0 < β`,
the Gibbs expectation of `positiveCheckWitnessProj sys W` under the scale-split truncated Hamiltonian
`sys.H0 + scaleSplitTruncatedOp V R_cut` is bounded by
`Real.exp (-β * (2 * Δ_0 - 6 * J * Δ_RCA) * (W.card : ℝ))`. -/
lemma directWorldline_truncated_css_witness_exp_bound
    {L q_code r_0 m_max w_0 L_star R_cut : ℕ} [NeZero L]
    {C_RCA β Δ_0 Δ_RCA C_wl c_wl J : ℝ}
    (D_field : Box3D L → LocalCSSDescriptor q_code r_0 m_max) (h_valid : ValidDescriptorField D_field)
    (sys : SysCSS[L, q_code, m_max])
    (h_sys_checks : ∀ idx, sys.checkProj idx = staticCSSCheckProj D_field idx ∧
      sys.support idx = staticCSSCheckSupport D_field idx ∧ sys.weight idx = 1)
    (h_geom : sys.IsGeometricallyLocal r_0 w_0)
    (h_tqo1 : SatisfiesTQO1 sys L_star) (h_tqo2 : SatisfiesSectorFilteredLinearTQO2 sys 1 L_star C_RCA)
    (V : QuasiLocalPerturbation 3 L (SiteCSS[L, q_code])) (f : ℕ → ℝ)
    (hf_super : InPerturbationClassSuper f) (h_ql : HasQuasiLocalDecayBound V J f)
    (hH_trunc : IsSelfAdjoint (sys.H0 + scaleSplitTruncatedOp V R_cut))
    (hR_cut : 1 ≤ R_cut) (hR_le : R_cut ≤ L_star) (h_scale_cal : SatisfiesWorldlineScaleCalibration L L_star R_cut r_0 C_RCA) (hC_RCA : 0 ≤ C_RCA)
    (h_rca_cal : rcaDiagonalCoercivityConstant 3 R_cut r_0 w_0 C_RCA ≤ Δ_RCA)
    (hC_wl_cal : (kpCollarMaxCheckCard R_cut r_0 w_0 C_RCA : ℝ) ≤ C_wl)
    (hc_wl_cal : (kpCollarMaxCheckCard R_cut r_0 w_0 C_RCA : ℝ) ≤ c_wl)
    (hΔ_0 : 0 < Δ_0) (hΔ_0_le : Δ_0 ≤ 1 / 4) (hΔ_RCA : 0 < Δ_RCA)
    (hβ : criticalInverseTempHier Δ_0 < β) (hJ : 0 ≤ J)
    (h_sum_pos : 0 < worldlineNativeKPSum f C_wl c_wl β R_cut)
    (hJ_walsh : J ≤ collarWalshCouplingThreshold R_cut r_0 w_0 C_RCA)
    (hJ_wl : J ≤ worldlineCouplingThreshold Δ_0 Δ_RCA)
    (h_thresh : J ≤ worldlineSpanningThreshold Δ_RCA C_wl c_wl β f R_cut)
    (W : Finset (IdxCSS[L, q_code, m_max]))
    (hW_valid : (fun idx => decide (idx ∈ W)) ∈ realizableSyndromes D_field) :
    gibbsFailureProb (sys.H0 + scaleSplitTruncatedOp V R_cut) hH_trunc β
      (positiveCheckWitnessProj sys W) ≤
      Real.exp (-β * (2 * Δ_0 - 6 * J * Δ_RCA) * (W.card : ℝ)) := by
  have h_24_le : 24 ≤ criticalInverseTempHier Δ_0 :=
    twenty_four_le_criticalInverseTempHier hΔ_0 hΔ_0_le
  have hβ_gt_16 : 16 < β := by linarith
  have hf_le_one : ∀ r, f r ≤ 1 := inPerturbationClassSuper_le_one hf_super
  have hV_norm : ∀ r ∈ Finset.Icc 1 (min R_cut L), ∀ A ∈ boxCubes 3 L r, ‖V.term r A‖ ≤ J * f r := by
    intro r hr A hA
    have hr_L : r ∈ Finset.Icc 1 L := Finset.mem_Icc.mpr
      ⟨(Finset.mem_Icc.mp hr).1, le_trans (Finset.mem_Icc.mp hr).2 (Nat.min_le_right R_cut L)⟩
    exact (h_ql.1 r hr_L A hA).2
  have hJ_wl_quarter : J ≤ worldlineCouplingThreshold (1 / 4) Δ_RCA := by
    unfold worldlineCouplingThreshold at hJ_wl ⊢
    exact le_trans hJ_wl (div_le_div_of_nonneg_right hΔ_0_le (by positivity))
  have h_core := directWorldline_truncated_css_witness_core_bound
    D_field h_valid sys h_sys_checks h_geom h_tqo1 h_tqo2 V f hf_super.1 hf_le_one hV_norm hH_trunc
    hR_cut hR_le h_scale_cal hC_RCA h_rca_cal hC_wl_cal hc_wl_cal hΔ_RCA hβ_gt_16 hJ h_sum_pos hJ_walsh hJ_wl_quarter h_thresh W hW_valid
  refine le_trans h_core (Real.exp_le_exp.mpr ?_)
  have h_rate_le : β * (2 * Δ_0 - 6 * J * Δ_RCA) ≤ (3 / 4 : ℝ) * β - 1 := by
    have h1 : 2 * Δ_0 - 6 * J * Δ_RCA ≤ 1 / 2 := by nlinarith
    nlinarith
  have h_mul := mul_le_mul_of_nonneg_right h_rate_le (Nat.cast_nonneg W.card)
  linarith

theorem directWorldline_truncated_css_witness_gibbsFailureProb_le
    {L q_code r_0 m_max w_0 L_star R_cut : ℕ} [NeZero L]
    {C_RCA β Δ_0 Δ_RCA C_wl c_wl J : ℝ}
    (D_field : Box3D L → LocalCSSDescriptor q_code r_0 m_max) (h_valid : ValidDescriptorField D_field)
    (sys : SysCSS[L, q_code, m_max])
    (h_sys_checks : ∀ idx, sys.checkProj idx = staticCSSCheckProj D_field idx ∧
      sys.support idx = staticCSSCheckSupport D_field idx ∧ sys.weight idx = 1)
    (h_geom : sys.IsGeometricallyLocal r_0 w_0)
    (h_tqo1 : SatisfiesTQO1 sys L_star) (h_tqo2 : SatisfiesSectorFilteredLinearTQO2 sys 1 L_star C_RCA)
    (V : QuasiLocalPerturbation 3 L (SiteCSS[L, q_code])) (f : ℕ → ℝ)
    (hf_super : InPerturbationClassSuper f) (h_ql : HasQuasiLocalDecayBound V J f)
    (hH_trunc : IsSelfAdjoint (sys.H0 + scaleSplitTruncatedOp V R_cut))
    (hR_cut : 1 ≤ R_cut) (hR_le : R_cut ≤ L_star) (h_scale_cal : SatisfiesWorldlineScaleCalibration L L_star R_cut r_0 C_RCA) (hC_RCA : 0 ≤ C_RCA)
    (h_rca_cal : rcaDiagonalCoercivityConstant 3 R_cut r_0 w_0 C_RCA ≤ Δ_RCA)
    (hC_wl_cal : (kpCollarMaxCheckCard R_cut r_0 w_0 C_RCA : ℝ) ≤ C_wl)
    (hc_wl_cal : (kpCollarMaxCheckCard R_cut r_0 w_0 C_RCA : ℝ) ≤ c_wl)
    (hΔ_0 : 0 < Δ_0) (hΔ_0_le : Δ_0 ≤ 1 / 4) (hΔ_RCA : 0 < Δ_RCA)
    (hβ : criticalInverseTempHier Δ_0 < β) (hJ : 0 ≤ J)
    (h_sum_pos : 0 < worldlineNativeKPSum f C_wl c_wl β R_cut)
    (hJ_walsh : J ≤ collarWalshCouplingThreshold R_cut r_0 w_0 C_RCA)
    (hJ_wl : J ≤ worldlineCouplingThreshold Δ_0 Δ_RCA)
    (h_thresh : J ≤ worldlineSpanningThreshold Δ_RCA C_wl c_wl β f R_cut)
    (W : Finset (IdxCSS[L, q_code, m_max]))
    (hW_valid : (fun idx => decide (idx ∈ W)) ∈ realizableSyndromes D_field) :
    gibbsFailureProb (sys.H0 + scaleSplitTruncatedOp V R_cut) hH_trunc β
      (positiveCheckWitnessProj sys W) ≤
      Real.exp (-β * (2 * Δ_0 - 6 * J * Δ_RCA) * (W.card : ℝ)) ∧
    gibbsFailureProb (sys.H0 + scaleSplitTruncatedOp V R_cut) hH_trunc β
      (positiveCheckWitnessProj sys W) ≤
      Real.exp (-β * (2 * Δ_0 - 6 * J * Δ_RCA) * (W.card : ℝ)) *
        Real.exp (64 * Real.exp 1 * max 1 β * J *
          worldlineNativeKPSum f C_wl c_wl β R_cut * (W.card : ℝ)) := by
  have h_bound1 := directWorldline_truncated_css_witness_exp_bound
    D_field h_valid sys h_sys_checks h_geom h_tqo1 h_tqo2 V f hf_super h_ql hH_trunc
    hR_cut hR_le h_scale_cal hC_RCA h_rca_cal hC_wl_cal hc_wl_cal hΔ_0 hΔ_0_le hΔ_RCA hβ hJ h_sum_pos hJ_walsh hJ_wl h_thresh W hW_valid
  have h_one_le :
      1 ≤ Real.exp (64 * Real.exp 1 * max 1 β * J *
        worldlineNativeKPSum f C_wl c_wl β R_cut * (W.card : ℝ)) :=
    Real.one_le_exp (by positivity)
  exact ⟨h_bound1, le_trans h_bound1 (le_mul_of_one_le_right (Real.exp_pos _).le h_one_le)⟩

private lemma abstract_cell_kp_majorant {Cell ι_poly ι_chk : Type*} [Fintype Cell] [DecidableEq Cell] [Fintype ι_poly] [DecidableEq ι_poly] [DecidableEq ι_chk]
    (adj : Cell → Cell → Prop) [DecidableRel adj] (h_refl : ∀ u : Cell, adj u u) (h_symm : ∀ u v : Cell, adj u v → adj v u)
    {D_adj : ℕ} (hD_ge : 16 ≤ D_adj) (h_deg : ∀ u : Cell, (Finset.univ.filter (adj u)).card ≤ D_adj)
    (S_stat S_jump supp : ι_poly → Finset Cell) (h_supp : ∀ γ, supp γ = S_stat γ ∪ S_jump γ) (compat : ι_poly → ι_poly → Prop)
    (h_compat : ∀ γ₁ γ₂, compat γ₁ γ₂ ↔ Disjoint (supp γ₁) (supp γ₂) ∧ ∀ u ∈ supp γ₁, ∀ v ∈ supp γ₂, ¬adj u v)
    (h_disj : ∀ γ, Disjoint (S_stat γ) (S_jump γ)) (h_nonempty : ∀ γ, (supp γ).Nonempty) (h_conn : ∀ γ, KPIsConnectedSubgraph adj (supp γ))
    (h_inj_poly : ∀ γ₁ γ₂, S_stat γ₁ = S_stat γ₂ → S_jump γ₁ = S_jump γ₂ → γ₁ = γ₂) (w_poly : ι_poly → ℝ) (hw_nn : ∀ γ, 0 ≤ w_poly γ)
    (hw_le : ∀ γ, w_poly γ ≤ (1 / (8 * (Real.exp 1) ^ 2 * (D_adj : ℝ) ^ 3)) ^ (supp γ).card) (W : Finset ι_chk) (cellOf : ι_chk → Cell)
    {inst_incompat : ∀ Γ_pin : Finset ι_poly, DecidablePred (fun γ' => ∃ γ ∈ Γ_pin, ¬compat γ γ')}
    {inst_compat : ∀ Γ_pin : Finset ι_poly, DecidablePred (fun γ' => ∀ γ ∈ Γ_pin, compat γ γ')}
    {inst_W : DecidablePred (fun γ : ι_poly => ∃ c ∈ W, cellOf c ∈ supp γ)} {inst_not_W : DecidablePred (fun γ : ι_poly => ¬∃ c ∈ W, cellOf c ∈ supp γ)} :
    ∃ (a_poly d_poly : ι_poly → ℝ), (∀ γ : ι_poly, ((supp γ).card : ℝ) ≤ a_poly γ ∧ ((supp γ).card : ℝ) ≤ d_poly γ) ∧
      SatisfiesKoteckyPreissCondition compat w_poly a_poly d_poly ∧
      (∀ (Γ_vac Γ_pin : Finset ι_poly), polymerPartitionZ compat w_poly Γ_vac ≤
        Real.exp (∑ γ' ∈ @Finset.filter ι_poly (fun γ' => ∃ γ ∈ Γ_pin, ¬compat γ γ') (inst_incompat Γ_pin) Γ_vac, a_poly γ') *
          polymerPartitionZ compat w_poly (@Finset.filter ι_poly (fun γ' => ∀ γ ∈ Γ_pin, compat γ γ') (inst_compat Γ_pin) Γ_vac)) ∧
      (∀ (Γ_pin : Finset ι_poly), IsCompatiblePolymerSet compat Γ_pin →
        polymerPinnedSum compat w_poly Finset.univ Γ_pin ≤ Real.exp (-(∑ γ ∈ Γ_pin, d_poly γ)) * polymerPartitionZ compat w_poly Finset.univ) ∧
      Real.exp (∑ γ ∈ @Finset.filter ι_poly (fun γ : ι_poly => ∃ c ∈ W, cellOf c ∈ supp γ) inst_W Finset.univ, w_poly γ * Real.exp (a_poly γ + d_poly γ)) ≤
        Real.exp ((1 / 2 : ℝ) * (W.card : ℝ)) ∧
      polymerPartitionZ compat w_poly Finset.univ / polymerPartitionZ compat w_poly
        (@Finset.filter ι_poly (fun γ : ι_poly => ¬∃ c ∈ W, cellOf c ∈ supp γ) inst_not_W Finset.univ) ≤ Real.exp (W.card : ℝ) := by
  let a_poly : ι_poly → ℝ := fun γ => ((supp γ).card : ℝ); let d_poly : ι_poly → ℝ := fun γ => ((supp γ).card : ℝ)
  let ε : ℝ := 1 / (8 * (Real.exp 1) ^ 2 * (D_adj : ℝ) ^ 3)
  have hD_pos : 0 < (D_adj : ℝ) := Nat.cast_pos.mpr (lt_of_lt_of_le (by decide : 0 < 16) hD_ge)
  have h_term_nn : ∀ γ : ι_poly, 0 ≤ w_poly γ * Real.exp (a_poly γ + d_poly γ) := fun γ => mul_nonneg (hw_nn γ) (le_of_lt (Real.exp_pos _))
  have hw_exp_le : ∀ γ : ι_poly, w_poly γ * Real.exp (a_poly γ + d_poly γ) ≤ (ε * (Real.exp 1) ^ 2) ^ (supp γ).card := fun γ => by
    have h_exp_eq : Real.exp (a_poly γ + d_poly γ) = ((Real.exp 1) ^ 2) ^ (supp γ).card := by dsimp [a_poly, d_poly]; rw [← pow_mul, ← Real.exp_nat_mul]; congr 1; push_cast; ring
    rw [h_exp_eq, mul_pow]; exact mul_le_mul_of_nonneg_right (hw_le γ) (by positivity)
  have h_card_supp_le : ∀ S : Finset Cell, ((Finset.univ.filter (fun γ : ι_poly => supp γ = S)).card : ℝ) ≤ (2 : ℝ) ^ S.card := fun S => by
    have h_inj : Set.InjOn S_stat (↑(Finset.univ.filter (fun γ : ι_poly => supp γ = S))) := fun γ₁ hγ₁ γ₂ hγ₂ h_stat_eq => by
      have h_j1 : S_jump γ₁ = S \ S_stat γ₁ := by rw [← (h_supp γ₁).symm.trans (Finset.mem_filter.mp hγ₁).2, Finset.union_sdiff_cancel_left (h_disj γ₁)]
      have h_j2 : S_jump γ₂ = S \ S_stat γ₂ := by rw [← (h_supp γ₂).symm.trans (Finset.mem_filter.mp hγ₂).2, Finset.union_sdiff_cancel_left (h_disj γ₂)]
      exact h_inj_poly γ₁ γ₂ h_stat_eq (by rw [h_j1, h_j2, h_stat_eq])
    have h_maps : Set.MapsTo S_stat (↑(Finset.univ.filter (fun γ : ι_poly => supp γ = S))) (↑S.powerset) := fun γ hγ => by
      rw [Finset.mem_coe, Finset.mem_powerset, ← (h_supp γ).symm.trans (Finset.mem_filter.mp hγ).2]; exact Finset.subset_union_left
    have h_nat := Finset.card_le_card_of_injOn S_stat h_maps h_inj; rw [Finset.card_powerset] at h_nat; exact_mod_cast h_nat
  have h_cell_sum : ∀ v : Cell, (∑ γ ∈ Finset.univ.filter (fun γ : ι_poly => v ∈ supp γ), w_poly γ * Real.exp (a_poly γ + d_poly γ)) ≤ 1 / (2 * (D_adj : ℝ)) := fun v => by
    let N_cells := Fintype.card Cell; let fib (S : Finset Cell) := Finset.univ.filter (fun γ : ι_poly => supp γ = S)
    let connSets (m : ℕ) := Finset.univ.filter (fun S : Finset Cell => v ∈ S ∧ S.card = m ∧ KPIsConnectedSubgraph adj S)
    have h_sub_m : Finset.univ.filter (fun γ : ι_poly => v ∈ supp γ) ⊆ (Finset.Icc 1 N_cells).biUnion (fun m => (connSets m).biUnion fib) := fun γ hγ => by
      have hv_in : v ∈ supp γ := (Finset.mem_filter.mp hγ).2
      exact Finset.mem_biUnion.mpr ⟨(supp γ).card, Finset.mem_Icc.mpr ⟨Finset.card_pos.mpr ⟨v, hv_in⟩, Finset.card_le_univ (supp γ)⟩,
        Finset.mem_biUnion.mpr ⟨supp γ, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hv_in, rfl, h_conn γ⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ γ, rfl⟩⟩⟩
    let r_ratio : ℝ := 1 / (4 * (D_adj : ℝ))
    have h_m_bound : ∀ m ∈ Finset.Icc 1 N_cells, (∑ γ ∈ (connSets m).biUnion fib, w_poly γ * Real.exp (a_poly γ + d_poly γ)) ≤ r_ratio ^ m := fun m hm => by
      have h_S_bound : ∀ S ∈ connSets m, (∑ γ ∈ fib S, w_poly γ * Real.exp (a_poly γ + d_poly γ)) ≤ (2 * (Real.exp 1) ^ 2 * ε) ^ m := fun S hS => by
        have hS_m : S.card = m := (Finset.mem_filter.mp hS).2.2.1
        have h_each : ∀ γ ∈ fib S, w_poly γ * Real.exp (a_poly γ + d_poly γ) ≤ (ε * (Real.exp 1) ^ 2) ^ m := fun γ hγ => by
          have h_le := hw_exp_le γ; rwa [(Finset.mem_filter.mp hγ).2, hS_m] at h_le
        have h_sum_S := Finset.sum_le_card_nsmul (fib S) _ ((ε * (Real.exp 1) ^ 2) ^ m) h_each; rw [nsmul_eq_mul] at h_sum_S
        have h_card_S := h_card_supp_le S; rw [hS_m] at h_card_S
        calc (∑ γ ∈ fib S, w_poly γ * Real.exp (a_poly γ + d_poly γ)) ≤ (2 : ℝ) ^ m * (ε * (Real.exp 1) ^ 2) ^ m := le_trans h_sum_S (mul_le_mul_of_nonneg_right h_card_S (by positivity))
          _ = (2 * (Real.exp 1) ^ 2 * ε) ^ m := by rw [← mul_pow]; congr 1; ring
      have h_klarner : ((connSets m).card : ℝ) ≤ ((D_adj : ℝ) ^ 2) ^ m :=
        (kp_klarner_connected_polymer_count_le adj h_symm (by omega : 4 ≤ D_adj) h_deg v (Finset.mem_Icc.mp hm).1 zero_le_one).1
      have h_b1 := sum_biUnion_le_of_nonneg (connSets m) fib _ h_term_nn
      have h_b2 := Finset.sum_le_card_nsmul (connSets m) (fun S => ∑ γ ∈ fib S, w_poly γ * Real.exp (a_poly γ + d_poly γ)) ((2 * (Real.exp 1) ^ 2 * ε) ^ m) h_S_bound
      rw [nsmul_eq_mul] at h_b2; have h_base_eq : (D_adj : ℝ) ^ 2 * (2 * (Real.exp 1) ^ 2 * ε) = r_ratio := by dsimp [ε, r_ratio]; have := ne_of_gt (Real.exp_pos 1); have := ne_of_gt hD_pos; field_simp; ring
      calc (∑ γ ∈ (connSets m).biUnion fib, w_poly γ * Real.exp (a_poly γ + d_poly γ))
        _ ≤ ((D_adj : ℝ) ^ 2) ^ m * (2 * (Real.exp 1) ^ 2 * ε) ^ m := le_trans (le_trans h_b1 h_b2) (mul_le_mul_of_nonneg_right h_klarner (by positivity))
        _ = r_ratio ^ m := by rw [← mul_pow, h_base_eq]
    have hr_nn : 0 ≤ r_ratio := by dsimp [r_ratio]; positivity
    have hr_le_half : r_ratio ≤ 1 / 2 := by dsimp [r_ratio]; rw [div_le_div_iff₀ (by positivity) (by norm_num)]; have : (16 : ℝ) ≤ (D_adj : ℝ) := Nat.cast_le.mpr hD_ge; linarith
    have h_step1 := Finset.sum_le_sum_of_subset_of_nonneg (f := fun γ : ι_poly => w_poly γ * Real.exp (a_poly γ + d_poly γ)) h_sub_m fun γ _ _ => h_term_nn γ
    have h_step2 := sum_biUnion_le_of_nonneg (Finset.Icc 1 N_cells) (fun m => (connSets m).biUnion fib) _ h_term_nn
    calc (∑ γ ∈ Finset.univ.filter (fun γ : ι_poly => v ∈ supp γ), w_poly γ * Real.exp (a_poly γ + d_poly γ))
      _ ≤ ∑ m ∈ Finset.Icc 1 N_cells, r_ratio ^ m := le_trans (le_trans h_step1 h_step2) (Finset.sum_le_sum h_m_bound)
      _ ≤ 2 * r_ratio := sum_Icc_pow_le_two_mul hr_nn hr_le_half N_cells
      _ = 1 / (2 * (D_adj : ℝ)) := by dsimp [r_ratio]; ring
  have h_kp : SatisfiesKoteckyPreissCondition compat w_poly a_poly d_poly := by
    refine ⟨fun γ₁ γ₂ h12 => ?_, fun γ h_self => ?_, fun γ => ⟨hw_nn γ, Nat.cast_nonneg _, Nat.cast_nonneg _⟩, fun γ => ?_⟩
    · rcases (h_compat γ₁ γ₂).mp h12 with ⟨h1, h2⟩; exact (h_compat γ₂ γ₁).mpr ⟨h1.symm, fun u hu v hv huv => h2 v hv u hu (h_symm u v huv)⟩
    · rcases (h_compat γ γ).mp h_self with ⟨h_disj_self, _⟩; rcases h_nonempty γ with ⟨u, hu⟩; exact Finset.disjoint_left.mp h_disj_self hu hu
    · let nbrs (u : Cell) := Finset.univ.filter (adj u); let cellPolys (v : Cell) := Finset.univ.filter (fun γ' : ι_poly => v ∈ supp γ')
      have h_sub_incompat : Finset.univ.filter (fun γ' : ι_poly => ¬compat γ γ') ⊆ (supp γ).biUnion (fun u => (nbrs u).biUnion cellPolys) := fun γ' hγ' => by
        have h_not : ¬(Disjoint (supp γ) (supp γ') ∧ ∀ u ∈ supp γ, ∀ v ∈ supp γ', ¬adj u v) := fun h => (Finset.mem_filter.mp hγ').2 ((h_compat γ γ').mpr h)
        rw [not_and_or] at h_not; rcases h_not with h_ndisj | h_nadj
        · rcases Finset.not_disjoint_iff.mp h_ndisj with ⟨u, hu, hu'⟩
          exact Finset.mem_biUnion.mpr ⟨u, hu, Finset.mem_biUnion.mpr ⟨u, Finset.mem_filter.mpr ⟨Finset.mem_univ u, h_refl u⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ γ', hu'⟩⟩⟩
        · push_neg at h_nadj; rcases h_nadj with ⟨u, hu, v, hv', huv⟩
          exact Finset.mem_biUnion.mpr ⟨u, hu, Finset.mem_biUnion.mpr ⟨v, Finset.mem_filter.mpr ⟨Finset.mem_univ v, huv⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ γ', hv'⟩⟩⟩
      have h_u_bound : ∀ u ∈ supp γ, (∑ γ' ∈ (nbrs u).biUnion cellPolys, w_poly γ' * Real.exp (a_poly γ' + d_poly γ')) ≤ 1 := fun u _ => by
        have h_b1 := sum_biUnion_le_of_nonneg (nbrs u) cellPolys _ h_term_nn
        have h_b2 := Finset.sum_le_card_nsmul (nbrs u) (fun v => ∑ γ' ∈ cellPolys v, w_poly γ' * Real.exp (a_poly γ' + d_poly γ')) (1 / (2 * (D_adj : ℝ))) fun v _ => h_cell_sum v
        rw [nsmul_eq_mul] at h_b2; have h_deg_u : ((nbrs u).card : ℝ) ≤ (D_adj : ℝ) := Nat.cast_le.mpr (h_deg u)
        have h_prod : ((nbrs u).card : ℝ) * (1 / (2 * (D_adj : ℝ))) ≤ 1 := by
          calc ((nbrs u).card : ℝ) * (1 / (2 * (D_adj : ℝ))) ≤ (D_adj : ℝ) * (1 / (2 * (D_adj : ℝ))) := mul_le_mul_of_nonneg_right h_deg_u (by positivity)
            _ = 1 / 2 := by field_simp [ne_of_gt hD_pos]
            _ ≤ 1 := by norm_num
        exact le_trans (le_trans h_b1 h_b2) h_prod
      have h_s1 := Finset.sum_le_sum_of_subset_of_nonneg (f := fun γ' : ι_poly => w_poly γ' * Real.exp (a_poly γ' + d_poly γ')) h_sub_incompat fun γ' _ _ => h_term_nn γ'
      have h_s2 := sum_biUnion_le_of_nonneg (supp γ) (fun u => (nbrs u).biUnion cellPolys) _ h_term_nn
      have h_s3 := Finset.sum_le_card_nsmul (supp γ) (fun u => ∑ γ' ∈ (nbrs u).biUnion cellPolys, w_poly γ' * Real.exp (a_poly γ' + d_poly γ')) 1 h_u_bound
      rw [nsmul_eq_mul, mul_one] at h_s3; exact le_trans h_s1 (le_trans h_s2 h_s3)
  let I := @Finset.filter ι_poly (fun γ : ι_poly => ∃ c ∈ W, cellOf c ∈ supp γ) inst_W Finset.univ
  have h_W_sum : (∑ γ ∈ I, w_poly γ * Real.exp (a_poly γ + d_poly γ)) ≤ (1 / 2 : ℝ) * (W.card : ℝ) := by
    let wPolys (c : ι_chk) := Finset.univ.filter (fun γ : ι_poly => cellOf c ∈ supp γ)
    have h_sub_W : I ⊆ W.biUnion wPolys := fun γ hγ => by
      rcases (@Finset.mem_filter _ _ inst_W _ _).mp hγ with ⟨_, c, hc, h_in⟩; exact Finset.mem_biUnion.mpr ⟨c, hc, Finset.mem_filter.mpr ⟨Finset.mem_univ γ, h_in⟩⟩
    have h_c_half : ∀ c ∈ W, (∑ γ ∈ wPolys c, w_poly γ * Real.exp (a_poly γ + d_poly γ)) ≤ 1 / 2 := fun c _ => by
      refine le_trans (h_cell_sum (cellOf c)) ?_; rw [div_le_div_iff₀ (by positivity) (by norm_num)]; have : (16 : ℝ) ≤ (D_adj : ℝ) := Nat.cast_le.mpr hD_ge; linarith
    have h_s1 := Finset.sum_le_sum_of_subset_of_nonneg (f := fun γ : ι_poly => w_poly γ * Real.exp (a_poly γ + d_poly γ)) h_sub_W fun γ _ _ => h_term_nn γ
    have h_s2 := sum_biUnion_le_of_nonneg W wPolys _ h_term_nn
    have h_s3 := Finset.sum_le_card_nsmul W (fun c => ∑ γ ∈ wPolys c, w_poly γ * Real.exp (a_poly γ + d_poly γ)) (1 / 2) h_c_half
    rw [nsmul_eq_mul, mul_comm] at h_s3; exact le_trans h_s1 (le_trans h_s2 h_s3)
  have hw_exp_le_one : ∀ γ : ι_poly, w_poly γ * Real.exp (a_poly γ + d_poly γ) ≤ 1 := fun γ => by
    rcases h_nonempty γ with ⟨v, hv⟩
    have h_in : γ ∈ Finset.univ.filter (fun γ' : ι_poly => v ∈ supp γ') := Finset.mem_filter.mpr ⟨Finset.mem_univ γ, hv⟩
    have h_le_sum := Finset.single_le_sum (f := fun γ' : ι_poly => w_poly γ' * Real.exp (a_poly γ' + d_poly γ')) (fun γ' _ => h_term_nn γ') h_in
    have h_le_half : (1 / (2 * (D_adj : ℝ))) ≤ 1 := by rw [div_le_iff₀ (by positivity)]; have : (16 : ℝ) ≤ (D_adj : ℝ) := Nat.cast_le.mpr hD_ge; linarith
    exact le_trans h_le_sum (le_trans (h_cell_sum v) h_le_half)
  have h_sdiff_vac : ∀ (Γ_vac Γ_pin : Finset ι_poly), polymerPartitionZ compat w_poly Γ_vac ≤
      Real.exp (∑ γ' ∈ @Finset.filter ι_poly (fun γ' => ∃ γ ∈ Γ_pin, ¬compat γ γ') (inst_incompat Γ_pin) Γ_vac, a_poly γ') *
        polymerPartitionZ compat w_poly (@Finset.filter ι_poly (fun γ' => ∀ γ ∈ Γ_pin, compat γ γ') (inst_compat Γ_pin) Γ_vac) := fun Γ_vac Γ_pin => by
    let I_pin := @Finset.filter ι_poly (fun γ' => ∃ γ ∈ Γ_pin, ¬compat γ γ') (inst_incompat Γ_pin) Γ_vac
    have h_eq : Γ_vac \ I_pin = @Finset.filter ι_poly (fun γ' => ∀ γ ∈ Γ_pin, compat γ γ') (inst_compat Γ_pin) Γ_vac := by
      ext γ'; simp only [I_pin, Finset.mem_sdiff, @Finset.mem_filter _ _ (inst_incompat Γ_pin), @Finset.mem_filter _ _ (inst_compat Γ_pin), not_and, not_exists, not_not]; tauto
    rw [← h_eq]; exact kotecky_preiss_partition_sdiff_le h_kp Γ_vac I_pin
  refine ⟨a_poly, d_poly, fun _ => ⟨le_rfl, le_rfl⟩, h_kp, h_sdiff_vac,
    fun Γ_pin h_pin => kotecky_preiss_pinned_witness_bound h_kp Γ_pin h_pin (fun γ _ => hw_exp_le_one γ), Real.exp_le_exp.mpr h_W_sum, ?_⟩
  have h_sdiff_eq : @Finset.filter ι_poly (fun γ : ι_poly => ¬∃ c ∈ W, cellOf c ∈ supp γ) inst_not_W Finset.univ = Finset.univ \ I := by
    ext γ; simp only [I, Finset.mem_sdiff, @Finset.mem_filter _ _ inst_not_W, @Finset.mem_filter _ _ inst_W, Finset.mem_univ, true_and]
  rw [h_sdiff_eq]; have hZ_pos : 0 < polymerPartitionZ compat w_poly (Finset.univ \ I) := polymerPartitionZ_pos compat hw_nn (Finset.univ \ I)
  rw [div_le_iff₀ hZ_pos]; have h_erasure := polymerPartitionZ_sdiff_le_exp_sum_weight h_kp Finset.univ I
  have h_w_le_W : (∑ γ ∈ I, w_poly γ) ≤ (W.card : ℝ) := by
    have h_le_exp : ∀ γ ∈ I, w_poly γ ≤ w_poly γ * Real.exp (a_poly γ + d_poly γ) := fun γ _ =>
      le_mul_of_one_le_right (hw_nn γ) (Real.one_le_exp (add_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)))
    have h1 := le_trans (Finset.sum_le_sum h_le_exp) h_W_sum; have h2 : (0 : ℝ) ≤ (W.card : ℝ) := Nat.cast_nonneg W.card; linarith
  exact le_trans h_erasure (mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr h_w_le_W) (le_of_lt hZ_pos))
private lemma kpCollarMaxCheckCard_and_kpRCADiagNat_bounds {R_cut r_0 w_0 : ℕ} {C_RCA : ℝ} (hR_cut : 1 ≤ R_cut)
    {Δ_V Δ_nat D_adj : ℕ} {Δ : ℝ} (hΔ_V_def : Δ_V = kpCollarMaxCheckCard R_cut r_0 w_0 C_RCA)
    (hΔ_nat_def : Δ_nat = kpRCADiagNat R_cut r_0 w_0 C_RCA) (hD_adj_def : D_adj = 4 * (Δ_nat + 1) * (Δ_V + 1))
    (hΔ_def : Δ = rcaDiagonalCoercivityConstant 3 R_cut r_0 w_0 C_RCA) :
    0 ≤ Δ ∧ 27 ≤ Δ_V ∧ Δ ≤ (Δ_V : ℝ) ^ 2 ∧ 16 ≤ D_adj ∧ (D_adj : ℝ) = 4 * (Δ + 1) * ((Δ_V : ℝ) + 1) := by
  let K_geom := (2 * (R_cut + 2 * linearExpansionRadius C_RCA R_cut + r_0) + 1) ^ 3 * (w_0 + 1)
  have hΔ_V_eq : Δ_V = K_geom + 1 := hΔ_V_def; have hΔ_nat_eq : Δ_nat = R_cut * K_geom := hΔ_nat_def
  have hK_geom_ge_27 : 27 ≤ K_geom := by
    dsimp [K_geom]; have h_base : 3 ≤ 2 * (R_cut + 2 * linearExpansionRadius C_RCA R_cut + r_0) + 1 := by omega
    exact le_trans (le_trans (by decide : 27 ≤ 3 ^ 3) (Nat.pow_le_pow_left h_base 3)) (Nat.le_mul_of_pos_right _ (Nat.succ_pos w_0))
  have hK_le_Δ_V : K_geom ≤ Δ_V := by omega
  have hR_le_Δ_V : R_cut ≤ Δ_V := by
    have h1 : R_cut ≤ 2 * (R_cut + 2 * linearExpansionRadius C_RCA R_cut + r_0) + 1 := by omega
    have h2 := Nat.le_self_pow (by decide : 3 ≠ 0) (2 * (R_cut + 2 * linearExpansionRadius C_RCA R_cut + r_0) + 1)
    exact le_trans (le_trans h1 (le_trans h2 (Nat.le_mul_of_pos_right _ (Nat.succ_pos w_0)))) hK_le_Δ_V
  have hΔ_nat_le_sq : Δ_nat ≤ Δ_V ^ 2 := by rw [hΔ_nat_eq, sq]; exact Nat.mul_le_mul hR_le_Δ_V hK_le_Δ_V
  have hΔ_cast : (Δ_nat : ℝ) = Δ := by rw [hΔ_nat_def, hΔ_def]; exact kpRCADiagNat_cast_eq R_cut r_0 w_0 C_RCA
  have h1 : 4 ≤ 4 * (Δ_nat + 1) := by omega
  have h2 : 4 ≤ Δ_V + 1 := by omega
  refine ⟨by rw [← hΔ_cast]; exact Nat.cast_nonneg _, by omega, by rw [← hΔ_cast]; exact_mod_cast hΔ_nat_le_sq,
    by rw [hD_adj_def]; exact le_trans (by decide : 16 ≤ 4 * 4) (Nat.mul_le_mul h1 h2), by rw [hD_adj_def]; push_cast; rw [hΔ_cast]⟩
private lemma worldline_weight_bounds_of_abstract_params {R_cut : ℕ} {β Δ_0 Δ_RCA C_wl c_wl J Δ τ_star ε : ℝ} {Δ_V D_adj : ℕ}
    (f : ℕ → ℝ) (hf_super : InPerturbationClassSuper f) (hτ_def : τ_star = 16 * (Δ + 1) * ((Δ_V : ℝ) + 1))
    (hε_def : ε = 1 / (8 * (Real.exp 1) ^ 2 * (D_adj : ℝ) ^ 3)) (hΔ_nn : 0 ≤ Δ) (hΔ_V_ge_27 : 27 ≤ Δ_V)
    (hΔ_le_v2 : Δ ≤ (Δ_V : ℝ) ^ 2) (hD_adj_ge_16 : 16 ≤ D_adj) (hD_adj_cast : (D_adj : ℝ) = 4 * (Δ + 1) * ((Δ_V : ℝ) + 1))
    (hC_wl_cal : (Δ_V : ℝ) ≤ C_wl) (hc_wl_cal : (Δ_V : ℝ) ≤ c_wl) (hΔ_0 : 0 < Δ_0) (hΔ_0_le : Δ_0 ≤ 1 / 4)
    (hΔ_RCA : 0 < Δ_RCA) (hβ_pos : 0 < β) (hβ : criticalInverseTempHier Δ_0 < β) (hJ : 0 ≤ J)
    (h_sum_pos : 0 < worldlineNativeKPSum f C_wl c_wl β R_cut) (h_thresh : J ≤ worldlineSpanningThreshold Δ_RCA C_wl c_wl β f R_cut) :
    Real.exp (-(3 / 4 : ℝ) * τ_star) ≤ ε ∧ ∀ r ∈ Finset.Icc 1 R_cut, 2 * Δ * J * f r ≤ ε := by
  have h_stat : Real.exp (-(3 / 4 : ℝ) * τ_star) ≤ ε := by
    have hx_ge : (16 : ℝ) ≤ (D_adj : ℝ) := Nat.cast_le.mpr hD_adj_ge_16
    have hx_half : (D_adj : ℝ) / 2 ≤ Real.exp ((D_adj : ℝ) / 2) := by linarith [Real.add_one_le_exp ((D_adj : ℝ) / 2)]
    have hx4 : ((D_adj : ℝ) / 2) ^ 4 ≤ Real.exp (2 * (D_adj : ℝ)) := by
      calc ((D_adj : ℝ) / 2) ^ 4 ≤ (Real.exp ((D_adj : ℝ) / 2)) ^ 4 := pow_le_pow_left₀ (by linarith) hx_half 4
        _ = Real.exp (2 * (D_adj : ℝ)) := by rw [← Real.exp_nat_mul]; congr 1; push_cast; ring
    have h16x : 16 * (D_adj : ℝ) ^ 3 ≤ (D_adj : ℝ) ^ 4 := by
      calc 16 * (D_adj : ℝ) ^ 3 ≤ (D_adj : ℝ) * (D_adj : ℝ) ^ 3 := mul_le_mul_of_nonneg_right hx_ge (by positivity)
        _ = (D_adj : ℝ) ^ 4 := by ring
    have hx3 : (D_adj : ℝ) ^ 3 ≤ Real.exp (2 * (D_adj : ℝ)) := le_trans (by linarith : (D_adj : ℝ) ^ 3 ≤ ((D_adj : ℝ) / 2) ^ 4) hx4
    have hx_sub : 8 ≤ Real.exp ((D_adj : ℝ) - 2) := by linarith [Real.add_one_le_exp ((D_adj : ℝ) - 2)]
    have h_exp_prod : 8 * (Real.exp 1) ^ 2 * (D_adj : ℝ) ^ 3 ≤ Real.exp (3 * (D_adj : ℝ)) := by
      calc 8 * (Real.exp 1) ^ 2 * (D_adj : ℝ) ^ 3 = 8 * (Real.exp 1 * Real.exp 1) * (D_adj : ℝ) ^ 3 := by ring
        _ ≤ Real.exp ((D_adj : ℝ) - 2) * (Real.exp 1 * Real.exp 1) * Real.exp (2 * (D_adj : ℝ)) :=
            mul_le_mul (mul_le_mul_of_nonneg_right hx_sub (by positivity)) hx3 (by positivity) (by positivity)
        _ = Real.exp (3 * (D_adj : ℝ)) := by simp_rw [← Real.exp_add]; congr 1; ring
    have hτ_eq : -(3 / 4 : ℝ) * τ_star = -(3 * (D_adj : ℝ)) := by rw [hτ_def, hD_adj_cast]; ring
    rw [hτ_eq, hε_def, Real.exp_neg, inv_eq_one_div]; exact one_div_le_one_div_of_le (by positivity) h_exp_prod
  refine ⟨h_stat, fun r hr_in => ?_⟩
  have hr_1 : 1 ≤ r := (Finset.mem_Icc.mp hr_in).1
  have h_kp_one : J * (64 * Real.exp 1 * max 1 β * worldlineNativeKPSum f C_wl c_wl β R_cut) ≤ 1 :=
    (le_div_iff₀ (by positivity)).mp (le_trans h_thresh (min_le_right _ _))
  have hv_ge : (27 : ℝ) ≤ (Δ_V : ℝ) := Nat.cast_le.mpr hΔ_V_ge_27
  have hC_wl_nn : 0 ≤ C_wl := by linarith
  have hc_wl_nn : 0 ≤ c_wl := by linarith
  have h_single_le : C_wl * (r : ℝ) ^ 6 * f r * Real.exp (c_wl * (1 + β) * (r : ℝ) ^ 3) ≤ worldlineNativeKPSum f C_wl c_wl β R_cut := by
    unfold worldlineNativeKPSum; refine Finset.single_le_sum (f := fun r' : ℕ => C_wl * (r' : ℝ) ^ 6 * f r' * Real.exp (c_wl * (1 + β) * (r' : ℝ) ^ 3)) (fun r' _ => ?_) hr_in
    have := hf_super.1 r'; positivity
  have hr_cast_1 : (1 : ℝ) ≤ (r : ℝ) := Nat.one_le_cast.mpr hr_1
  have hr_pow6_1 : (1 : ℝ) ≤ (r : ℝ) ^ 6 := one_le_pow₀ (n := 6) hr_cast_1; have hr_pow3_1 : (1 : ℝ) ≤ (r : ℝ) ^ 3 := one_le_pow₀ (n := 3) hr_cast_1
  have hβ_ge_24 : 24 < β := lt_of_le_of_lt (twenty_four_le_criticalInverseTempHier hΔ_0 hΔ_0_le) hβ
  have hv_exp : (Δ_V : ℝ) ≤ Real.exp (Δ_V : ℝ) := by linarith [Real.add_one_le_exp (Δ_V : ℝ)]
  have h_exp_r : 8 * Real.exp (16 * (Δ_V : ℝ)) ≤ Real.exp (c_wl * (1 + β) * (r : ℝ) ^ 3) := by
    have h8_v : (8 : ℝ) ≤ Real.exp (Δ_V : ℝ) := by linarith
    have h17_v : 17 * (Δ_V : ℝ) ≤ c_wl * (1 + β) := by nlinarith
    calc 8 * Real.exp (16 * (Δ_V : ℝ)) ≤ Real.exp (Δ_V : ℝ) * Real.exp (16 * (Δ_V : ℝ)) := mul_le_mul_of_nonneg_right h8_v (le_of_lt (Real.exp_pos _))
      _ = Real.exp (17 * (Δ_V : ℝ)) := by rw [← Real.exp_add]; congr 1; ring
      _ ≤ Real.exp (c_wl * (1 + β) * (r : ℝ) ^ 3) := Real.exp_le_exp.mpr (by nlinarith)
  have h_factor_r : 8 * (Δ_V : ℝ) * f r * Real.exp (16 * (Δ_V : ℝ)) ≤ worldlineNativeKPSum f C_wl c_wl β R_cut := by
    have hf_r_nn : 0 ≤ f r := hf_super.1 r
    have h_c1 : (Δ_V : ℝ) * f r ≤ C_wl * (r : ℝ) ^ 6 * f r := mul_le_mul_of_nonneg_right (by nlinarith) hf_r_nn
    linarith [mul_le_mul h_c1 h_exp_r (by positivity) (by positivity)]
  have h_512 : 512 * Real.exp 1 * (Δ_V : ℝ) * Real.exp (16 * (Δ_V : ℝ)) * J * f r ≤ 1 := by
    have h1 := le_trans h_factor_r (le_mul_of_one_le_left (by positivity) (le_max_left 1 β))
    linarith [mul_le_mul_of_nonneg_left h1 (by positivity : 0 ≤ 64 * Real.exp 1 * J)]
  have hD_le_16v3 : (D_adj : ℝ) ≤ 16 * (Δ_V : ℝ) ^ 3 := by
    rw [hD_adj_cast]
    have h_a : Δ + 1 ≤ 2 * (Δ_V : ℝ) ^ 2 := by nlinarith
    have h_b : (Δ_V : ℝ) + 1 ≤ 2 * (Δ_V : ℝ) := by linarith
    nlinarith
  have hD3_le : (D_adj : ℝ) ^ 3 ≤ (16 * (Δ_V : ℝ) ^ 3) ^ 3 := pow_le_pow_left₀ (by positivity) hD_le_16v3 3
  have hv10 : (Δ_V : ℝ) ^ 10 ≤ Real.exp (10 * (Δ_V : ℝ)) := by
    calc (Δ_V : ℝ) ^ 10 ≤ (Real.exp (Δ_V : ℝ)) ^ 10 := pow_le_pow_left₀ (by positivity) hv_exp 10
      _ = Real.exp (10 * (Δ_V : ℝ)) := by rw [← Real.exp_nat_mul]; congr 1
  have hv_6 : 128 ≤ Real.exp (6 * (Δ_V : ℝ) - 1) := by linarith [Real.add_one_le_exp (6 * (Δ_V : ℝ) - 1)]
  have h_coeff : 16 * (Real.exp 1) ^ 2 * Δ * (D_adj : ℝ) ^ 3 ≤ 512 * Real.exp 1 * (Δ_V : ℝ) * Real.exp (16 * (Δ_V : ℝ)) := by
    have h_alg1 : 16 * (Real.exp 1) ^ 2 * Δ * (D_adj : ℝ) ^ 3 ≤ 65536 * (Real.exp 1) ^ 2 * (Δ_V : ℝ) ^ 11 := by
      have h_mul := mul_le_mul hΔ_le_v2 hD3_le (by positivity) (by positivity)
      have h_eq : (Δ_V : ℝ) ^ 2 * (16 * (Δ_V : ℝ) ^ 3) ^ 3 = 4096 * (Δ_V : ℝ) ^ 11 := by ring
      rw [h_eq] at h_mul
      have h_pos : 0 ≤ 16 * (Real.exp 1) ^ 2 := by positivity
      nlinarith
    have h_alg2 : 128 * Real.exp 1 * (Δ_V : ℝ) ^ 10 ≤ Real.exp (16 * (Δ_V : ℝ)) := by
      calc 128 * Real.exp 1 * (Δ_V : ℝ) ^ 10 ≤ Real.exp (6 * (Δ_V : ℝ) - 1) * Real.exp 1 * Real.exp (10 * (Δ_V : ℝ)) :=
            mul_le_mul (mul_le_mul_of_nonneg_right hv_6 (by positivity)) hv10 (by positivity) (by positivity)
        _ = Real.exp (16 * (Δ_V : ℝ)) := by simp_rw [← Real.exp_add]; congr 1; ring
    linarith [mul_le_mul_of_nonneg_left h_alg2 (by positivity : 0 ≤ 512 * Real.exp 1 * (Δ_V : ℝ))]
  have h_prod_le_1 : (2 * Δ * J * f r) * (8 * (Real.exp 1) ^ 2 * (D_adj : ℝ) ^ 3) ≤ 1 := by
    linarith [mul_le_mul_of_nonneg_right h_coeff (mul_nonneg hJ (hf_super.1 r))]
  rw [hε_def]; exact (le_div_iff₀ (by positivity)).mpr h_prod_le_1
private lemma mul_off_diag_le_two_mul {Δ a b c J f_r : ℝ} (hΔ : 0 ≤ Δ) (h1 : a ≤ b + c) (h2 : b ≤ J * f_r) (h3 : c ≤ b) : Δ * a ≤ 2 * Δ * J * f_r := by nlinarith
private lemma w_poly_nonneg_and_le_pow {Cell ι_poly : Type*} [DecidableEq Cell] (S_stat S_jump supp : ι_poly → Finset Cell)
    (h_supp : ∀ γ, supp γ = S_stat γ ∪ S_jump γ) (h_disj : ∀ γ, Disjoint (S_stat γ) (S_jump γ)) {w_stat ε : ℝ} (b_jump w_poly : ι_poly → ℝ)
    (hw_def : ∀ γ, w_poly γ = w_stat ^ (S_stat γ).card * (b_jump γ) ^ (S_jump γ).card)
    (hw_stat_nn : 0 ≤ w_stat) (hw_stat_le : w_stat ≤ ε) (hb_nn : ∀ γ, 0 ≤ b_jump γ) (hb_le : ∀ γ, b_jump γ ≤ ε) :
    (∀ γ, 0 ≤ w_poly γ) ∧ (∀ γ, w_poly γ ≤ ε ^ (supp γ).card) := by
  refine ⟨fun γ => by rw [hw_def γ]; exact mul_nonneg (pow_nonneg hw_stat_nn _) (pow_nonneg (hb_nn γ) _), fun γ => ?_⟩
  rw [hw_def γ, h_supp γ, Finset.card_union_of_disjoint (h_disj γ), pow_add]
  exact mul_le_mul (pow_le_pow_left₀ hw_stat_nn hw_stat_le _) (pow_le_pow_left₀ (hb_nn γ) (hb_le γ) _) (pow_nonneg (hb_nn γ) _) (pow_nonneg (le_trans hw_stat_nn hw_stat_le) _)

/-- **Existence of Worldline Kotecký–Preiss Majorant under Spanning Threshold (`exists_worldline_kp_majorant_of_spanningThreshold`)**
(Part II, Section 3.5 (`subsec:worldline-expansion`), Proposition 3.10 (`prop:tube-local-ursell-erasure`)):
Under `J ≤ worldlineSpanningThreshold Δ_RCA C_wl c_wl β f R_cut`, the connected spacetime worldline
polymers `γ : ι_poly` with support `supp γ = S_stat γ ∪ S_jump γ` admit size/decay functions
`a_poly, d_poly ≥ |supp γ|` satisfying the Kotecký–Preiss condition and the tube-local erasure
partition ratio bound `polymerPartitionZ compat w_poly univ / polymerPartitionZ compat w_poly (univ \ T_W) ≤ exp(|W|)`. -/
lemma exists_worldline_kp_majorant_of_spanningThreshold
    {L q_code r_0 m_max w_0 L_star R_cut : ℕ} [NeZero L]
    {ι_poly : Type*} [Fintype ι_poly] [DecidableEq ι_poly]
    {C_RCA β Δ_0 Δ_RCA C_wl c_wl J : ℝ}
    (D_field : Box3D L → LocalCSSDescriptor q_code r_0 m_max) (h_valid : ValidDescriptorField D_field)
    (sys : SysCSS[L, q_code, m_max])
    (h_sys_checks : ∀ idx, sys.checkProj idx = staticCSSCheckProj D_field idx ∧
      sys.support idx = staticCSSCheckSupport D_field idx ∧ sys.weight idx = 1)
    (h_geom : sys.IsGeometricallyLocal r_0 w_0)
    (h_tqo1 : SatisfiesTQO1 sys L_star) (h_tqo2 : SatisfiesSectorFilteredLinearTQO2 sys 1 L_star C_RCA)
    (V : QuasiLocalPerturbation 3 L (SiteCSS[L, q_code])) (f : ℕ → ℝ)
    (hf_super : InPerturbationClassSuper f) (h_ql : HasQuasiLocalDecayBound V J f)
    (W : Finset (IdxCSS[L, q_code, m_max]))
    (S_stat S_jump : ι_poly → Finset (KPSpacetimeGridCell L q_code m_max (thermalTimeSliceCount β)))
    (r_jump : ι_poly → ℕ) (A_jump : ι_poly → Finset (Box3D L))
    (hR_cut : 1 ≤ R_cut) (hR_le : R_cut ≤ L_star) (hC_RCA : 0 ≤ C_RCA)
    (h_rca_cal : rcaDiagonalCoercivityConstant 3 R_cut r_0 w_0 C_RCA ≤ Δ_RCA)
    (hC_wl_cal : (kpCollarMaxCheckCard R_cut r_0 w_0 C_RCA : ℝ) ≤ C_wl)
    (hc_wl_cal : (kpCollarMaxCheckCard R_cut r_0 w_0 C_RCA : ℝ) ≤ c_wl)
    (hΔ_0 : 0 < Δ_0) (hΔ_0_le : Δ_0 ≤ 1 / 4) (hΔ_RCA : 0 < Δ_RCA)
    (hβ_pos : 0 < β) (hβ : criticalInverseTempHier Δ_0 < β) (hJ : 0 ≤ J)
    (hr_jump : ∀ γ, r_jump γ ∈ Finset.Icc 1 (min R_cut L) ∧ A_jump γ ∈ boxCubes 3 L (r_jump γ))
    (h_jump_card : ∀ γ : ι_poly, 1 ≤ (S_jump γ).card)
    (h_sum_pos : 0 < worldlineNativeKPSum f C_wl c_wl β R_cut)
    (hJ_wl : J ≤ worldlineCouplingThreshold Δ_0 Δ_RCA)
    (h_thresh : J ≤ worldlineSpanningThreshold Δ_RCA C_wl c_wl β f R_cut)
    (h_disj : ∀ γ, Disjoint (S_stat γ) (S_jump γ)) (h_nonempty : ∀ γ, (S_stat γ ∪ S_jump γ).Nonempty)
    (h_conn : ∀ γ, KPIsConnectedSubgraph (KPSpacetimeCellAdj sys C_RCA R_cut (thermalTimeSliceCount β)) (S_stat γ ∪ S_jump γ))
    (h_inj_poly : ∀ γ₁ γ₂, S_stat γ₁ = S_stat γ₂ → S_jump γ₁ = S_jump γ₂ → γ₁ = γ₂) :
    let M := thermalTimeSliceCount β
    let Δ := rcaDiagonalCoercivityConstant 3 R_cut r_0 w_0 C_RCA
    let Δ_V := kpCollarMaxCheckCard R_cut r_0 w_0 C_RCA
    let τ_star := 16 * (Δ + 1) * ((Δ_V : ℝ) + 1)
    let supp := fun γ : ι_poly => S_stat γ ∪ S_jump γ
    let compat := fun γ₁ γ₂ : ι_poly => Disjoint (supp γ₁) (supp γ₂) ∧
      ∀ u ∈ supp γ₁, ∀ v ∈ supp γ₂, ¬KPSpacetimeCellAdj sys C_RCA R_cut M u v
    let w_poly := fun γ : ι_poly =>
      (Real.exp (-(3 / 4 : ℝ) * τ_star)) ^ (S_stat γ).card *
        (Δ * ‖pauliOffDiagonalTerm sys V (r_jump γ) (A_jump γ)‖) ^ (S_jump γ).card
    have hM_pos : 0 < M := lt_of_lt_of_le Nat.zero_lt_one (le_max_left 1 ⌈β⌉₊)
    ∃ (a_poly d_poly : ι_poly → ℝ),
      (∀ γ : ι_poly, ((supp γ).card : ℝ) ≤ a_poly γ ∧ ((supp γ).card : ℝ) ≤ d_poly γ) ∧
      SatisfiesKoteckyPreissCondition compat w_poly a_poly d_poly ∧
      (∀ (Γ_vac Γ_pin : Finset ι_poly),
        polymerPartitionZ compat w_poly Γ_vac ≤
          Real.exp (∑ γ' ∈ Γ_vac.filter (fun γ' => ∃ γ ∈ Γ_pin, ¬compat γ γ'), a_poly γ') *
            polymerPartitionZ compat w_poly (Γ_vac.filter (fun γ' => ∀ γ ∈ Γ_pin, compat γ γ'))) ∧
      (∀ (Γ_pin : Finset ι_poly), IsCompatiblePolymerSet compat Γ_pin →
        polymerPinnedSum compat w_poly Finset.univ Γ_pin ≤
          Real.exp (-(∑ γ ∈ Γ_pin, d_poly γ)) * polymerPartitionZ compat w_poly Finset.univ) ∧
      Real.exp (∑ γ ∈ Finset.univ.filter (fun γ : ι_poly => ∃ c ∈ W, (c, ⟨0, hM_pos⟩) ∈ supp γ),
        w_poly γ * Real.exp (a_poly γ + d_poly γ)) ≤ Real.exp ((1 / 2 : ℝ) * (W.card : ℝ)) ∧
      polymerPartitionZ compat w_poly Finset.univ /
        polymerPartitionZ compat w_poly
          (Finset.univ.filter (fun γ : ι_poly => ¬∃ c ∈ W, (c, ⟨0, hM_pos⟩) ∈ supp γ)) ≤
        Real.exp (W.card : ℝ) := by
  intro M Δ Δ_V τ_star supp compat w_poly hM_pos
  let Δ_nat := kpRCADiagNat R_cut r_0 w_0 C_RCA; let D_adj : ℕ := 4 * (Δ_nat + 1) * (Δ_V + 1); let ε : ℝ := 1 / (8 * (Real.exp 1) ^ 2 * (D_adj : ℝ) ^ 3)
  rcases kpCollarMaxCheckCard_and_kpRCADiagNat_bounds hR_cut (rfl : Δ_V = _) (rfl : Δ_nat = _) (rfl : D_adj = _) (rfl : Δ = _) with ⟨hΔ_nn, hΔ_V_ge_27, hΔ_le_v2, hD_adj_ge_16, hD_adj_cast⟩
  rcases worldline_weight_bounds_of_abstract_params f hf_super (rfl : τ_star = _) (rfl : ε = _)
    hΔ_nn hΔ_V_ge_27 hΔ_le_v2 hD_adj_ge_16 hD_adj_cast hC_wl_cal hc_wl_cal hΔ_0 hΔ_0_le hΔ_RCA hβ_pos hβ hJ h_sum_pos h_thresh with ⟨h_stat_le_ε, h_r_le_ε⟩
  have h_jump_le_ε : ∀ γ : ι_poly, Δ * ‖pauliOffDiagonalTerm sys V (r_jump γ) (A_jump γ)‖ ≤ ε := fun γ => by
    have hr_1 : 1 ≤ r_jump γ := (Finset.mem_Icc.mp (hr_jump γ).1).1; have hr_R : r_jump γ ≤ R_cut := le_trans (Finset.mem_Icc.mp (hr_jump γ).1).2 (Nat.min_le_left R_cut L)
    have hr_L : r_jump γ ∈ Finset.Icc 1 L := Finset.mem_Icc.mpr ⟨hr_1, le_trans (Finset.mem_Icc.mp (hr_jump γ).1).2 (Nat.min_le_right R_cut L)⟩
    have h_pinch := (syndromePinchOp_norm_and_isSupportedOn_of_staticCSSCheck D_field sys h_sys_checks (A_jump γ) (V.is_supported (r_jump γ) hr_L (A_jump γ) (hr_jump γ).2)).1
    exact le_trans (mul_off_diag_le_two_mul hΔ_nn (norm_sub_le _ _) (h_ql.1 (r_jump γ) hr_L (A_jump γ) (hr_jump γ).2).2 h_pinch) (h_r_le_ε (r_jump γ) (Finset.mem_Icc.mpr ⟨hr_1, hr_R⟩))
  rcases w_poly_nonneg_and_le_pow S_stat S_jump supp (fun _ => rfl) h_disj (fun γ => Δ * ‖pauliOffDiagonalTerm sys V (r_jump γ) (A_jump γ)‖) w_poly (fun _ => rfl)
    (le_of_lt (Real.exp_pos _)) h_stat_le_ε (fun _ => mul_nonneg hΔ_nn (norm_nonneg _)) h_jump_le_ε with ⟨hw_nn, hw_le⟩
  exact abstract_cell_kp_majorant (KPSpacetimeCellAdj sys C_RCA R_cut M) (kpSpacetimeCellAdj_refl sys C_RCA R_cut M)
    (kpSpacetimeCellAdj_symm sys C_RCA R_cut M) hD_adj_ge_16 (fun u => card_filter_kpSpacetimeCellAdj_le D_field sys h_sys_checks h_geom hC_RCA u)
    S_stat S_jump supp (fun _ => rfl) compat (fun _ _ => Iff.rfl) h_disj h_nonempty h_conn h_inj_poly w_poly hw_nn hw_le W (fun c => (c, ⟨0, hM_pos⟩))

/-- **Worldline Factorization and Tube-Local Ursell Erasure Synthesis (`worldline_factorization_and_ursell_erasure`)**
(Part II, Section 3.3 (`subsec:walsh-coset-peeling`), Propositions 3.5–3.6 (`prop:witness-coset-reduction`, `prop:walsh-coset-dominance`), Section 3.5 (`subsec:worldline-expansion`), Lemma 3.9 (`lem:worldline-factorization-time-reversal`) and Proposition 3.10 (`prop:tube-local-ursell-erasure`), and Section 5.1 (`subsec:direct-worldline-synthesis`), Theorem 5.1 (`thm:direct-worldline-intact-cluster-erasure`)):
Walsh–Hadamard coset trace, time-reversal positivity, disjoint tube factorization, logical character
orthogonality, native-collar and Prüfer tree bounds, 3D CSS worldline KP convergence, and witness failure bound. -/
theorem worldline_factorization_and_ursell_erasure
    {L q_code r_0 m_max w_0 c_chk L_star R_cut m m_tree : ℕ} [NeZero L]
    {ι_synd ι_tube ι_poly ι_mon : Type*} [Fintype ι_synd] [DecidableEq ι_synd]
    [Fintype ι_poly] [DecidableEq ι_poly] [DecidableEq ι_mon]
    {ι_cube : ℕ → Type*} [∀ r, Fintype (ι_cube r)] [∀ r, DecidableEq (ι_cube r)]
    {C_RCA β Δ_0 Δ_RCA C_wl c_wl J : ℝ}
    (D_field : Box3D L → LocalCSSDescriptor q_code r_0 m_max) (h_valid : ValidDescriptorField D_field)
    (sys : SysCSS[L, q_code, m_max])
    (h_sys_checks : ∀ idx, sys.checkProj idx = staticCSSCheckProj D_field idx ∧
      sys.support idx = staticCSSCheckSupport D_field idx ∧ sys.weight idx = 1)
    (h_geom : sys.IsGeometricallyLocal r_0 w_0)
    (h_tqo1 : SatisfiesTQO1 sys L_star) (h_tqo2 : SatisfiesSectorFilteredLinearTQO2 sys 1 L_star C_RCA)
    (V : QuasiLocalPerturbation 3 L (SiteCSS[L, q_code])) (f : ℕ → ℝ)
    (hf_super : InPerturbationClassSuper f) (h_ql : HasQuasiLocalDecayBound V J f)
    (hH_trunc : IsSelfAdjoint (sys.H0 + scaleSplitTruncatedOp V R_cut))
    (W_event : Finset ι_synd) (τ_W : ι_synd ↪ ι_synd) (E_0 V_diag : ι_synd → ℝ)
    (V_term : (r : ℕ) → ι_cube r → ι_synd → ℝ) (collarHitCount : (r : ℕ) → ι_cube r → ℕ)
    (K : ι_synd → ι_synd → ℂ) (tubes : Finset ι_tube) (Z_tube : ι_tube → ℝ) (W : Finset (IdxCSS[L, q_code, m_max]))
    (S_stat S_jump : ι_poly → Finset (KPSpacetimeGridCell L q_code m_max (thermalTimeSliceCount β)))
    (r_jump : ι_poly → ℕ) (A_jump : ι_poly → Finset (Box3D L)) (w_micro : ι_poly → ℝ)
    (μ_char : ι_poly → LogicalPauliChar) (μ_0 : LogicalPauliChar)
    (collarChecks : ι_mon → Finset (IdxCSS[L, q_code, m_max])) (d_deg : Fin (m_tree + 2) → ℕ)
    (hR_cut : 1 ≤ R_cut) (hR_le : R_cut ≤ L_star) (h_scale_cal : SatisfiesWorldlineScaleCalibration L L_star R_cut r_0 C_RCA) (hC_RCA : 0 ≤ C_RCA)
    (h_rca_cal : rcaDiagonalCoercivityConstant 3 R_cut r_0 w_0 C_RCA ≤ Δ_RCA)
    (hC_wl_cal : (kpCollarMaxCheckCard R_cut r_0 w_0 C_RCA : ℝ) ≤ C_wl)
    (hc_wl_cal : (kpCollarMaxCheckCard R_cut r_0 w_0 C_RCA : ℝ) ≤ c_wl)
    (hΔ_0 : 0 < Δ_0) (hΔ_0_le : Δ_0 ≤ 1 / 4) (hΔ_RCA : 0 < Δ_RCA) (hβ_pos : 0 < β) (hβ : criticalInverseTempHier Δ_0 < β) (hJ : 0 ≤ J)
    (hr_jump : ∀ γ, r_jump γ ∈ Finset.Icc 1 (min R_cut L) ∧ A_jump γ ∈ boxCubes 3 L (r_jump γ))
    (h_jump_card : ∀ γ : ι_poly, 1 ≤ (S_jump γ).card)
    (h_energy_drop : ∀ σ ∈ W_event, E_0 (τ_W σ) ≤ E_0 σ - 2 * Δ_0 * (m : ℝ))
    (h_V_decomp : ∀ σ : ι_synd, V_diag σ = ∑ r ∈ Finset.Icc 1 L_star, ∑ A : ι_cube r, V_term r A σ)
    (h_local_collar : ∀ r ∈ Finset.Icc 1 L_star, ∀ A : ι_cube r, ∀ σ ∈ W_event,
      |V_term r A σ - V_term r A (τ_W σ)| ≤ 2 * J * f r * (collarHitCount r A : ℝ))
    (h_hit_sum : ∀ r ∈ Finset.Icc 1 L_star, (∑ A : ι_cube r, collarHitCount r A) ≤
      m * activeCheckFootprintBound c_chk r_0 (rcaCollarRadius C_RCA r_0 r))
    (h_collar_le : rcaCollarFiniteSum f c_chk r_0 L_star C_RCA ≤ Δ_RCA)
    (h_herm : ∀ σ τ : ι_synd, K τ σ = star (K σ τ)) (hZ_nonneg : ∀ T ∈ tubes, 0 ≤ Z_tube T)
    (h_deg_sum : (∑ i : Fin (m_tree + 2), d_deg i) = m_tree + 1)
    (h_sum_pos : 0 < worldlineNativeKPSum f C_wl c_wl β R_cut)
    (hJ_walsh : J ≤ collarWalshCouplingThreshold R_cut r_0 w_0 C_RCA)
    (hJ_wl : J ≤ worldlineCouplingThreshold Δ_0 Δ_RCA)
    (h_thresh : J ≤ worldlineSpanningThreshold Δ_RCA C_wl c_wl β f R_cut)
    (hW_valid : (fun idx => decide (idx ∈ W)) ∈ realizableSyndromes D_field)
    (h_disj : ∀ γ, Disjoint (S_stat γ) (S_jump γ)) (h_nonempty : ∀ γ, (S_stat γ ∪ S_jump γ).Nonempty)
    (h_conn : ∀ γ, KPIsConnectedSubgraph (KPSpacetimeCellAdj sys C_RCA R_cut (thermalTimeSliceCount β)) (S_stat γ ∪ S_jump γ))
    (h_inj_poly : ∀ γ₁ γ₂, S_stat γ₁ = S_stat γ₂ → S_jump γ₁ = S_jump γ₂ → γ₁ = γ₂) :
    let M := thermalTimeSliceCount β
    let Δ := rcaDiagonalCoercivityConstant 3 R_cut r_0 w_0 C_RCA
    let Δ_V := kpCollarMaxCheckCard R_cut r_0 w_0 C_RCA
    let τ_star := 16 * (Δ + 1) * ((Δ_V : ℝ) + 1)
    let supp := fun γ : ι_poly => S_stat γ ∪ S_jump γ
    let compat := fun γ₁ γ₂ : ι_poly => Disjoint (supp γ₁) (supp γ₂) ∧
      ∀ u ∈ supp γ₁, ∀ v ∈ supp γ₂, ¬KPSpacetimeCellAdj sys C_RCA R_cut M u v
    let w_poly := fun γ : ι_poly =>
      (Real.exp (-(3 / 4 : ℝ) * τ_star)) ^ (S_stat γ).card *
        (Δ * ‖pauliOffDiagonalTerm sys V (r_jump γ) (A_jump γ)‖) ^ (S_jump γ).card
    have hM_pos : 0 < M := lt_of_lt_of_le Nat.zero_lt_one (le_max_left 1 ⌈β⌉₊)
    ((∀ σ ∈ W_event, |V_diag σ - V_diag (τ_W σ)| ≤ 2 * J * Δ_RCA * (m : ℝ)) ∧
    (∑ σ ∈ W_event, Real.exp (-β * (E_0 σ + V_diag σ))) ≤
      Real.exp (-β * (2 * Δ_0 - 2 * J * Δ_RCA) * (m : ℝ)) *
        (∑ σ : ι_synd, Real.exp (-β * (E_0 σ + V_diag σ)))) ∧
    ((∀ σ τ : ι_synd, 0 ≤ ‖K σ τ‖ ^ 2 * Real.exp (-β * (E_0 σ + E_0 τ) / 2)) ∧
      (∏ T ∈ tubes, (1 + Z_tube T)) ≤ Real.exp (∑ T ∈ tubes, Z_tube T) ∧
      (∀ ν : LogicalPauliChar, ∀ γ : ι_poly,
        |characterTwistedPolymerWeight w_micro μ_char ν γ| = |w_micro γ|) ∧
      (1 / 4 : ℝ) * (∑ ν : LogicalPauliChar, logicalCharSign ν μ_0) =
        (if μ_0 = (0, 0) then 1 else 0) ∧
      (∀ γ_set : Finset ι_mon,
        (1 / 8 : ℝ) * ((nativeCollarSupport collarChecks γ_set).card : ℝ) ≤
          worldlinePolymerSize collarChecks γ_set) ∧
      (pruferRootedTreeDegreeSum d_deg : ℝ) = (Nat.factorial (m_tree + 1) : ℝ)) ∧
    ((∀ γ : ι_poly, ‖pauliOffDiagonalTerm sys V (r_jump γ) (A_jump γ)‖ ≤ 2 * J * f (r_jump γ)) ∧
      64 * Real.exp 1 * max 1 β * J * worldlineNativeKPSum f C_wl c_wl β R_cut ≤ 1 ∧
      gibbsFailureProb (sys.H0 + scaleSplitTruncatedOp V R_cut) hH_trunc β
        (positiveCheckWitnessProj sys W) ≤
        Real.exp (-β * (2 * Δ_0 - 6 * J * Δ_RCA) * (W.card : ℝ)) ∧
      ∃ (a_poly d_poly : ι_poly → ℝ),
        (∀ γ : ι_poly, ((supp γ).card : ℝ) ≤ a_poly γ ∧ ((supp γ).card : ℝ) ≤ d_poly γ) ∧
        SatisfiesKoteckyPreissCondition compat w_poly a_poly d_poly ∧
        (∀ (Γ_vac Γ_pin : Finset ι_poly),
          polymerPartitionZ compat w_poly Γ_vac ≤
            Real.exp (∑ γ' ∈ Γ_vac.filter (fun γ' => ∃ γ ∈ Γ_pin, ¬compat γ γ'), a_poly γ') *
              polymerPartitionZ compat w_poly (Γ_vac.filter (fun γ' => ∀ γ ∈ Γ_pin, compat γ γ'))) ∧
        (∀ (Γ_pin : Finset ι_poly), IsCompatiblePolymerSet compat Γ_pin →
          polymerPinnedSum compat w_poly Finset.univ Γ_pin ≤
            Real.exp (-(∑ γ ∈ Γ_pin, d_poly γ)) * polymerPartitionZ compat w_poly Finset.univ) ∧
        Real.exp (∑ γ ∈ Finset.univ.filter (fun γ : ι_poly => ∃ c ∈ W, (c, ⟨0, hM_pos⟩) ∈ supp γ),
          w_poly γ * Real.exp (a_poly γ + d_poly γ)) ≤ Real.exp ((1 / 2 : ℝ) * (W.card : ℝ)) ∧
        polymerPartitionZ compat w_poly Finset.univ /
          polymerPartitionZ compat w_poly
            (Finset.univ.filter (fun γ : ι_poly => ¬∃ c ∈ W, (c, ⟨0, hM_pos⟩) ∈ supp γ)) ≤
          Real.exp (W.card : ℝ)) := by
  intro M Δ Δ_V τ_star supp compat w_poly hM_pos
  have h1 := witnessCoset_trace_diagonal_reduction W_event τ_W E_0 V_diag V_term collarHitCount
    f c_chk r_0 L_star C_RCA β Δ_0 J Δ_RCA m hβ_pos.le hJ hf_super.1
    h_energy_drop h_V_decomp h_local_collar h_hit_sum h_collar_le
  have h2a := worldline_factorization_and_time_reversal_nonneg K E_0 β tubes Z_tube h_herm hZ_nonneg
  have h2b := worldline_character_projection_and_prufer_tree_bound w_micro μ_char μ_0
    collarChecks m_tree d_deg h_deg_sum
  have h_off_norm : ∀ γ : ι_poly, ‖pauliOffDiagonalTerm sys V (r_jump γ) (A_jump γ)‖ ≤ 2 * J * f (r_jump γ) := by
    intro γ
    have hr := (hr_jump γ).1; have hA := (hr_jump γ).2
    have hr_L : r_jump γ ∈ Finset.Icc 1 L := Finset.mem_Icc.mpr
      ⟨(Finset.mem_Icc.mp hr).1, le_trans (Finset.mem_Icc.mp hr).2 (Nat.min_le_right R_cut L)⟩
    have h_pinch := (syndromePinchOp_norm_and_isSupportedOn_of_staticCSSCheck
      D_field sys h_sys_checks (A_jump γ) (V.is_supported (r_jump γ) hr_L (A_jump γ) hA)).1
    have h_ql_norm := (h_ql.1 (r_jump γ) hr_L (A_jump γ) hA).2
    unfold pauliOffDiagonalTerm
    calc ‖V.term (r_jump γ) (A_jump γ) - syndromePinchOp sys (V.term (r_jump γ) (A_jump γ))‖
      _ ≤ ‖V.term (r_jump γ) (A_jump γ)‖ + ‖syndromePinchOp sys (V.term (r_jump γ) (A_jump γ))‖ := norm_sub_le _ _
      _ ≤ J * f (r_jump γ) + J * f (r_jump γ) := add_le_add h_ql_norm (le_trans h_pinch h_ql_norm)
      _ = 2 * J * f (r_jump γ) := by ring
  have h_kp_le_one : 64 * Real.exp 1 * max 1 β * J * worldlineNativeKPSum f C_wl c_wl β R_cut ≤ 1 :=
    (tubeLocal_ursell_erasure_log_ratio_le (∅ : Finset (IdxCSS[L, q_code, m_max]))
      (fun _ : ι_poly => ∅) (fun _ => 0) f R_cut Δ_RCA C_wl c_wl β J 1 1 0
      hΔ_RCA hβ_pos hJ h_sum_pos h_thresh zero_lt_one (by simp) (by simp) (fun _ h => False.elim (Finset.notMem_empty _ h))).1
  have h_gibbs := (directWorldline_truncated_css_witness_gibbsFailureProb_le
    D_field h_valid sys h_sys_checks h_geom h_tqo1 h_tqo2 V f hf_super h_ql hH_trunc
    hR_cut hR_le h_scale_cal hC_RCA h_rca_cal hC_wl_cal hc_wl_cal hΔ_0 hΔ_0_le hΔ_RCA hβ hJ h_sum_pos hJ_walsh hJ_wl h_thresh W hW_valid).1
  have h_kp_exist := exists_worldline_kp_majorant_of_spanningThreshold
    D_field h_valid sys h_sys_checks h_geom h_tqo1 h_tqo2 V f hf_super h_ql W
    S_stat S_jump r_jump A_jump hR_cut hR_le hC_RCA h_rca_cal hC_wl_cal hc_wl_cal hΔ_0 hΔ_0_le hΔ_RCA hβ_pos hβ hJ
    hr_jump h_jump_card h_sum_pos hJ_wl h_thresh h_disj h_nonempty h_conn h_inj_poly
  exact ⟨h1, ⟨h2a.1, h2a.2, h2b.1, h2b.2.1, h2b.2.2.1, h2b.2.2.2⟩,
    h_off_norm, h_kp_le_one, h_gibbs, h_kp_exist⟩

/-- Tail operator norm bound `‖scaleSplitTailOp V R_cut‖ ≤ J * L^3 * perturbationTailSeries f R_cut`. -/
lemma scaleSplitTailOp_norm_le {L : ℕ}
    {Site : BoxD 3 L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    (V : QuasiLocalPerturbation 3 L Site) (J : ℝ) (f : ℕ → ℝ) (R_cut : ℕ)
    (hJ_nonneg : 0 ≤ J) (hf_nn : ∀ r, 0 ≤ f r) (h_summable : Summable f)
    (h_ql : HasQuasiLocalDecayBound V J f) :
    ‖scaleSplitTailOp V R_cut‖ ≤ J * ((L ^ 3 : ℕ) : ℝ) * perturbationTailSeries f R_cut := by
  unfold scaleSplitTailOp perturbationTailSeries
  let S_tail := (Finset.Icc 1 L).filter (fun r => R_cut < r)
  have h_sum : Summable (fun r : ℕ => if R_cut < r then f r else 0) :=
    Summable.of_nonneg_of_le (fun r => by split_ifs <;> [exact hf_nn r; exact le_rfl])
      (fun r => by split_ifs <;> [exact le_rfl; exact hf_nn r]) h_summable
  have h1 : ‖∑ r ∈ S_tail, ∑ A ∈ boxCubes 3 L r, V.term r A‖ ≤
      ∑ r ∈ S_tail, ∑ A ∈ boxCubes 3 L r, ‖V.term r A‖ :=
    le_trans (norm_sum_le S_tail _) (Finset.sum_le_sum fun r _ => norm_sum_le (boxCubes 3 L r) _)
  have h2 : (∑ r ∈ S_tail, ∑ A ∈ boxCubes 3 L r, ‖V.term r A‖) ≤
      ∑ r ∈ S_tail, J * ((L ^ 3 : ℕ) : ℝ) * (if R_cut < r then f r else 0) :=
    Finset.sum_le_sum fun r hr => by
      rw [if_pos (Finset.mem_filter.mp hr).2]; exact h_ql.2 r (Finset.mem_filter.mp hr).1
  have h3 : (∑ r ∈ S_tail, J * ((L ^ 3 : ℕ) : ℝ) * (if R_cut < r then f r else 0)) ≤
      J * ((L ^ 3 : ℕ) : ℝ) * (∑' r : ℕ, if R_cut < r then f r else 0) := by
    rw [← Finset.mul_sum]
    exact mul_le_mul_of_nonneg_left (h_sum.sum_le_tsum S_tail
      (fun r _ => by split_ifs <;> [exact hf_nn r; exact le_rfl])) (by positivity)
  exact le_trans h1 (le_trans h2 h3)

/-- **Scale-Split Intact-Cluster Synthesis (`directWorldline_scaleSplit_intact_cluster_synthesis`)** (Part II, Section 6.3 (`subsec:main-theorems`), Theorem 6.3 (`thm:main-A`), Equation `eq:main-A-master`, and Section 5.1 (`subsec:direct-worldline-synthesis`), Theorem 5.1 (`thm:direct-worldline-intact-cluster-erasure`)):
Polymorphic scale-split master bound combining `pauliDiagOffDecomposition_local_shift_le`,
`rcaCollarConstant_le_pi_sq_div_six_mul_moment5`, `duhamelWeyl_relative_partition_ratio_bound`,
and `directWorldline_truncated_gibbsFailureProb_le`. -/
theorem directWorldline_scaleSplit_intact_cluster_synthesis {L : ℕ}
    {Site : BoxD 3 L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)] [∀ x, Nonempty (Site x)]
    {ι_chk : Type} [Fintype ι_chk] [DecidableEq ι_chk]
    (sys : IndexedCommutingProjectorHamiltonian 3 L Site ι_chk)
    (V : QuasiLocalPerturbation 3 L Site)
    (f : ℕ → ℝ) (c_chk r_0 R_cut d_min : ℕ)
    (hH_trunc : IsSelfAdjoint (sys.H0 + scaleSplitTruncatedOp V R_cut))
    (hH_full : IsSelfAdjoint ((sys.H0 + scaleSplitTruncatedOp V R_cut) + scaleSplitTailOp V R_cut))
    (C_RCA M_5 η c_wt Δ_0 Δ_RCA C_wl c_wl β J : ℝ)
    (S_safe : Finset (ι_chk → Bool)) (W_cover : Finset (Finset ι_chk))
    (hc_chk : 1 ≤ c_chk) (hr_0 : 1 ≤ r_0) (hC_RCA : 0 ≤ C_RCA) (hR_cut : 1 ≤ R_cut)
    (hM5 : HasDecayMomentBound f 5 M_5) (h_summable : Summable f) (h_ql : HasQuasiLocalDecayBound V J f)
    (hc_wt : 0 < c_wt) (hΔ_0 : 0 < Δ_0) (hΔ_RCA : 0 < Δ_RCA) (hJ_nonneg : 0 ≤ J)
    (hJ_wl : J ≤ worldlineCouplingThreshold Δ_0 Δ_RCA)
    (hJ_span : J ≤ worldlineSpanningThreshold Δ_RCA C_wl c_wl β f R_cut)
    (h_sum_pos : 0 < worldlineNativeKPSum f C_wl c_wl β R_cut) (hβ : criticalInverseTempHier Δ_0 < β)
    (hd_min : c_wt * (((L ^ 3 : ℕ) : ℝ) ^ η) ≤ (d_min : ℝ))
    (h_cover : IsPositiveCheckWitnessCover S_safe W_cover)
    (h_witness_raw : ∀ W ∈ W_cover,
      gibbsFailureProb (sys.H0 + scaleSplitTruncatedOp V R_cut) hH_trunc β
        (positiveCheckWitnessProj sys W) ≤
        Real.exp (-β * (2 * Δ_0 - 6 * J * Δ_RCA) * (W.card : ℝ)) *
          Real.exp (64 * Real.exp 1 * max 1 β * J *
            worldlineNativeKPSum f C_wl c_wl β R_cut * (W.card : ℝ)))
    (h_min_card : ∀ W ∈ W_cover, d_min ≤ W.card)
    (h_klarner_shell : ∀ s : ℕ,
      ((W_cover.filter (fun W => W.card = d_min + s)).card : ℝ) ≤ klarnerAnimalConst ^ (d_min + s)) :
    V.totalPerturbation = scaleSplitTruncatedOp V R_cut + scaleSplitTailOp V R_cut ∧
    gibbsFailureProb (sys.H0 + scaleSplitTruncatedOp V R_cut)
      hH_trunc β (1 - indexedBareFailureProjector sys S_safe) ≤
      2 * Real.exp (-(c_wt * (3 / 2 : ℝ) * Δ_0 * (β - criticalInverseTempHier Δ_0)) * (((L ^ 3 : ℕ) : ℝ) ^ η)) ∧
    gibbsFailureProb ((sys.H0 + scaleSplitTruncatedOp V R_cut) + scaleSplitTailOp V R_cut)
      hH_full β (1 - indexedBareFailureProjector sys S_safe) ≤
      scaleSplitMasterUpperBound L η (c_wt * (3 / 2 : ℝ) * Δ_0) β
        (criticalInverseTempHier Δ_0) 1 J (perturbationTailSeries f R_cut) ∧
    gibbsFailureProb ((sys.H0 + scaleSplitTruncatedOp V R_cut) + scaleSplitTailOp V R_cut)
      hH_full β (1 - indexedBareFailureProjector sys S_safe) ≤
      scaleSplitMasterUpperBound L η (c_wt * (3 / 2 : ℝ) * Δ_0) β
        (criticalInverseTempHier Δ_0) 1 J ((Real.pi ^ 2 / 6) * M_5 / ((R_cut : ℝ) ^ 3)) ∧
    (∀ r_pert : ℕ, InPerturbationClassFin f r_pert → r_pert ≤ R_cut →
      gibbsFailureProb ((sys.H0 + scaleSplitTruncatedOp V R_cut) + scaleSplitTailOp V R_cut)
        hH_full β (1 - indexedBareFailureProjector sys S_safe) ≤
        2 * Real.exp (-(c_wt * (3 / 2 : ℝ) * Δ_0 * (β - criticalInverseTempHier Δ_0)) *
          (((L ^ 3 : ℕ) : ℝ) ^ η))) := by
  have hβ_pos : 0 < β := by
    have h_gt : (1 : ℝ) < klarnerAnimalConst := by
      unfold klarnerAnimalConst; linarith [Real.one_le_exp zero_le_one]
    have h_log : 0 < Real.log klarnerAnimalConst := Real.log_pos h_gt
    exact lt_trans (by unfold criticalInverseTempHier; positivity) hβ
  have h_vtot : V.totalPerturbation = scaleSplitTruncatedOp V R_cut + scaleSplitTailOp V R_cut := by
    unfold QuasiLocalPerturbation.totalPerturbation scaleSplitTruncatedOp scaleSplitTailOp
    have h1 : Finset.Icc 1 (min R_cut L) = (Finset.Icc 1 L).filter (· ≤ R_cut) := by
      ext r; simp only [Finset.mem_Icc, Finset.mem_filter, le_min_iff]; omega
    have h2 : (Finset.Icc 1 L).filter (R_cut < ·) = (Finset.Icc 1 L).filter (¬ · ≤ R_cut) := by
      ext r; simp only [Finset.mem_filter, not_le]
    rw [h1, h2, Finset.sum_filter_add_sum_filter_not]
  have h_tail_sa : IsSelfAdjoint (scaleSplitTailOp V R_cut) :=
    _root_.isSelfAdjoint_finset_sum _ _ fun r _ => _root_.isSelfAdjoint_finset_sum _ _ fun A _ => V.is_selfAdjoint r A
  have h_tail_norm : ‖scaleSplitTailOp V R_cut‖ ≤ 1 * J * ((L ^ 3 : ℕ) : ℝ) * perturbationTailSeries f R_cut := by
    simpa [one_mul] using scaleSplitTailOp_norm_le V J f R_cut hJ_nonneg hM5.1 h_summable h_ql
  have h_rca := rcaCollarConstant_le_pi_sq_div_six_mul_moment5 f c_chk r_0 C_RCA M_5
    hc_chk hr_0 hC_RCA hM5
  let P_unsafe := 1 - indexedBareFailureProjector sys S_safe
  have hP_proj : IsStarProjection P_unsafe := (indexedBareFailureProjector_props sys S_safe).1.one_sub
  have h_weyl := (duhamelWeyl_relative_partition_ratio_bound β
    (sys.H0 + scaleSplitTruncatedOp V R_cut) (scaleSplitTailOp V R_cut) P_unsafe
    hβ_pos.le hH_trunc h_tail_sa hH_full hP_proj).2
  have h_trunc := (directWorldline_truncated_gibbsFailureProb_le
    sys (sys.H0 + scaleSplitTruncatedOp V R_cut) hH_trunc f R_cut d_min
    η c_wt Δ_0 Δ_RCA C_wl c_wl β J S_safe W_cover
    hc_wt hΔ_0 hΔ_RCA hJ_nonneg hJ_wl hJ_span h_sum_pos hβ hd_min
    h_cover h_witness_raw h_min_card h_klarner_shell).2
  have h_exp_mono1 :
      Real.exp (2 * β * ‖scaleSplitTailOp V R_cut‖) ≤
        Real.exp (2 * β * (1 * J * ((L ^ 3 : ℕ) : ℝ) * perturbationTailSeries f R_cut)) :=
    Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left h_tail_norm (by linarith))
  have h_rhs_nonneg :
      0 ≤ 2 * Real.exp (-(c_wt * (3 / 2 : ℝ) * Δ_0) *
        (β - criticalInverseTempHier Δ_0) * (((L ^ 3 : ℕ) : ℝ) ^ η)) := by positivity
  have h_master1 :
      gibbsFailureProb ((sys.H0 + scaleSplitTruncatedOp V R_cut) + scaleSplitTailOp V R_cut)
        hH_full β P_unsafe ≤
        scaleSplitMasterUpperBound L η (c_wt * (3 / 2 : ℝ) * Δ_0) β
          (criticalInverseTempHier Δ_0) 1 J (perturbationTailSeries f R_cut) := by
    unfold scaleSplitMasterUpperBound; (try dsimp only)
    calc gibbsFailureProb ((sys.H0 + scaleSplitTruncatedOp V R_cut) + scaleSplitTailOp V R_cut)
          hH_full β P_unsafe
        ≤ Real.exp (2 * β * ‖scaleSplitTailOp V R_cut‖) *
            gibbsFailureProb (sys.H0 + scaleSplitTruncatedOp V R_cut) hH_trunc β P_unsafe +
            (Real.exp (2 * β * ‖scaleSplitTailOp V R_cut‖) - 1) := h_weyl
      _ ≤ Real.exp (2 * β * ‖scaleSplitTailOp V R_cut‖) *
            (2 * Real.exp (-(c_wt * (3 / 2 : ℝ) * Δ_0 *
              (β - criticalInverseTempHier Δ_0)) * (((L ^ 3 : ℕ) : ℝ) ^ η))) +
            (Real.exp (2 * β * ‖scaleSplitTailOp V R_cut‖) - 1) := by
          linarith [mul_le_mul_of_nonneg_left h_trunc (Real.exp_pos (2 * β * ‖scaleSplitTailOp V R_cut‖)).le]
      _ = Real.exp (2 * β * ‖scaleSplitTailOp V R_cut‖) *
            (2 * Real.exp (-(c_wt * (3 / 2 : ℝ) * Δ_0) *
              (β - criticalInverseTempHier Δ_0) * (((L ^ 3 : ℕ) : ℝ) ^ η))) +
            (Real.exp (2 * β * ‖scaleSplitTailOp V R_cut‖) - 1) := by ring_nf
      _ ≤ Real.exp (2 * β * (1 * J * ((L ^ 3 : ℕ) : ℝ) * perturbationTailSeries f R_cut)) *
            (2 * Real.exp (-(c_wt * (3 / 2 : ℝ) * Δ_0) *
              (β - criticalInverseTempHier Δ_0) * (((L ^ 3 : ℕ) : ℝ) ^ η))) +
            (Real.exp (2 * β * (1 * J * ((L ^ 3 : ℕ) : ℝ) * perturbationTailSeries f R_cut)) - 1) := by
          linarith [mul_le_mul_of_nonneg_right h_exp_mono1 h_rhs_nonneg]
      _ = 2 * Real.exp (2 * β * (1 * J * ((L ^ 3 : ℕ) : ℝ) * perturbationTailSeries f R_cut)) *
            Real.exp (-(c_wt * (3 / 2 : ℝ) * Δ_0) *
              (β - criticalInverseTempHier Δ_0) * (((L ^ 3 : ℕ) : ℝ) ^ η)) +
            (Real.exp (2 * β * (1 * J * ((L ^ 3 : ℕ) : ℝ) * perturbationTailSeries f R_cut)) - 1) := by ring
  have h_master2 :
      scaleSplitMasterUpperBound L η (c_wt * (3 / 2 : ℝ) * Δ_0) β
        (criticalInverseTempHier Δ_0) 1 J (perturbationTailSeries f R_cut) ≤
      scaleSplitMasterUpperBound L η (c_wt * (3 / 2 : ℝ) * Δ_0) β
        (criticalInverseTempHier Δ_0) 1 J ((Real.pi ^ 2 / 6) * M_5 / ((R_cut : ℝ) ^ 3)) := by
    unfold scaleSplitMasterUpperBound; (try dsimp only)
    have h_tail_m5 := h_rca.2.2.2.1 R_cut hR_cut
    have h_coeff_nonneg : 0 ≤ 2 * β * (1 * J * ((L ^ 3 : ℕ) : ℝ)) := by positivity
    have h_exp_m5 :
        Real.exp (2 * β * (1 * J * ((L ^ 3 : ℕ) : ℝ) * perturbationTailSeries f R_cut)) ≤
          Real.exp (2 * β * (1 * J * ((L ^ 3 : ℕ) : ℝ) *
            ((Real.pi ^ 2 / 6) * M_5 / ((R_cut : ℝ) ^ 3)))) := by
      apply Real.exp_le_exp.mpr
      linarith [mul_le_mul_of_nonneg_left h_tail_m5 h_coeff_nonneg]
    have h_exp_pos :
        0 ≤ Real.exp (-(c_wt * (3 / 2 : ℝ) * Δ_0) *
          (β - criticalInverseTempHier Δ_0) * (((L ^ 3 : ℕ) : ℝ) ^ η)) := (Real.exp_pos _).le
    linarith [mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left h_exp_m5 (by norm_num : (0 : ℝ) ≤ 2)) h_exp_pos]
  have h_fin_regime : ∀ r_pert : ℕ, InPerturbationClassFin f r_pert → r_pert ≤ R_cut →
      gibbsFailureProb ((sys.H0 + scaleSplitTruncatedOp V R_cut) + scaleSplitTailOp V R_cut)
        hH_full β P_unsafe ≤
        2 * Real.exp (-(c_wt * (3 / 2 : ℝ) * Δ_0 * (β - criticalInverseTempHier Δ_0)) *
          (((L ^ 3 : ℕ) : ℝ) ^ η)) := by
    intro r_pert h_fin hr_le
    have h_zero := h_rca.2.2.2.2 r_pert R_cut h_fin hr_le
    have h_eval :
        scaleSplitMasterUpperBound L η (c_wt * (3 / 2 : ℝ) * Δ_0) β
          (criticalInverseTempHier Δ_0) 1 J (perturbationTailSeries f R_cut) =
        2 * Real.exp (-(c_wt * (3 / 2 : ℝ) * Δ_0 * (β - criticalInverseTempHier Δ_0)) *
          (((L ^ 3 : ℕ) : ℝ) ^ η)) := by
      unfold scaleSplitMasterUpperBound; (try dsimp only)
      rw [h_zero, mul_zero, mul_zero, Real.exp_zero, mul_one, sub_self, add_zero]; ring_nf
    exact h_eval ▸ h_master1
  exact ⟨h_vtot, h_trunc, h_master1, le_trans h_master1 h_master2, h_fin_regime⟩

/-- Positivity of `worldlineNativeKPSum` is independent of `β`. -/
lemma worldlineNativeKPSum_pos_of_pos (f : ℕ → ℝ) (C_wl c_wl β₀ β : ℝ) (R_cut : ℕ)
    (hC_wl : 0 ≤ C_wl) (hf : ∀ r, 0 ≤ f r)
    (h_pos : 0 < worldlineNativeKPSum f C_wl c_wl β₀ R_cut) :
    0 < worldlineNativeKPSum f C_wl c_wl β R_cut := by
  by_contra h_le; push_neg at h_le
  have h_nn : ∀ r ∈ Finset.Icc 1 R_cut,
      0 ≤ C_wl * ((r : ℝ) ^ 6) * f r * Real.exp (c_wl * (1 + β) * ((r : ℝ) ^ 3)) :=
    fun r _ => mul_nonneg (mul_nonneg (mul_nonneg hC_wl (by positivity)) (hf r)) (Real.exp_pos _).le
  have h_eq_zero := (Finset.sum_eq_zero_iff_of_nonneg h_nn).mp (le_antisymm h_le (Finset.sum_nonneg h_nn))
  have h_zero₀ : worldlineNativeKPSum f C_wl c_wl β₀ R_cut = 0 := by
    unfold worldlineNativeKPSum
    refine Finset.sum_eq_zero fun r hr => ?_
    rcases mul_eq_zero.mp (h_eq_zero r hr) with h1 | h2
    · rw [h1, zero_mul]
    · exact False.elim ((Real.exp_pos _).ne' h2)
  linarith

/-- Window threshold persistence (Part II, Section 6.3 (`subsec:main-theorems`), Proposition 3.10 (`prop:tube-local-ursell-erasure`), Equation `eq:J-span-full-def`, and Section 5.1 (`subsec:direct-worldline-synthesis`), Theorem 5.1 (`thm:direct-worldline-intact-cluster-erasure`)):
If `J ≤ worldlineSpanningThreshold Δ_RCA C_wl c_wl (2 * criticalInverseTempHier Δ_0) f R_cut` and
`β ≤ lowTempWindowBetaMax ...`, then `J ≤ worldlineSpanningThreshold Δ_RCA C_wl c_wl β f R_cut`. -/
theorem worldlineSpanningThreshold_ge_of_beta_le_windowMax
    (f : ℕ → ℝ) (R_cut : ℕ) (Δ_0 Δ_RCA C_wl c_wl β J : ℝ)
    (hf : ∀ r, 0 ≤ f r) (hC_wl : 0 ≤ C_wl) (hc_wl : 0 ≤ c_wl)
    (h_beta_c_ge : 1 / 2 ≤ criticalInverseTempHier Δ_0) (hJ_pos : 0 < J)
    (hJ_hier : J ≤ worldlineSpanningThreshold Δ_RCA C_wl c_wl (2 * criticalInverseTempHier Δ_0) f R_cut)
    (h_sum_pos : 0 < worldlineNativeKPSum f C_wl c_wl (2 * criticalInverseTempHier Δ_0) R_cut)
    (hβ_max : β ≤ lowTempWindowBetaMax (criticalInverseTempHier Δ_0) c_wl R_cut
      (worldlineSpanningThreshold Δ_RCA C_wl c_wl (2 * criticalInverseTempHier Δ_0) f R_cut) J) :
    let J_span_hier := worldlineSpanningThreshold Δ_RCA C_wl c_wl (2 * criticalInverseTempHier Δ_0) f R_cut
    0 < worldlineNativeKPSum f C_wl c_wl β R_cut ∧
    2 * criticalInverseTempHier Δ_0 ≤ lowTempWindowBetaMax (criticalInverseTempHier Δ_0) c_wl R_cut J_span_hier J ∧
    J ≤ worldlineSpanningThreshold Δ_RCA C_wl c_wl β f R_cut := by
  intro J_span_hier
  let β₀ := 2 * criticalInverseTempHier Δ_0
  have hβ₀_ge_one : 1 ≤ β₀ := by dsimp [β₀]; linarith
  have h_sum_β : 0 < worldlineNativeKPSum f C_wl c_wl β R_cut :=
    worldlineNativeKPSum_pos_of_pos f C_wl c_wl β₀ β R_cut hC_wl hf h_sum_pos
  have h_log_nn : 0 ≤ Real.log (J_span_hier / J) := Real.log_nonneg ((one_le_div hJ_pos).mpr hJ_hier)
  have h_denom_pos : 0 < c_wl * ((R_cut : ℝ) ^ 3) + 1 := by positivity
  have h_win : β₀ ≤ lowTempWindowBetaMax (criticalInverseTempHier Δ_0) c_wl R_cut J_span_hier J := by
    unfold lowTempWindowBetaMax
    have h_term : 0 ≤ (1 / (c_wl * ((R_cut : ℝ) ^ 3) + 1)) * Real.log (J_span_hier / J) := by positivity
    dsimp [β₀]; linarith
  refine ⟨h_sum_β, h_win, ?_⟩
  unfold worldlineSpanningThreshold
  refine le_min (le_trans hJ_hier (min_le_left _ _)) ?_
  have hJ_hier_right :
      J_span_hier ≤ 1 / (64 * Real.exp 1 * max 1 β₀ * worldlineNativeKPSum f C_wl c_wl β₀ R_cut) :=
    min_le_right _ _
  let D₀ := 64 * Real.exp 1 * max 1 β₀ * worldlineNativeKPSum f C_wl c_wl β₀ R_cut
  let D_β := 64 * Real.exp 1 * max 1 β * worldlineNativeKPSum f C_wl c_wl β R_cut
  have hD₀_pos : 0 < D₀ := by dsimp [D₀]; positivity
  have hD_β_pos : 0 < D_β := by dsimp [D_β]; positivity
  have hJ_D₀ : J_span_hier * D₀ ≤ 1 := (le_div_iff₀ hD₀_pos).mp hJ_hier_right
  rw [le_div_iff₀ hD_β_pos]
  by_cases h_le : β ≤ β₀
  · have h_max_le : max 1 β ≤ max 1 β₀ := max_le_max le_rfl h_le
    have h_sum_le : worldlineNativeKPSum f C_wl c_wl β R_cut ≤ worldlineNativeKPSum f C_wl c_wl β₀ R_cut := by
      unfold worldlineNativeKPSum
      refine Finset.sum_le_sum fun r _ => ?_
      refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_)
        (mul_nonneg (mul_nonneg hC_wl (by positivity)) (hf r))
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (by linarith) hc_wl) (by positivity)
    have hD_le : D_β ≤ D₀ := by
      dsimp [D_β, D₀]
      exact mul_le_mul (mul_le_mul_of_nonneg_left h_max_le (by positivity)) h_sum_le h_sum_β.le (by positivity)
    exact le_trans (mul_le_mul hJ_hier hD_le hD_β_pos.le (le_trans hJ_pos.le hJ_hier)) hJ_D₀
  · push_neg at h_le
    let Δβ := β - β₀
    have hΔβ_pos : 0 < Δβ := sub_pos.mpr h_le
    have h_β_le_exp : max 1 β ≤ max 1 β₀ * Real.exp Δβ := by
      rw [max_eq_right hβ₀_ge_one, max_eq_right (le_trans hβ₀_ge_one h_le.le)]
      have h_add : β ≤ β₀ * (1 + Δβ) := by dsimp [Δβ]; nlinarith
      exact le_trans h_add (mul_le_mul_of_nonneg_left (by linarith [Real.add_one_le_exp Δβ]) (by linarith))
    have h_sum_exp :
        worldlineNativeKPSum f C_wl c_wl β R_cut ≤
          worldlineNativeKPSum f C_wl c_wl β₀ R_cut * Real.exp (c_wl * ((R_cut : ℝ) ^ 3) * Δβ) := by
      unfold worldlineNativeKPSum; rw [Finset.sum_mul]
      refine Finset.sum_le_sum fun r hr => ?_
      rw [mul_assoc (C_wl * (r : ℝ) ^ 6 * f r), ← Real.exp_add]
      refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_)
        (mul_nonneg (mul_nonneg hC_wl (by positivity)) (hf r))
      have hr_le : (r : ℝ) ≤ (R_cut : ℝ) := by exact_mod_cast (Finset.mem_Icc.mp hr).2
      have hr3_le : (r : ℝ) ^ 3 ≤ (R_cut : ℝ) ^ 3 := pow_le_pow_left₀ (Nat.cast_nonneg r) hr_le 3
      have h_mul_r := mul_le_mul_of_nonneg_left hr3_le (mul_nonneg hc_wl hΔβ_pos.le)
      dsimp [Δβ] at h_mul_r ⊢; linarith
    have hD_exp : D_β ≤ D₀ * Real.exp ((c_wl * ((R_cut : ℝ) ^ 3) + 1) * Δβ) := by
      calc D_β
        _ ≤ 64 * Real.exp 1 * (max 1 β₀ * Real.exp Δβ) *
              (worldlineNativeKPSum f C_wl c_wl β₀ R_cut * Real.exp (c_wl * ((R_cut : ℝ) ^ 3) * Δβ)) :=
            mul_le_mul (mul_le_mul_of_nonneg_left h_β_le_exp (by positivity)) h_sum_exp h_sum_β.le (by positivity)
        _ = D₀ * (Real.exp Δβ * Real.exp (c_wl * ((R_cut : ℝ) ^ 3) * Δβ)) := by dsimp [D₀]; ring
        _ = D₀ * Real.exp ((c_wl * ((R_cut : ℝ) ^ 3) + 1) * Δβ) := by rw [← Real.exp_add]; congr 2; ring
    have h_log_bound : (c_wl * ((R_cut : ℝ) ^ 3) + 1) * Δβ ≤ Real.log (J_span_hier / J) := by
      unfold lowTempWindowBetaMax at hβ_max
      have h_sub : Δβ ≤ (1 / (c_wl * ((R_cut : ℝ) ^ 3) + 1)) * Real.log (J_span_hier / J) := by
        dsimp [Δβ, β₀]; linarith
      have h_mul := mul_le_mul_of_nonneg_left h_sub h_denom_pos.le
      rwa [← mul_assoc, mul_one_div_cancel h_denom_pos.ne', one_mul] at h_mul
    have h_exp_bound : Real.exp ((c_wl * ((R_cut : ℝ) ^ 3) + 1) * Δβ) ≤ J_span_hier / J := by
      rw [← Real.exp_log (div_pos (lt_of_lt_of_le hJ_pos hJ_hier) hJ_pos)]
      exact Real.exp_le_exp.mpr h_log_bound
    have hJ_exp : J * Real.exp ((c_wl * ((R_cut : ℝ) ^ 3) + 1) * Δβ) ≤ J_span_hier := by
      rw [mul_comm]; exact (le_div_iff₀ hJ_pos).mp h_exp_bound
    calc J * D_β
      _ ≤ J * (D₀ * Real.exp ((c_wl * ((R_cut : ℝ) ^ 3) + 1) * Δβ)) :=
          mul_le_mul_of_nonneg_left hD_exp hJ_pos.le
      _ = (J * Real.exp ((c_wl * ((R_cut : ℝ) ^ 3) + 1) * Δβ)) * D₀ := by ring
      _ ≤ J_span_hier * D₀ := mul_le_mul_of_nonneg_right hJ_exp hD₀_pos.le
      _ ≤ 1 := hJ_D₀

/-- Unitary conjugation invariance of `gibbsFailureProb`. -/
theorem gibbsFailureProb_unitary_conj_eq {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)] [∀ x, Nonempty (Site x)]
    (H H_d P : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site)
    (U : unitary (ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site))
    (hH : IsSelfAdjoint H) (hH_d : IsSelfAdjoint H_d) (β : ℝ) (h_conj : H = U.1 * H_d * U.1†) :
    gibbsFailureProb H hH β (1 - U.1 * P * U.1†) = gibbsFailureProb H_d hH_d β (1 - P) := by
  let ψ := opEigenbasis H_d hH_d; let E := opEigenvalues H_d hH_d
  let ψ' : ManyBodyConfig Site → ManyBodyHilbertSpace Site := fun ω => U.1 (ψ ω)
  have hU_star_mul : U.1† * U.1 = 1 := Unitary.coe_star_mul_self U
  have hU_mul_star : U.1 * U.1† = 1 := Unitary.coe_mul_star_self U
  have hU_cancel : ∀ x : ManyBodyHilbertSpace Site, (U.1†) (U.1 x) = x := fun x => by
    change (U.1† * U.1) x = x; rw [hU_star_mul, ContinuousLinearMap.one_apply]
  have h_onb' : ∀ ω₁ ω₂ : ManyBodyConfig Site, inner ℂ (ψ' ω₁) (ψ' ω₂) = if ω₁ = ω₂ then 1 else 0 := by
    intro ω₁ ω₂; dsimp only [ψ']
    rw [← ContinuousLinearMap.adjoint_inner_left,
      show ContinuousLinearMap.adjoint U.1 = U.1† from rfl, hU_cancel, opEigenbasis_orthonormal H_d hH_d]
  have h_eig' : ∀ ω : ManyBodyConfig Site, H (ψ' ω) = ((E ω : ℝ) : ℂ) • ψ' ω := by
    intro ω; dsimp only [ψ']
    rw [h_conj, ContinuousLinearMap.mul_apply, ContinuousLinearMap.mul_apply,
      hU_cancel, opEigenbasis_apply_H H_d hH_d ω, map_smul]
  have h_one_sub : 1 - U.1 * P * U.1† = U.1 * (1 - P) * U.1† := by rw [mul_sub, mul_one, sub_mul, hU_mul_star]
  have h_inner_eq : ∀ ω : ManyBodyConfig Site,
      inner ℂ (ψ' ω) ((1 - U.1 * P * U.1†) (ψ' ω)) = inner ℂ (ψ ω) ((1 - P) (ψ ω)) := by
    intro ω; rw [h_one_sub]; dsimp only [ψ']
    rw [ContinuousLinearMap.mul_apply, ContinuousLinearMap.mul_apply, hU_cancel,
      ← ContinuousLinearMap.adjoint_inner_left, show ContinuousLinearMap.adjoint U.1 = U.1† from rfl, hU_cancel]
  have h_tr_num := perturbed_hilbertTrace_gibbsBoltzmannOp_eq_sum_any_orthonormal_eigenbasis
    H hH ψ' E h_onb' h_eig' β (1 - U.1 * P * U.1†)
  have h_tr_num_d := perturbed_hilbertTrace_gibbsBoltzmannOp_eq_sum_any_orthonormal_eigenbasis
    H_d hH_d ψ E (opEigenbasis_orthonormal H_d hH_d) (opEigenbasis_apply_H H_d hH_d) β (1 - P)
  have h_num_eq :
      hilbertTrace (gibbsBoltzmannOp (opEigenbasis H hH) (opEigenvalues H hH) β * (1 - U.1 * P * U.1†)) =
        hilbertTrace (gibbsBoltzmannOp ψ E β * (1 - P)) := by
    rw [h_tr_num, h_tr_num_d]; exact Finset.sum_congr rfl fun ω _ => by rw [h_inner_eq ω]
  have h_tr_Z := perturbed_hilbertTrace_gibbsBoltzmannOp_eq_sum_any_orthonormal_eigenbasis H hH ψ' E h_onb' h_eig' β 1
  have h_tr_Z_d := perturbed_hilbertTrace_gibbsBoltzmannOp_eq_sum_any_orthonormal_eigenbasis
    H_d hH_d ψ E (opEigenbasis_orthonormal H_d hH_d) (opEigenbasis_apply_H H_d hH_d) β 1
  have h_Z_eq : gibbsPartitionZ (opEigenvalues H hH) β = gibbsPartitionZ E β := by
    have h_tr_eq :
        hilbertTrace (gibbsBoltzmannOp (opEigenbasis H hH) (opEigenvalues H hH) β * 1) =
          hilbertTrace (gibbsBoltzmannOp ψ E β * 1) := by
      rw [h_tr_Z, h_tr_Z_d]; refine Finset.sum_congr rfl fun ω _ => ?_
      rw [ContinuousLinearMap.one_apply, ContinuousLinearMap.one_apply, h_onb' ω ω, opEigenbasis_orthonormal H_d hH_d ω ω]
    have h1 : ∀ (H' : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site) (hH' : IsSelfAdjoint H'),
        hilbertTrace (gibbsBoltzmannOp (opEigenbasis H' hH') (opEigenvalues H' hH') β * 1) =
          gibbsPartitionZ (opEigenvalues H' hH') β := by
      intro H' hH'
      rw [perturbed_hilbertTrace_gibbsBoltzmannOp_eq_sum_any_orthonormal_eigenbasis
        H' hH' (opEigenbasis H' hH') (opEigenvalues H' hH')
        (opEigenbasis_orthonormal H' hH') (opEigenbasis_apply_H H' hH') β 1]
      unfold gibbsPartitionZ; refine Finset.sum_congr rfl fun ω _ => ?_
      have h_u := congrArg RCLike.re (opEigenbasis_orthonormal H' hH' ω ω)
      rw [if_pos rfl] at h_u
      rw [ContinuousLinearMap.one_apply, h_u, RCLike.re_to_complex, Complex.one_re, mul_one]
    rw [← h1 H hH, ← h1 H_d hH_d, h_tr_eq]
  rw [perturbed_gibbsFailureProb_eq_inv_gibbsPartitionZ_mul_boltzmann_trace H hH β,
    perturbed_gibbsFailureProb_eq_inv_gibbsPartitionZ_mul_boltzmann_trace H_d hH_d β, h_num_eq, h_Z_eq]

/-- Ground-space safety and deep low-temperature (`β > β_cross`) BHM gap bound for
    `(sys.H0 + scaleSplitTruncatedOp V_eff R_cut) + R_split`. -/
theorem bhm_dressed_ground_excited_gibbs_bound
    {D L : ℕ} {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    [∀ x, Nonempty (Site x)] {ι_chk : Type} [Fintype ι_chk] [DecidableEq ι_chk]
    (sys : IndexedCommutingProjectorHamiltonian D L Site ι_chk)
    (H_eff R_split : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site)
    (U_dress : unitary (ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site))
    (S_safe : Finset (ι_chk → Bool))
    (β β_cross δ_split E_0_bhm : ℝ) (hH_dressed : IsSelfAdjoint (H_eff + R_split))
    (hβ_pos : 0 ≤ β) (hδ_small : 2 * δ_split ≤ 1 / 8) (h_split_norm : ‖R_split‖ ≤ δ_split)
    (hP0_ne : sys.P0 ≠ 0) (hP0_safe : sys.P0 * indexedBareFailureProjector sys S_safe = sys.P0)
    (h_comm_eff_P0 : Commute H_eff sys.P0)
    (h_comm_split_P0 : Commute R_split sys.P0) (h_split_vac : R_split * sys.P0 = 0)
    (h_eff_vac : (H_eff - ((E_0_bhm : ℝ) : ℂ) • 1) * sys.P0 = 0)
    (h_eff_gap : ∀ ψ : ManyBodyHilbertSpace Site,
      (3 / 4 : ℝ) * ‖(1 - sys.P0) ψ‖ ^ 2 ≤
        RCLike.re (inner ℂ ((1 - sys.P0) ψ)
          ((H_eff - ((E_0_bhm : ℝ) : ℂ) • 1) ((1 - sys.P0) ψ))))
    (hβ_cross : 4 * Real.log (Fintype.card (ManyBodyConfig Site) : ℝ) ≤ β_cross) :
    let Pi_safe := indexedBareFailureProjector sys S_safe
    let Pi_safe_dress := U_dress.1 * Pi_safe * U_dress.1†
    let P0_dress := U_dress.1 * sys.P0 * U_dress.1†
    (1 - Pi_safe) * sys.P0 = 0 ∧ (1 - Pi_safe_dress) * P0_dress = 0 ∧
    (β_cross < β →
      gibbsFailureProb (H_eff + R_split) hH_dressed β (1 - Pi_safe) ≤ Real.exp (-(3 / 8 : ℝ) * β)) := by
  intro Pi_safe Pi_safe_dress P0_dress
  have hPi_safe : IsStarProjection Pi_safe := (indexedBareFailureProjector_props sys S_safe).1
  have hP0_proj : IsStarProjection sys.P0 := by
    have h_res := _root_.syndrome_resolution_indexed sys
    rw [← h_res.1]; exact h_res.2.1 (fun _ => false)
  have h_pi_p0 : Pi_safe * sys.P0 = sys.P0 := by
    have h_star := congrArg star hP0_safe; rw [star_mul, hPi_safe.2, hP0_proj.2] at h_star; exact h_star
  have h_unsafe_p0 : (1 - Pi_safe) * sys.P0 = 0 := by rw [sub_mul, one_mul, h_pi_p0, sub_self]
  have hU_star_mul : U_dress.1† * U_dress.1 = 1 := Unitary.coe_star_mul_self U_dress
  have hU_mul_star : U_dress.1 * U_dress.1† = 1 := Unitary.coe_mul_star_self U_dress
  have h_dress_p0 : (1 - Pi_safe_dress) * P0_dress = 0 := by
    dsimp [Pi_safe_dress, P0_dress]
    have h_sub : 1 - U_dress.1 * Pi_safe * U_dress.1† = U_dress.1 * (1 - Pi_safe) * U_dress.1† := by
      rw [mul_sub, mul_one, sub_mul, hU_mul_star]
    rw [h_sub]
    calc (U_dress.1 * (1 - Pi_safe) * U_dress.1†) * (U_dress.1 * sys.P0 * U_dress.1†)
      _ = U_dress.1 * (1 - Pi_safe) * (U_dress.1† * U_dress.1) * sys.P0 * U_dress.1† := by simp only [mul_assoc]
      _ = U_dress.1 * ((1 - Pi_safe) * sys.P0) * U_dress.1† := by
          rw [hU_star_mul, mul_one, mul_assoc U_dress.1 (1 - Pi_safe) sys.P0]
      _ = 0 := by rw [h_unsafe_p0, mul_zero, zero_mul]
  refine ⟨h_unsafe_p0, h_dress_p0, fun hβ_gt_cross => ?_⟩
  let H_d := H_eff + R_split; let ψ := opEigenbasis H_d hH_dressed
  let E := opEigenvalues H_d hH_dressed; let Z := gibbsPartitionZ E β
  have hZ_pos : 0 < Z := gibbsPartitionZ_pos E β
  have hHd_comm_P0 : Commute H_d sys.P0 := h_comm_eff_P0.add_left h_comm_split_P0
  have hHd_vac : (H_d - ((E_0_bhm : ℝ) : ℂ) • 1) * sys.P0 = 0 := by
    rw [show H_d - ((E_0_bhm : ℝ) : ℂ) • 1 = (H_eff - ((E_0_bhm : ℝ) : ℂ) • 1) + R_split from
      add_sub_right_comm H_eff R_split _, add_mul, h_eff_vac, h_split_vac, add_zero]
  have h_exists_ω₀ : ∃ ω₀ : ManyBodyConfig Site, sys.P0 (ψ ω₀) ≠ 0 := by
    by_contra h_all; push_neg at h_all; apply hP0_ne
    refine ContinuousLinearMap.ext fun φ => ?_
    rw [ContinuousLinearMap.zero_apply, ← norm_eq_zero]
    have h_sq : ‖sys.P0 φ‖ ^ 2 = 0 := by
      rw [← opEigenbasis_parseval H_d hH_dressed (sys.P0 φ)]
      refine Finset.sum_eq_zero fun ω _ => ?_
      have h_in : inner ℂ (ψ ω) (sys.P0 φ) = 0 := by
        rw [← ContinuousLinearMap.adjoint_inner_left,
          ContinuousLinearMap.isSelfAdjoint_iff'.mp hP0_proj.isSelfAdjoint, h_all ω, inner_zero_left]
      rw [h_in, norm_zero, sq, mul_zero]
    exact sq_eq_zero_iff.mp h_sq
  rcases h_exists_ω₀ with ⟨ω₀, hω₀_ne⟩
  have hE_ω₀ : E ω₀ = E_0_bhm := by
    have h1 : (H_d - ((E_0_bhm : ℝ) : ℂ) • 1) (sys.P0 (ψ ω₀)) = 0 := by
      change ((H_d - ((E_0_bhm : ℝ) : ℂ) • 1) * sys.P0) (ψ ω₀) = 0
      rw [hHd_vac, ContinuousLinearMap.zero_apply]
    have h2 : H_d (sys.P0 (ψ ω₀)) = ((E ω₀ : ℝ) : ℂ) • sys.P0 (ψ ω₀) := by
      change (H_d * sys.P0) (ψ ω₀) = _
      rw [hHd_comm_P0.eq, ContinuousLinearMap.mul_apply, opEigenbasis_apply_H H_d hH_dressed ω₀, map_smul]
    rw [ContinuousLinearMap.sub_apply, h2, ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.one_apply, ← sub_smul, smul_eq_zero] at h1
    rcases h1 with h_scalar | h_vec
    · exact sub_eq_zero.mp (Complex.ofReal_injective (by simpa using h_scalar))
    · exact False.elim (hω₀_ne h_vec)
  have hZ_ge : Real.exp (-β * E_0_bhm) ≤ Z := by
    rw [← hE_ω₀]
    exact Finset.single_le_sum (f := fun ω => Real.exp (-β * E ω))
      (fun _ _ => (Real.exp_pos _).le) (Finset.mem_univ ω₀)
  have hP_unsafe : IsStarProjection (1 - Pi_safe) := hPi_safe.one_sub
  have h_term_bound : ∀ ω : ManyBodyConfig Site,
      Real.exp (-β * E ω) * RCLike.re (inner ℂ (ψ ω) ((1 - Pi_safe) (ψ ω))) ≤
        Real.exp (-(5 / 8 : ℝ) * β) * Z := by
    intro ω
    let φ := (1 - sys.P0) (ψ ω)
    have h_unsafe_eq : (1 - Pi_safe) (ψ ω) = (1 - Pi_safe) φ := by
      have h_id : ψ ω = sys.P0 (ψ ω) + φ := by
        dsimp [φ]; rw [ContinuousLinearMap.sub_apply, ContinuousLinearMap.one_apply, add_sub_cancel]
      conv_lhs => rw [h_id, map_add]
      have h_zero : (1 - Pi_safe) (sys.P0 (ψ ω)) = 0 := by
        change ((1 - Pi_safe) * sys.P0) (ψ ω) = 0; rw [h_unsafe_p0, ContinuousLinearMap.zero_apply]
      rw [h_zero, zero_add]
    by_cases hφ_zero : ‖φ‖ = 0
    · rw [isStarProjection_re_inner_eq_norm_sq hP_unsafe (ψ ω), h_unsafe_eq,
        norm_eq_zero.mp hφ_zero, map_zero, norm_zero, sq, mul_zero, mul_zero]
      exact mul_nonneg (Real.exp_pos _).le hZ_pos.le
    · have hφ_pos : 0 < ‖φ‖ ^ 2 := sq_pos_of_ne_zero hφ_zero
      have hHd_comm_Q0 : Commute H_d (1 - sys.P0) := (Commute.one_right H_d).sub_right hHd_comm_P0
      have hHd_φ : (H_d - ((E_0_bhm : ℝ) : ℂ) • 1) φ = ((E ω - E_0_bhm : ℝ) : ℂ) • φ := by
        rw [ContinuousLinearMap.sub_apply, ContinuousLinearMap.smul_apply, ContinuousLinearMap.one_apply]
        have h_app : H_d φ = ((E ω : ℝ) : ℂ) • φ := by
          change (H_d * (1 - sys.P0)) (ψ ω) = ((E ω : ℝ) : ℂ) • φ
          rw [hHd_comm_Q0.eq, ContinuousLinearMap.mul_apply, opEigenbasis_apply_H H_d hH_dressed ω, map_smul]
        rw [h_app, Complex.ofReal_sub, sub_smul]
      have h_re_lhs : RCLike.re (inner ℂ φ ((H_d - ((E_0_bhm : ℝ) : ℂ) • 1) φ)) =
          (E ω - E_0_bhm) * ‖φ‖ ^ 2 := by
        rw [hHd_φ, inner_smul_right, re_ofReal_mul, inner_self_eq_norm_sq]
      have h_re_split :
          RCLike.re (inner ℂ φ ((H_d - ((E_0_bhm : ℝ) : ℂ) • 1) φ)) =
            RCLike.re (inner ℂ φ ((H_eff - ((E_0_bhm : ℝ) : ℂ) • 1) φ)) +
              RCLike.re (inner ℂ φ (R_split φ)) := by
        have h_op : H_d - ((E_0_bhm : ℝ) : ℂ) • 1 = (H_eff - ((E_0_bhm : ℝ) : ℂ) • 1) + R_split := by
          dsimp [H_d]; abel
        rw [h_op, ContinuousLinearMap.add_apply, inner_add_right, map_add]
      have h_R_bound : -(δ_split * ‖φ‖ ^ 2) ≤ RCLike.re (inner ℂ φ (R_split φ)) := by
        refine (abs_le.mp ?_).1
        calc |RCLike.re (inner ℂ φ (R_split φ))|
          _ ≤ ‖inner ℂ φ (R_split φ)‖ := RCLike.abs_re_le_norm _
          _ ≤ ‖φ‖ * ‖R_split φ‖ := norm_inner_le_norm _ _
          _ ≤ ‖φ‖ * (‖R_split‖ * ‖φ‖) :=
              mul_le_mul_of_nonneg_left (ContinuousLinearMap.le_opNorm R_split φ) (norm_nonneg _)
          _ = ‖R_split‖ * ‖φ‖ ^ 2 := by ring
          _ ≤ δ_split * ‖φ‖ ^ 2 := mul_le_mul_of_nonneg_right h_split_norm (sq_nonneg _)
      have h_gap_mul : (5 / 8 : ℝ) * ‖φ‖ ^ 2 ≤ (E ω - E_0_bhm) * ‖φ‖ ^ 2 := by
        have h_eff : (3 / 4 : ℝ) * ‖φ‖ ^ 2 ≤
            RCLike.re (inner ℂ φ ((H_eff - ((E_0_bhm : ℝ) : ℂ) • 1) φ)) := h_eff_gap (ψ ω)
        have h_δ_le : δ_split * ‖φ‖ ^ 2 ≤ (1 / 8 : ℝ) * ‖φ‖ ^ 2 :=
          mul_le_mul_of_nonneg_right (by linarith) (sq_nonneg _)
        linarith
      have hE_gap : E_0_bhm + 5 / 8 ≤ E ω := by linarith [le_of_mul_le_mul_right h_gap_mul hφ_pos]
      have h_re_le_one : RCLike.re (inner ℂ (ψ ω) ((1 - Pi_safe) (ψ ω))) ≤ 1 := by
        rw [isStarProjection_re_inner_eq_norm_sq hP_unsafe (ψ ω)]
        have h_le := isStarProjection_norm_sq_apply_le hP_unsafe (ψ ω)
        have h_unit : ‖ψ ω‖ ^ 2 = 1 := by
          have h1 := congrArg RCLike.re (opEigenbasis_orthonormal H_d hH_dressed ω ω)
          rw [if_pos rfl, inner_self_eq_norm_sq] at h1; simpa using h1
        rwa [h_unit] at h_le
      have h_exp_le : Real.exp (-β * E ω) ≤ Real.exp (-(5 / 8 : ℝ) * β) * Real.exp (-β * E_0_bhm) := by
        rw [← Real.exp_add]; exact Real.exp_le_exp.mpr (by nlinarith)
      calc Real.exp (-β * E ω) * RCLike.re (inner ℂ (ψ ω) ((1 - Pi_safe) (ψ ω)))
        _ ≤ Real.exp (-β * E ω) * 1 := mul_le_mul_of_nonneg_left h_re_le_one (Real.exp_pos _).le
        _ = Real.exp (-β * E ω) := mul_one _
        _ ≤ Real.exp (-(5 / 8 : ℝ) * β) * Real.exp (-β * E_0_bhm) := h_exp_le
        _ ≤ Real.exp (-(5 / 8 : ℝ) * β) * Z := mul_le_mul_of_nonneg_left hZ_ge (Real.exp_pos _).le
  rw [perturbed_gibbsFailureProb_eq_inv_gibbsPartitionZ_mul_boltzmann_trace H_d hH_dressed β (1 - Pi_safe),
    hilbertTrace_gibbsBoltzmannOp_mul_eq]
  let N_card := (Fintype.card (ManyBodyConfig Site) : ℝ)
  have hN_pos : 0 < N_card := Nat.cast_pos.mpr Fintype.card_pos
  have h_sum_le :
      (∑ ω : ManyBodyConfig Site, Real.exp (-β * E ω) * RCLike.re (inner ℂ (ψ ω) ((1 - Pi_safe) (ψ ω)))) ≤
        N_card * Real.exp (-(5 / 8 : ℝ) * β) * Z := by
    calc (∑ ω : ManyBodyConfig Site, Real.exp (-β * E ω) * RCLike.re (inner ℂ (ψ ω) ((1 - Pi_safe) (ψ ω))))
      _ ≤ ∑ _ω : ManyBodyConfig Site, Real.exp (-(5 / 8 : ℝ) * β) * Z := Finset.sum_le_sum fun ω _ => h_term_bound ω
      _ = N_card * Real.exp (-(5 / 8 : ℝ) * β) * Z := by rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_assoc]
  have h_prob_le_N :
      Z⁻¹ * (∑ ω : ManyBodyConfig Site, Real.exp (-β * E ω) * RCLike.re (inner ℂ (ψ ω) ((1 - Pi_safe) (ψ ω)))) ≤
        N_card * Real.exp (-(5 / 8 : ℝ) * β) := by
    have h_mul := mul_le_mul_of_nonneg_left h_sum_le (inv_nonneg.mpr hZ_pos.le)
    rwa [mul_comm (N_card * Real.exp (-(5 / 8 : ℝ) * β)) Z, inv_mul_cancel_left₀ hZ_pos.ne'] at h_mul
  have h_N_le_exp : N_card ≤ Real.exp ((1 / 4 : ℝ) * β) := by
    rw [← Real.exp_log hN_pos]; apply Real.exp_le_exp.mpr; dsimp [N_card] at hβ_cross ⊢; linarith
  calc Z⁻¹ * (∑ ω : ManyBodyConfig Site, Real.exp (-β * E ω) * RCLike.re (inner ℂ (ψ ω) ((1 - Pi_safe) (ψ ω))))
    _ ≤ N_card * Real.exp (-(5 / 8 : ℝ) * β) := h_prob_le_N
    _ ≤ Real.exp ((1 / 4 : ℝ) * β) * Real.exp (-(5 / 8 : ℝ) * β) := mul_le_mul_of_nonneg_right h_N_le_exp (Real.exp_pos _).le
    _ = Real.exp (-(3 / 8 : ℝ) * β) := by rw [← Real.exp_add]; congr 1; ring

/-- **Two-level involution Gibbs failure lower bound (`twoLevel_involution_gibbsFailureProb_ge`)**:
For any self-adjoint block Hamiltonian `H_block` and midpoint reference `H_mid` commuting with
`P_safe` (`‖H_block - H_mid‖ ≤ Δ_gap / 2`) and involution `E_K` (`E_K * E_K = 1`, `‖E_K‖ ≤ 1`,
`(1 - P_safe) * E_K * P_safe = E_K * P_safe`, `Commute H_mid E_K`), every unit eigenstate `ψ`
of `H_jump = H_block - (b : ℂ) • E_K` satisfies `b ≤ (Δ_gap + 2 * b) * ‖(1 - P_safe) ψ‖`, so
`(b / (Δ_gap + 2 * b)) ^ 2 ≤ gibbsFailureProb H_jump hH_jump β (1 - P_safe)`. -/
theorem twoLevel_involution_gibbsFailureProb_ge {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)] [∀ x, Nonempty (Site x)]
    (b Δ_gap β : ℝ)
    (P_safe H_block H_mid E_K : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site)
    (hP_safe : IsStarProjection P_safe) (hH_mid : IsSelfAdjoint H_mid)
    (hH_jump : IsSelfAdjoint (H_block - ((b : ℝ) : ℂ) • E_K))
    (hb : 0 ≤ b) (hΔ_gap : 0 < Δ_gap) (h_comm_block : Commute H_block P_safe)
    (h_comm_mid_safe : Commute H_mid P_safe) (h_comm_mid_EK : Commute H_mid E_K)
    (h_norm_split : ‖H_block - H_mid‖ ≤ Δ_gap / 2)
    (hEK_inv : E_K * E_K = 1) (hEK_norm : ‖E_K‖ ≤ 1)
    (hEK_flip : (1 - P_safe) * E_K * P_safe = E_K * P_safe) :
    (b / (Δ_gap + 2 * b)) ^ 2 ≤
      gibbsFailureProb (H_block - ((b : ℝ) : ℂ) • E_K) hH_jump β (1 - P_safe) := by
  let H_jump := H_block - ((b : ℝ) : ℂ) • E_K
  let P_unsafe := 1 - P_safe
  have hP_unsafe : IsStarProjection P_unsafe := hP_safe.one_sub
  let ψ := opEigenbasis H_jump hH_jump
  let E := opEigenvalues H_jump hH_jump
  let Z := gibbsPartitionZ E β
  have hZ_pos : 0 < Z := gibbsPartitionZ_pos E β
  have h_denom_pos : 0 < Δ_gap + 2 * b := by positivity
  have h_pyth : ∀ z : ManyBodyHilbertSpace Site, ‖P_safe z‖ ^ 2 + ‖P_unsafe z‖ ^ 2 = ‖z‖ ^ 2 := by
    intro z; rw [← isStarProjection_re_inner_eq_norm_sq hP_safe z,
      ← isStarProjection_re_inner_eq_norm_sq hP_unsafe z, ← map_add, ← inner_add_right]
    have h_add : P_safe z + P_unsafe z = z := by
      dsimp [P_unsafe]; rw [ContinuousLinearMap.sub_apply, ContinuousLinearMap.one_apply, add_sub_cancel]
    rw [h_add, inner_self_eq_norm_sq]
  have h_ek_le : ∀ z : ManyBodyHilbertSpace Site, ‖E_K z‖ ≤ ‖z‖ := fun z =>
    le_trans (ContinuousLinearMap.le_opNorm E_K z) (by simpa using mul_le_mul_of_nonneg_right hEK_norm (norm_nonneg z))
  have h_eig_lower : ∀ ω : ManyBodyConfig Site,
      (b / (Δ_gap + 2 * b)) ^ 2 ≤ RCLike.re (inner ℂ (ψ ω) (P_unsafe (ψ ω))) := by
    intro ω; rw [isStarProjection_re_inner_eq_norm_sq hP_unsafe (ψ ω)]
    let u := E_K (P_safe (ψ ω)); let w := P_unsafe (ψ ω)
    have hψ_unit : ‖ψ ω‖ ^ 2 = 1 := by
      have h1 := congrArg RCLike.re (opEigenbasis_orthonormal H_jump hH_jump ω ω)
      rw [if_pos rfl, inner_self_eq_norm_sq] at h1; simpa using h1
    have hu_norm : ‖u‖ = ‖P_safe (ψ ω)‖ := by
      refine le_antisymm (h_ek_le _) ?_
      have h_inv : E_K u = P_safe (ψ ω) := by
        change (E_K * E_K) (P_safe (ψ ω)) = P_safe (ψ ω); rw [hEK_inv, ContinuousLinearMap.one_apply]
      rw [← h_inv]; exact h_ek_le u
    have huw_sq : ‖u‖ ^ 2 + ‖w‖ ^ 2 = 1 := by rw [hu_norm, ← hψ_unit]; exact h_pyth (ψ ω)
    have hu_le_one : ‖u‖ ≤ 1 := by nlinarith [sq_nonneg ‖w‖]
    have hw_le_one : ‖w‖ ≤ 1 := by nlinarith [sq_nonneg ‖u‖]
    let v₁ := P_safe (E_K w); let v₂ := P_unsafe (E_K w)
    have hv_sq : ‖v₁‖ ^ 2 + ‖v₂‖ ^ 2 ≤ ‖w‖ ^ 2 := by
      rw [h_pyth (E_K w)]; exact pow_le_pow_left₀ (norm_nonneg _) (h_ek_le w) 2
    have h_pu_u : P_unsafe u = u := by
      change ((1 - P_safe) * E_K * P_safe) (ψ ω) = (E_K * P_safe) (ψ ω); rw [hEK_flip]
    have h_ps_u : P_safe u = 0 := by
      have h_add : P_safe u + P_unsafe u = u := by
        dsimp [P_unsafe]; rw [ContinuousLinearMap.sub_apply, ContinuousLinearMap.one_apply, add_sub_cancel]
      simpa [h_pu_u] using h_add
    have hψ_split : ψ ω = P_safe (ψ ω) + w := by
      dsimp [w, P_unsafe]; rw [ContinuousLinearMap.sub_apply, ContinuousLinearMap.one_apply, add_sub_cancel]
    have h_ps_EK : P_safe (E_K (ψ ω)) = v₁ := by
      conv_lhs => rw [hψ_split, map_add, map_add]
      change P_safe u + v₁ = v₁; rw [h_ps_u, zero_add]
    have h_pu_EK : P_unsafe (E_K (ψ ω)) = u + v₂ := by
      conv_lhs => rw [hψ_split, map_add, map_add]
      change P_unsafe u + v₂ = u + v₂; rw [h_pu_u]
    let A := H_mid - ((E ω : ℝ) : ℂ) • 1; let ΔH := H_block - H_mid
    have h_comm_app : ∀ (S T : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site) (x),
        Commute S T → T (S x) = S (T x) := fun S T x h => by change (T * S) x = (S * T) x; rw [h.eq]
    have hA_comm_safe : Commute A P_safe :=
      h_comm_mid_safe.sub_left (Commute.smul_left (Commute.one_left P_safe) ((E ω : ℝ) : ℂ))
    have hA_comm_unsafe : Commute A P_unsafe := (Commute.one_right A).sub_right hA_comm_safe
    have hΔH_comm_safe : Commute ΔH P_safe := h_comm_block.sub_left h_comm_mid_safe
    have hΔH_comm_unsafe : Commute ΔH P_unsafe := (Commute.one_right ΔH).sub_right hΔH_comm_safe
    have hA_comm_EK : Commute A E_K :=
      h_comm_mid_EK.sub_left (Commute.smul_left (Commute.one_left E_K) ((E ω : ℝ) : ℂ))
    have h_eig_eq : A (ψ ω) + ΔH (ψ ω) = ((b : ℝ) : ℂ) • E_K (ψ ω) := by
      have h_ev : (H_block - ((b : ℝ) : ℂ) • E_K) (ψ ω) = ((E ω : ℝ) : ℂ) • ψ ω :=
        opEigenbasis_apply_H H_jump hH_jump ω
      rw [ContinuousLinearMap.sub_apply, ContinuousLinearMap.smul_apply] at h_ev
      change (H_mid - ((E ω : ℝ) : ℂ) • 1) (ψ ω) + (H_block - H_mid) (ψ ω) = ((b : ℝ) : ℂ) • E_K (ψ ω)
      rw [ContinuousLinearMap.sub_apply, ContinuousLinearMap.sub_apply,
        ContinuousLinearMap.smul_apply, ContinuousLinearMap.one_apply, ← h_ev]
      abel
    have hAu_eq : A u = ((b : ℝ) : ℂ) • E_K v₁ - E_K (ΔH (P_safe (ψ ω))) := by
      have h_ps := congrArg P_safe h_eig_eq; rw [map_add, map_smul, h_ps_EK] at h_ps
      rw [h_comm_app A P_safe (ψ ω) hA_comm_safe, h_comm_app ΔH P_safe (ψ ω) hΔH_comm_safe] at h_ps
      have h_ek := congrArg E_K (eq_sub_of_add_eq h_ps)
      rw [h_comm_app A E_K (P_safe (ψ ω)) hA_comm_EK, map_sub, map_smul] at h_ek; exact h_ek
    have hbu_eq : ((b : ℝ) : ℂ) • u = A w + (ΔH w - ((b : ℝ) : ℂ) • v₂) := by
      have h_pu := congrArg P_unsafe h_eig_eq; rw [map_add, map_smul, h_pu_EK, smul_add] at h_pu
      rw [h_comm_app A P_unsafe (ψ ω) hA_comm_unsafe, h_comm_app ΔH P_unsafe (ψ ω) hΔH_comm_unsafe] at h_pu
      rw [← add_sub_assoc, show A w + ΔH w = ((b : ℝ) : ℂ) • u + ((b : ℝ) : ℂ) • v₂ from h_pu, add_sub_cancel_right]
    have hAu_norm : ‖A u‖ ≤ b * ‖v₁‖ + (Δ_gap / 2) * ‖u‖ := by
      rw [hAu_eq]
      have h1 : ‖((b : ℝ) : ℂ) • E_K v₁‖ ≤ b * ‖v₁‖ := by
        rw [norm_smul, Complex.norm_real, Real.norm_of_nonneg hb]; exact mul_le_mul_of_nonneg_left (h_ek_le v₁) hb
      have h2 : ‖E_K (ΔH (P_safe (ψ ω)))‖ ≤ (Δ_gap / 2) * ‖u‖ := by
        rw [hu_norm]
        exact le_trans (h_ek_le _) (le_trans (ContinuousLinearMap.le_opNorm ΔH _)
          (mul_le_mul_of_nonneg_right h_norm_split (norm_nonneg _)))
      exact le_trans (norm_sub_le _ _) (add_le_add h1 h2)
    have h_rhs2_norm : ‖ΔH w - ((b : ℝ) : ℂ) • v₂‖ ≤ (Δ_gap / 2) * ‖w‖ + b * ‖v₂‖ := by
      have h1 : ‖ΔH w‖ ≤ (Δ_gap / 2) * ‖w‖ :=
        le_trans (ContinuousLinearMap.le_opNorm ΔH w) (mul_le_mul_of_nonneg_right h_norm_split (norm_nonneg _))
      have h2 : ‖((b : ℝ) : ℂ) • v₂‖ = b * ‖v₂‖ := by rw [norm_smul, Complex.norm_real, Real.norm_of_nonneg hb]
      exact le_trans (norm_sub_le _ _) (add_le_add h1 h2.le)
    have h_inner_A : inner ℂ u (A w) = inner ℂ (A u) w := by
      change inner ℂ u (H_mid w - ((E ω : ℝ) : ℂ) • w) = inner ℂ (H_mid u - ((E ω : ℝ) : ℂ) • u) w
      rw [inner_sub_right, inner_sub_left, inner_smul_right, inner_smul_left,
        Complex.conj_ofReal, ← ContinuousLinearMap.adjoint_inner_left,
        ContinuousLinearMap.isSelfAdjoint_iff'.mp hH_mid]
    have h_re_bu : RCLike.re (inner ℂ u (((b : ℝ) : ℂ) • u)) = b * ‖u‖ ^ 2 := by
      rw [inner_smul_right, re_ofReal_mul, inner_self_eq_norm_sq]
    have h_bu_le : b * ‖u‖ ^ 2 ≤ Δ_gap * ‖u‖ * ‖w‖ + b * (‖v₁‖ * ‖w‖ + ‖u‖ * ‖v₂‖) := by
      have h_eq := congrArg (fun z => RCLike.re (inner ℂ u z)) hbu_eq; (try dsimp only at h_eq)
      rw [h_re_bu, inner_add_right, map_add, h_inner_A] at h_eq
      have h_cs1 : RCLike.re (inner ℂ (A u) w) ≤ (b * ‖v₁‖ + (Δ_gap / 2) * ‖u‖) * ‖w‖ :=
        le_trans (le_trans (le_abs_self _) (RCLike.abs_re_le_norm _))
          (le_trans (norm_inner_le_norm _ _) (mul_le_mul_of_nonneg_right hAu_norm (norm_nonneg _)))
      have h_cs2 : RCLike.re (inner ℂ u (ΔH w - ((b : ℝ) : ℂ) • v₂)) ≤ ‖u‖ * ((Δ_gap / 2) * ‖w‖ + b * ‖v₂‖) :=
        le_trans (le_trans (le_abs_self _) (RCLike.abs_re_le_norm _))
          (le_trans (norm_inner_le_norm _ _) (mul_le_mul_of_nonneg_left h_rhs2_norm (norm_nonneg _)))
      linarith
    have h_cs_v : ‖v₁‖ * ‖w‖ + ‖u‖ * ‖v₂‖ ≤ ‖w‖ := by
      have h_sq : (‖v₁‖ * ‖w‖ + ‖u‖ * ‖v₂‖) ^ 2 ≤ ‖w‖ ^ 2 := by
        calc (‖v₁‖ * ‖w‖ + ‖u‖ * ‖v₂‖) ^ 2
          _ ≤ (‖v₁‖ * ‖w‖ + ‖u‖ * ‖v₂‖) ^ 2 + (‖v₁‖ * ‖u‖ - ‖w‖ * ‖v₂‖) ^ 2 := le_add_of_nonneg_right (sq_nonneg _)
          _ = (‖v₁‖ ^ 2 + ‖v₂‖ ^ 2) * (‖u‖ ^ 2 + ‖w‖ ^ 2) := by ring
          _ ≤ ‖w‖ ^ 2 * 1 := by rw [huw_sq]; exact mul_le_mul_of_nonneg_right hv_sq zero_le_one
          _ = ‖w‖ ^ 2 := mul_one _
      nlinarith [norm_nonneg v₁, norm_nonneg v₂, norm_nonneg u, norm_nonneg w]
    have h_b_le : b ≤ (Δ_gap + 2 * b) * ‖w‖ := by
      have h_uw_le : ‖u‖ * ‖w‖ ≤ ‖w‖ := mul_le_of_le_one_left (norm_nonneg w) hu_le_one
      have h_w2_le : ‖w‖ ^ 2 ≤ ‖w‖ := by rw [sq]; exact mul_le_of_le_one_left (norm_nonneg w) hw_le_one
      calc b = b * (‖u‖ ^ 2 + ‖w‖ ^ 2) := by rw [huw_sq, mul_one]
        _ = b * ‖u‖ ^ 2 + b * ‖w‖ ^ 2 := by ring
        _ ≤ (Δ_gap * ‖u‖ * ‖w‖ + b * (‖v₁‖ * ‖w‖ + ‖u‖ * ‖v₂‖)) + b * ‖w‖ ^ 2 := add_le_add h_bu_le le_rfl
        _ ≤ (Δ_gap * ‖w‖ + b * ‖w‖) + b * ‖w‖ :=
            add_le_add (add_le_add (by nlinarith) (mul_le_mul_of_nonneg_left h_cs_v hb))
              (mul_le_mul_of_nonneg_left h_w2_le hb)
        _ = (Δ_gap + 2 * b) * ‖w‖ := by ring
    exact pow_le_pow_left₀ (by positivity) ((div_le_iff₀ h_denom_pos).mpr (by linarith)) 2
  rw [perturbed_gibbsFailureProb_eq_inv_gibbsPartitionZ_mul_boltzmann_trace H_jump hH_jump β P_unsafe,
    hilbertTrace_gibbsBoltzmannOp_mul_eq]
  have h_sum_ge : Z * (b / (Δ_gap + 2 * b)) ^ 2 ≤
      ∑ ω : ManyBodyConfig Site, Real.exp (-β * E ω) * RCLike.re (inner ℂ (ψ ω) (P_unsafe (ψ ω))) := by
    change (∑ ω : ManyBodyConfig Site, Real.exp (-β * E ω)) * (b / (Δ_gap + 2 * b)) ^ 2 ≤ _
    rw [Finset.sum_mul]; exact Finset.sum_le_sum fun ω _ => mul_le_mul_of_nonneg_left (h_eig_lower ω) (Real.exp_pos _).le
  calc (b / (Δ_gap + 2 * b)) ^ 2
    _ = Z⁻¹ * (Z * (b / (Δ_gap + 2 * b)) ^ 2) := (inv_mul_cancel_left₀ hZ_pos.ne' _).symm
    _ ≤ Z⁻¹ * ∑ ω : ManyBodyConfig Site, Real.exp (-β * E ω) * RCLike.re (inner ℂ (ψ ω) (P_unsafe (ψ ω))) :=
        mul_le_mul_of_nonneg_left h_sum_ge (inv_nonneg.mpr hZ_pos.le)

/-- **Scale-Split Master Gibbs Bound (`scale_split_master_gibbs_bound`)** (Part II, Section 6.3 (`subsec:main-theorems`), Theorem 6.3 (`thm:main-A`), Equation `eq:main-A-master`, and Section 5.1 (`subsec:direct-worldline-synthesis`), Theorem 5.1 (`thm:direct-worldline-intact-cluster-erasure`)):
Scale-split master bound, `D_super` fifth-moment bound, and `D_fin` zero-tail bound on `gibbsFailureProb`
on `sys` under `worldlineCouplingThreshold` and `worldlineSpanningThreshold` for `β > criticalInverseTempHier Δ_0`. -/
theorem scale_split_master_gibbs_bound
    {L q_code r_0 m_max w_0 c_chk L_star R_cut Δ_adj d_min : ℕ} [NeZero L]
    (D_field : Box3D L → LocalCSSDescriptor q_code r_0 m_max) (h_valid : ValidDescriptorField D_field)
    (sys : SysCSS[L, q_code, m_max])
    (h_sys_checks : ∀ idx, sys.checkProj idx = staticCSSCheckProj D_field idx ∧
      sys.support idx = staticCSSCheckSupport D_field idx ∧ sys.weight idx = 1)
    (h_geom : sys.IsGeometricallyLocal r_0 w_0)
    (C_RCA M_5 η c_wt Δ_0 Δ_RCA C_wl c_wl β J : ℝ)
    (h_tqo1 : SatisfiesTQO1 sys L_star) (h_tqo2 : SatisfiesSectorFilteredLinearTQO2 sys 1 L_star C_RCA)
    (V : QuasiLocalPerturbation 3 L (SiteCSS[L, q_code])) (f : ℕ → ℝ)
    (hH_trunc : IsSelfAdjoint (sys.H0 + scaleSplitTruncatedOp V R_cut))
    (hH_full : IsSelfAdjoint ((sys.H0 + scaleSplitTruncatedOp V R_cut) + scaleSplitTailOp V R_cut))
    (adj : IdxCSS[L, q_code, m_max] → IdxCSS[L, q_code, m_max] → Prop) [DecidableRel adj]
    (S_safe : Finset (IdxCSS[L, q_code, m_max] → Bool))
    (W_cover : Finset (Finset (IdxCSS[L, q_code, m_max]))) (v_0 : IdxCSS[L, q_code, m_max])
    (hc_chk : 1 ≤ c_chk) (hr_0 : 1 ≤ r_0) (hC_RCA : 0 ≤ C_RCA) (hR_cut : 1 ≤ R_cut) (hR_le : R_cut ≤ L_star) (h_scale_cal : SatisfiesWorldlineScaleCalibration L L_star R_cut r_0 C_RCA)
    (h_rca_cal : rcaDiagonalCoercivityConstant 3 R_cut r_0 w_0 C_RCA ≤ Δ_RCA)
    (hC_wl_cal : (kpCollarMaxCheckCard R_cut r_0 w_0 C_RCA : ℝ) ≤ C_wl)
    (hc_wl_cal : (kpCollarMaxCheckCard R_cut r_0 w_0 C_RCA : ℝ) ≤ c_wl)
    (hf_super : InPerturbationClassSuper f) (hM5 : HasDecayMomentBound f 5 M_5) (h_summable : Summable f)
    (h_ql : HasQuasiLocalDecayBound V J f) (hc_wt : 0 < c_wt) (hΔ_0 : 0 < Δ_0) (hΔ_0_le : Δ_0 ≤ 1 / 4) (hΔ_RCA : 0 < Δ_RCA)
    (hJ_nonneg : 0 ≤ J) (hJ_walsh : J ≤ collarWalshCouplingThreshold R_cut r_0 w_0 C_RCA)
    (hJ_wl : J ≤ worldlineCouplingThreshold Δ_0 Δ_RCA)
    (hJ_span : J ≤ worldlineSpanningThreshold Δ_RCA C_wl c_wl β f R_cut)
    (h_sum_pos : 0 < worldlineNativeKPSum f C_wl c_wl β R_cut) (hβ : criticalInverseTempHier Δ_0 < β)
    (hd_min : c_wt * (((L ^ 3 : ℕ) : ℝ) ^ η) ≤ (d_min : ℝ))
    (h_conn_cover : IsConnectedCheckWitnessCover adj S_safe W_cover v_0 Δ_adj d_min)
    (hW_cover_valid : ∀ W ∈ W_cover, (fun idx => decide (idx ∈ W)) ∈ realizableSyndromes D_field) :
    V.totalPerturbation = scaleSplitTruncatedOp V R_cut + scaleSplitTailOp V R_cut ∧
    gibbsFailureProb (sys.H0 + scaleSplitTruncatedOp V R_cut)
      hH_trunc β (1 - indexedBareFailureProjector sys S_safe) ≤
      2 * Real.exp (-(c_wt * (3 / 2 : ℝ) * Δ_0 * (β - criticalInverseTempHier Δ_0)) * (((L ^ 3 : ℕ) : ℝ) ^ η)) ∧
    gibbsFailureProb ((sys.H0 + scaleSplitTruncatedOp V R_cut) + scaleSplitTailOp V R_cut)
      hH_full β (1 - indexedBareFailureProjector sys S_safe) ≤
      scaleSplitMasterUpperBound L η (c_wt * (3 / 2 : ℝ) * Δ_0) β
        (criticalInverseTempHier Δ_0) 1 J (perturbationTailSeries f R_cut) ∧
    gibbsFailureProb ((sys.H0 + scaleSplitTruncatedOp V R_cut) + scaleSplitTailOp V R_cut)
      hH_full β (1 - indexedBareFailureProjector sys S_safe) ≤
      scaleSplitMasterUpperBound L η (c_wt * (3 / 2 : ℝ) * Δ_0) β
        (criticalInverseTempHier Δ_0) 1 J ((Real.pi ^ 2 / 6) * M_5 / ((R_cut : ℝ) ^ 3)) ∧
    (∀ r_pert : ℕ, InPerturbationClassFin f r_pert → r_pert ≤ R_cut →
      gibbsFailureProb ((sys.H0 + scaleSplitTruncatedOp V R_cut) + scaleSplitTailOp V R_cut)
        hH_full β (1 - indexedBareFailureProjector sys S_safe) ≤
        2 * Real.exp (-(c_wt * (3 / 2 : ℝ) * Δ_0 * (β - criticalInverseTempHier Δ_0)) *
          (((L ^ 3 : ℕ) : ℝ) ^ η))) := by
  haveI : Nonempty (CodeSlotConfig q_code) := ⟨fun _ => false⟩
  haveI : ∀ x : Box3D L, Nonempty (SiteCSS[L, q_code] x) := fun _ => inferInstance
  have h_conn := connected_check_witness_cover_card_and_klarner_bound
    adj S_safe W_cover v_0 Δ_adj d_min h_conn_cover
  have h_wit_raw : ∀ W ∈ W_cover,
      gibbsFailureProb (sys.H0 + scaleSplitTruncatedOp V R_cut) hH_trunc β
        (positiveCheckWitnessProj sys W) ≤
        Real.exp (-β * (2 * Δ_0 - 6 * J * Δ_RCA) * (W.card : ℝ)) *
          Real.exp (64 * Real.exp 1 * max 1 β * J *
            worldlineNativeKPSum f C_wl c_wl β R_cut * (W.card : ℝ)) :=
    fun W hW => (directWorldline_truncated_css_witness_gibbsFailureProb_le
      D_field h_valid sys h_sys_checks h_geom h_tqo1 h_tqo2 V f hf_super h_ql hH_trunc
      hR_cut hR_le h_scale_cal hC_RCA h_rca_cal hC_wl_cal hc_wl_cal hΔ_0 hΔ_0_le hΔ_RCA hβ hJ_nonneg h_sum_pos hJ_walsh hJ_wl hJ_span W (hW_cover_valid W hW)).2
  exact directWorldline_scaleSplit_intact_cluster_synthesis
    sys V f c_chk r_0 R_cut d_min hH_trunc hH_full
    C_RCA M_5 η c_wt Δ_0 Δ_RCA C_wl c_wl β J S_safe W_cover
    hc_chk hr_0 hC_RCA hR_cut hM5 h_summable h_ql
    hc_wt hΔ_0 hΔ_RCA hJ_nonneg hJ_wl hJ_span h_sum_pos hβ hd_min
    h_conn_cover.1 h_wit_raw h_conn.1 h_conn.2

/-- **Low-Temperature Window Gibbs Stability (`fixed_temp_window_gibbs_stability`)** (Part II, Section 6.3 (`subsec:main-theorems`), Theorem 6.4 (`thm:main-B`), and Section 5.2 (`subsec:low-temp-crossover`), Theorem 5.3 (`thm:low-temperature-window-and-crossover`)):
For `J ≤ J_span_hier(R_cut)` and `β ∈ (β_c^hier, β_max(J; R_cut)]`, proves `J ≤ worldlineSpanningThreshold`,
`scaleSplitMasterUpperBound`, and the tail-free Peierls bound for `InPerturbationClassFin`. -/
theorem fixed_temp_window_gibbs_stability
    {L q_code r_0 m_max w_0 c_chk L_star R_cut Δ_adj d_min : ℕ} [NeZero L]
    (D_field : Box3D L → LocalCSSDescriptor q_code r_0 m_max) (h_valid : ValidDescriptorField D_field)
    (sys : SysCSS[L, q_code, m_max])
    (h_sys_checks : ∀ idx, sys.checkProj idx = staticCSSCheckProj D_field idx ∧
      sys.support idx = staticCSSCheckSupport D_field idx ∧ sys.weight idx = 1)
    (h_geom : sys.IsGeometricallyLocal r_0 w_0)
    (C_RCA M_5 η c_wt Δ_0 Δ_RCA C_wl c_wl β J : ℝ)
    (h_tqo1 : SatisfiesTQO1 sys L_star) (h_tqo2 : SatisfiesSectorFilteredLinearTQO2 sys 1 L_star C_RCA)
    (V : QuasiLocalPerturbation 3 L (SiteCSS[L, q_code])) (f : ℕ → ℝ)
    (hH_trunc : IsSelfAdjoint (sys.H0 + scaleSplitTruncatedOp V R_cut))
    (hH_full : IsSelfAdjoint ((sys.H0 + scaleSplitTruncatedOp V R_cut) + scaleSplitTailOp V R_cut))
    (adj : IdxCSS[L, q_code, m_max] → IdxCSS[L, q_code, m_max] → Prop) [DecidableRel adj]
    (S_safe : Finset (IdxCSS[L, q_code, m_max] → Bool))
    (W_cover : Finset (Finset (IdxCSS[L, q_code, m_max]))) (v_0 : IdxCSS[L, q_code, m_max])
    (hc_chk : 1 ≤ c_chk) (hr_0 : 1 ≤ r_0) (hC_RCA : 0 ≤ C_RCA) (hR_cut : 1 ≤ R_cut) (hR_le : R_cut ≤ L_star) (h_scale_cal : SatisfiesWorldlineScaleCalibration L L_star R_cut r_0 C_RCA)
    (h_rca_cal : rcaDiagonalCoercivityConstant 3 R_cut r_0 w_0 C_RCA ≤ Δ_RCA)
    (hC_wl_cal : (kpCollarMaxCheckCard R_cut r_0 w_0 C_RCA : ℝ) ≤ C_wl)
    (hc_wl_cal : (kpCollarMaxCheckCard R_cut r_0 w_0 C_RCA : ℝ) ≤ c_wl)
    (hf_super : InPerturbationClassSuper f) (hM5 : HasDecayMomentBound f 5 M_5) (h_summable : Summable f)
    (h_ql : HasQuasiLocalDecayBound V J f) (hc_wt : 0 < c_wt) (hΔ_0 : 0 < Δ_0) (hΔ_0_le : Δ_0 ≤ 1 / 4) (hΔ_RCA : 0 < Δ_RCA)
    (hC_wl : 0 ≤ C_wl) (hc_wl : 0 ≤ c_wl) (h_beta_c_ge : 1 / 2 ≤ criticalInverseTempHier Δ_0)
    (hJ_pos : 0 < J) (hJ_walsh : J ≤ collarWalshCouplingThreshold R_cut r_0 w_0 C_RCA)
    (hJ_wl : J ≤ worldlineCouplingThreshold Δ_0 Δ_RCA)
    (hJ_hier : J ≤ worldlineSpanningThreshold Δ_RCA C_wl c_wl (2 * criticalInverseTempHier Δ_0) f R_cut)
    (h_sum_pos : 0 < worldlineNativeKPSum f C_wl c_wl (2 * criticalInverseTempHier Δ_0) R_cut)
    (hβ : criticalInverseTempHier Δ_0 < β)
    (hβ_max : β ≤ lowTempWindowBetaMax (criticalInverseTempHier Δ_0) c_wl R_cut
      (worldlineSpanningThreshold Δ_RCA C_wl c_wl (2 * criticalInverseTempHier Δ_0) f R_cut) J)
    (hd_min : c_wt * (((L ^ 3 : ℕ) : ℝ) ^ η) ≤ (d_min : ℝ))
    (h_conn_cover : IsConnectedCheckWitnessCover adj S_safe W_cover v_0 Δ_adj d_min)
    (hW_cover_valid : ∀ W ∈ W_cover, (fun idx => decide (idx ∈ W)) ∈ realizableSyndromes D_field) :
    let J_span_hier := worldlineSpanningThreshold Δ_RCA C_wl c_wl (2 * criticalInverseTempHier Δ_0) f R_cut
    2 * criticalInverseTempHier Δ_0 ≤ lowTempWindowBetaMax (criticalInverseTempHier Δ_0) c_wl R_cut J_span_hier J ∧
    J ≤ worldlineSpanningThreshold Δ_RCA C_wl c_wl β f R_cut ∧
    gibbsFailureProb ((sys.H0 + scaleSplitTruncatedOp V R_cut) + scaleSplitTailOp V R_cut)
      hH_full β (1 - indexedBareFailureProjector sys S_safe) ≤
      scaleSplitMasterUpperBound L η (c_wt * (3 / 2 : ℝ) * Δ_0) β
        (criticalInverseTempHier Δ_0) 1 J (perturbationTailSeries f R_cut) ∧
    gibbsFailureProb ((sys.H0 + scaleSplitTruncatedOp V R_cut) + scaleSplitTailOp V R_cut)
      hH_full β (1 - indexedBareFailureProjector sys S_safe) ≤
      scaleSplitMasterUpperBound L η (c_wt * (3 / 2 : ℝ) * Δ_0) β
        (criticalInverseTempHier Δ_0) 1 J ((Real.pi ^ 2 / 6) * M_5 / ((R_cut : ℝ) ^ 3)) ∧
    (∀ r_pert : ℕ, InPerturbationClassFin f r_pert → r_pert ≤ R_cut →
      gibbsFailureProb ((sys.H0 + scaleSplitTruncatedOp V R_cut) + scaleSplitTailOp V R_cut)
        hH_full β (1 - indexedBareFailureProjector sys S_safe) ≤
        2 * Real.exp (-(c_wt * (3 / 2 : ℝ) * Δ_0 * (β - criticalInverseTempHier Δ_0)) *
          (((L ^ 3 : ℕ) : ℝ) ^ η))) := by
  intro J_span_hier
  obtain ⟨h_sum_β, h_win, hJ_span⟩ :=
    worldlineSpanningThreshold_ge_of_beta_le_windowMax
      f R_cut Δ_0 Δ_RCA C_wl c_wl β J hf_super.1 hC_wl hc_wl h_beta_c_ge hJ_pos hJ_hier h_sum_pos hβ_max
  have hA := scale_split_master_gibbs_bound
    D_field h_valid sys h_sys_checks h_geom C_RCA M_5 η c_wt Δ_0 Δ_RCA C_wl c_wl β J
    h_tqo1 h_tqo2 V f hH_trunc hH_full adj S_safe W_cover v_0
    hc_chk hr_0 hC_RCA hR_cut hR_le h_scale_cal h_rca_cal hC_wl_cal hc_wl_cal hf_super hM5 h_summable h_ql
    hc_wt hΔ_0 hΔ_0_le hΔ_RCA hJ_pos.le hJ_walsh hJ_wl hJ_span h_sum_β hβ hd_min h_conn_cover hW_cover_valid
  exact ⟨h_win, hJ_span, hA.2.2.1, hA.2.2.2.1, hA.2.2.2.2⟩

/-- **Low-Temperature Window and QAC-Dressed BHM Crossover (`low_temp_window_and_bhm_crossover`)** (Part II, Section 6.3 (`subsec:main-theorems`), Theorem 6.4 (`thm:main-B`), Equation `eq:main-B-dressed`, and Section 5.2 (`subsec:low-temp-crossover`), Proposition 5.2 (`prop:bhm-relative-form-bound`) and Theorem 5.3 (`thm:low-temperature-window-and-crossover`)):
BHM relative-form sandwich from `SatisfiesTQO1`/`SatisfiesSectorFilteredLinearTQO2`, QAC dressing unitary
conjugation, exact ground-space safety, and `qacDressedGibbsUpperBound` crossover. -/
theorem low_temp_window_and_bhm_crossover
    {L q_code r_0 m_max w_0 L_star R_cut Δ_adj d_min : ℕ} [NeZero L]
    (D_field : Box3D L → LocalCSSDescriptor q_code r_0 m_max) (h_valid : ValidDescriptorField D_field)
    (sys : SysCSS[L, q_code, m_max])
    (h_sys_checks : ∀ idx, sys.checkProj idx = staticCSSCheckProj D_field idx ∧
      sys.support idx = staticCSSCheckSupport D_field idx ∧ sys.weight idx = 1)
    (h_geom : sys.IsGeometricallyLocal r_0 w_0)
    (C_RCA c_wt η Δ_0 Δ_RCA C_wl c_wl c_β_hier β β_tilde_c β_cross δ_split E_0_bhm J_eff : ℝ)
    (h_tqo1 : SatisfiesTQO1 sys L_star) (h_tqo2 : SatisfiesSectorFilteredLinearTQO2 sys 1 L_star C_RCA)
    (V_eff : QuasiLocalPerturbation 3 L (SiteCSS[L, q_code])) (f : ℕ → ℝ)
    (H R_split : ℬ_CSS[L, q_code]) (U_dress : unitary (ℬ_CSS[L, q_code]))
    (adj : IdxCSS[L, q_code, m_max] → IdxCSS[L, q_code, m_max] → Prop) [DecidableRel adj]
    (S_safe : Finset (IdxCSS[L, q_code, m_max] → Bool))
    (W_cover : Finset (Finset (IdxCSS[L, q_code, m_max]))) (v_0 : IdxCSS[L, q_code, m_max])
    (hH : IsSelfAdjoint H)
    (hH_eff : IsSelfAdjoint (sys.H0 + scaleSplitTruncatedOp V_eff R_cut)) (hR_split : IsSelfAdjoint R_split)
    (hH_dressed : IsSelfAdjoint ((sys.H0 + scaleSplitTruncatedOp V_eff R_cut) + R_split))
    (h_dress_conj : H = U_dress.1 * ((sys.H0 + scaleSplitTruncatedOp V_eff R_cut) + R_split) * U_dress.1†)
    (hR_cut : 1 ≤ R_cut) (hR_le : R_cut ≤ L_star) (h_scale_cal : SatisfiesWorldlineScaleCalibration L L_star R_cut r_0 C_RCA) (hC_RCA : 0 ≤ C_RCA)
    (hf_super : InPerturbationClassSuper f) (h_ql : HasQuasiLocalDecayBound V_eff J_eff f)
    (h_rca_cal : rcaDiagonalCoercivityConstant 3 R_cut r_0 w_0 C_RCA ≤ Δ_RCA)
    (hC_wl_cal : (kpCollarMaxCheckCard R_cut r_0 w_0 C_RCA : ℝ) ≤ C_wl)
    (hc_wl_cal : (kpCollarMaxCheckCard R_cut r_0 w_0 C_RCA : ℝ) ≤ c_wl)
    (hc_wt : 0 < c_wt) (hΔ_0 : 0 < Δ_0) (hΔ_0_le : Δ_0 ≤ 1 / 4) (hΔ_RCA : 0 < Δ_RCA) (hJ_eff : 0 ≤ J_eff)
    (hJ_walsh : J_eff ≤ collarWalshCouplingThreshold R_cut r_0 w_0 C_RCA)
    (hJ_wl : J_eff ≤ worldlineCouplingThreshold Δ_0 Δ_RCA)
    (hJ_span : J_eff ≤ worldlineSpanningThreshold Δ_RCA C_wl c_wl β f R_cut)
    (h_sum_pos : 0 < worldlineNativeKPSum f C_wl c_wl β R_cut)
    (hδ_split : 0 ≤ δ_split) (hδ_small : 2 * δ_split ≤ 1 / 8) (h_split_norm : ‖R_split‖ ≤ δ_split)
    (hβ_tilde : criticalInverseTempHier Δ_0 ≤ β_tilde_c) (hβ : β_tilde_c < β) (hβ_cross_gt : criticalInverseTempHier Δ_0 < β_cross)
    (hc_β_le : (3 / 4 : ℝ) * c_β_hier ≤ c_wt * (3 / 2 : ℝ) * Δ_0)
    (hd_min : c_wt * (((L ^ 3 : ℕ) : ℝ) ^ η) ≤ (d_min : ℝ))
    (h_conn_cover : IsConnectedCheckWitnessCover adj S_safe W_cover v_0 Δ_adj d_min)
    (hW_cover_valid : ∀ W ∈ W_cover, (fun idx => decide (idx ∈ W)) ∈ realizableSyndromes D_field)
    (hP0_ne : sys.P0 ≠ 0) (hP0_safe : sys.P0 * indexedBareFailureProjector sys S_safe = sys.P0)
    (h_comm_eff_P0 : Commute (sys.H0 + scaleSplitTruncatedOp V_eff R_cut) sys.P0)
    (h_comm_split_P0 : Commute R_split sys.P0) (h_split_vac : R_split * sys.P0 = 0)
    (h_eff_vac : (sys.H0 + scaleSplitTruncatedOp V_eff R_cut - ((E_0_bhm : ℝ) : ℂ) • 1) * sys.P0 = 0)
    (h_eff_gap : ∀ ψ : ℋ_CSS[L, q_code],
      (3 / 4 : ℝ) * ‖(1 - sys.P0) ψ‖ ^ 2 ≤
        RCLike.re (inner ℂ ((1 - sys.P0) ψ)
          ((sys.H0 + scaleSplitTruncatedOp V_eff R_cut - ((E_0_bhm : ℝ) : ℂ) • 1) ((1 - sys.P0) ψ))))
    (hβ_cross : 4 * Real.log (Fintype.card (ManyBodyConfig (SiteCSS[L, q_code])) : ℝ) ≤ β_cross) :
    let Pi_safe := indexedBareFailureProjector sys S_safe
    let Pi_safe_dress := U_dress.1 * Pi_safe * U_dress.1†
    let P0_dress := U_dress.1 * sys.P0 * U_dress.1†
    (∃ E_vac : ℝ,
      let H_diag := sys.H0 + pauliDiagonalPart sys V_eff R_cut - ((E_vac : ℝ) : ℂ) • 1
      ∀ σ (ψ : ℋ_CSS[L, q_code]),
        (3 / 4 : ℝ) * sys.syndromeEnergy σ * ‖sys.syndromeProjector σ ψ‖ ^ 2 ≤
          RCLike.re (inner ℂ (sys.syndromeProjector σ ψ) (H_diag (sys.syndromeProjector σ ψ))) ∧
        RCLike.re (inner ℂ (sys.syndromeProjector σ ψ) (H_diag (sys.syndromeProjector σ ψ))) ≤
          (5 / 4 : ℝ) * sys.syndromeEnergy σ * ‖sys.syndromeProjector σ ψ‖ ^ 2) ∧
    (1 - Pi_safe) * sys.P0 = 0 ∧ (1 - Pi_safe_dress) * P0_dress = 0 ∧
    gibbsFailureProb (sys.H0 + scaleSplitTruncatedOp V_eff R_cut) hH_eff β (1 - Pi_safe) ≤
      2 * Real.exp (-(3 / 4 : ℝ) * c_β_hier * (β - β_tilde_c) * (((L ^ 3 : ℕ) : ℝ) ^ η)) ∧
    gibbsFailureProb H hH β (1 - Pi_safe_dress) =
      gibbsFailureProb ((sys.H0 + scaleSplitTruncatedOp V_eff R_cut) + R_split) hH_dressed β (1 - Pi_safe) ∧
    gibbsFailureProb H hH β (1 - Pi_safe_dress) ≤
      2 * Real.exp (2 * β * δ_split) *
        Real.exp (-(3 / 4 : ℝ) * c_β_hier * (β - β_tilde_c) * (((L ^ 3 : ℕ) : ℝ) ^ η)) +
        (Real.exp (2 * β * δ_split) - 1) ∧
    gibbsFailureProb H hH β (1 - Pi_safe_dress) ≤
      qacDressedGibbsUpperBound L η c_β_hier β β_tilde_c β_cross δ_split := by
  intro Pi_safe Pi_safe_dress P0_dress
  haveI : Nonempty (CodeSlotConfig q_code) := ⟨fun _ => false⟩
  haveI : ∀ x : Box3D L, Nonempty (SiteCSS[L, q_code] x) := fun _ => inferInstance
  have hβ_gt_crit : criticalInverseTempHier Δ_0 < β := lt_of_le_of_lt hβ_tilde hβ
  have h_24_le : 24 ≤ criticalInverseTempHier Δ_0 :=
    twenty_four_le_criticalInverseTempHier hΔ_0 hΔ_0_le
  have hβ_pos : 0 < β := by linarith
  let V_trunc := scaleSplitTruncatedPerturbation V_eff R_cut
  have hV_range : HasFiniteRangeBound V_trunc R_cut J_eff :=
    scaleSplitTruncatedPerturbation_hasFiniteRangeBound V_eff R_cut J_eff f hJ_eff hf_super h_ql
  have h_diag_eq : pauliDiagonalPart sys V_trunc R_cut = pauliDiagonalPart sys V_eff R_cut :=
    scaleSplitTruncatedPerturbation_pauliDiagonalPart sys V_eff R_cut
  obtain ⟨E_vac, h_coerc⟩ := hasSyndromeDiagonalCoercivity_of_tqo_and_finiteRange
    D_field h_valid sys h_sys_checks h_geom hR_cut hR_le hC_RCA hJ_eff h_tqo1 h_tqo2 V_trunc hV_range
  have h_quarter : 2 * rcaDiagonalCoercivityConstant 3 R_cut r_0 w_0 C_RCA * J_eff ≤ 1 / 4 := by
    have h1 : 2 * rcaDiagonalCoercivityConstant 3 R_cut r_0 w_0 C_RCA * J_eff ≤ 2 * Δ_RCA * J_eff := by nlinarith
    have h2 : 16 * Δ_RCA * J_eff ≤ Δ_0 := by
      have h_pos : 0 < 16 * Δ_RCA := by positivity
      have := (le_div_iff₀ h_pos).mp hJ_wl; linarith
    linarith
  rcases rca1_diagonal_syndrome_coercivity_sandwich sys h_coerc h_quarter with ⟨_, _, h_sandwich_trunc⟩
  have h_sandwich : ∃ E_vac : ℝ,
      let H_diag := sys.H0 + pauliDiagonalPart sys V_eff R_cut - ((E_vac : ℝ) : ℂ) • 1
      ∀ σ (ψ : ℋ_CSS[L, q_code]),
        (3 / 4 : ℝ) * sys.syndromeEnergy σ * ‖sys.syndromeProjector σ ψ‖ ^ 2 ≤
          RCLike.re (inner ℂ (sys.syndromeProjector σ ψ) (H_diag (sys.syndromeProjector σ ψ))) ∧
        RCLike.re (inner ℂ (sys.syndromeProjector σ ψ) (H_diag (sys.syndromeProjector σ ψ))) ≤
          (5 / 4 : ℝ) * sys.syndromeEnergy σ * ‖sys.syndromeProjector σ ψ‖ ^ 2 :=
    ⟨E_vac, by simpa only [h_diag_eq] using h_sandwich_trunc⟩
  obtain ⟨h_unsafe_p0, h_dress_p0, h_deep⟩ :=
    bhm_dressed_ground_excited_gibbs_bound sys
      (sys.H0 + scaleSplitTruncatedOp V_eff R_cut) R_split U_dress S_safe
      β β_cross δ_split E_0_bhm hH_dressed hβ_pos.le hδ_small h_split_norm
      hP0_ne hP0_safe h_comm_eff_P0 h_comm_split_P0 h_split_vac h_eff_vac h_eff_gap hβ_cross
  have h_conj_eq :
      gibbsFailureProb H hH β (1 - Pi_safe_dress) =
        gibbsFailureProb ((sys.H0 + scaleSplitTruncatedOp V_eff R_cut) + R_split) hH_dressed β (1 - Pi_safe) :=
    gibbsFailureProb_unitary_conj_eq H ((sys.H0 + scaleSplitTruncatedOp V_eff R_cut) + R_split)
      Pi_safe U_dress hH hH_dressed β h_dress_conj
  have h_conn := connected_check_witness_cover_card_and_klarner_bound
    adj S_safe W_cover v_0 Δ_adj d_min h_conn_cover
  have h_wit_raw : ∀ W ∈ W_cover,
      gibbsFailureProb (sys.H0 + scaleSplitTruncatedOp V_eff R_cut) hH_eff β
        (positiveCheckWitnessProj sys W) ≤
        Real.exp (-β * (2 * Δ_0 - 6 * J_eff * Δ_RCA) * (W.card : ℝ)) *
          Real.exp (64 * Real.exp 1 * max 1 β * J_eff *
            worldlineNativeKPSum f C_wl c_wl β R_cut * (W.card : ℝ)) :=
    fun W hW => (directWorldline_truncated_css_witness_gibbsFailureProb_le
      D_field h_valid sys h_sys_checks h_geom h_tqo1 h_tqo2 V_eff f hf_super h_ql hH_eff
      hR_cut hR_le h_scale_cal hC_RCA h_rca_cal hC_wl_cal hc_wl_cal hΔ_0 hΔ_0_le hΔ_RCA hβ_gt_crit hJ_eff h_sum_pos hJ_walsh hJ_wl hJ_span W (hW_cover_valid W hW)).2
  have h_trunc_hier := (directWorldline_truncated_gibbsFailureProb_le
    sys (sys.H0 + scaleSplitTruncatedOp V_eff R_cut) hH_eff f R_cut d_min
    η c_wt Δ_0 Δ_RCA C_wl c_wl β J_eff S_safe W_cover
    hc_wt hΔ_0 hΔ_RCA hJ_eff hJ_wl hJ_span h_sum_pos hβ_gt_crit hd_min
    h_conn_cover.1 h_wit_raw h_conn.1 h_conn.2).2
  have h_rate_cmp :
      (3 / 4 : ℝ) * c_β_hier * (β - β_tilde_c) ≤
        c_wt * (3 / 2 : ℝ) * Δ_0 * (β - criticalInverseTempHier Δ_0) := by
    have h_sub_pos : 0 ≤ β - β_tilde_c := (sub_pos.mpr hβ).le
    have h1 : (3 / 4 : ℝ) * c_β_hier * (β - β_tilde_c) ≤
        (c_wt * (3 / 2 : ℝ) * Δ_0) * (β - β_tilde_c) :=
      mul_le_mul_of_nonneg_right hc_β_le h_sub_pos
    have h2 : (c_wt * (3 / 2 : ℝ) * Δ_0) * (β - β_tilde_c) ≤
        (c_wt * (3 / 2 : ℝ) * Δ_0) * (β - criticalInverseTempHier Δ_0) :=
      mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    exact le_trans h1 h2
  have h_eff_bound :
      gibbsFailureProb (sys.H0 + scaleSplitTruncatedOp V_eff R_cut) hH_eff β (1 - Pi_safe) ≤
        2 * Real.exp (-(3 / 4 : ℝ) * c_β_hier * (β - β_tilde_c) * (((L ^ 3 : ℕ) : ℝ) ^ η)) := by
    refine le_trans h_trunc_hier (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (by norm_num))
    have h_vol_nn : (0 : ℝ) ≤ (((L ^ 3 : ℕ) : ℝ) ^ η) := by positivity
    have h_mul := mul_le_mul_of_nonneg_right h_rate_cmp h_vol_nn
    linarith
  have hPi_unsafe : IsStarProjection (1 - Pi_safe) :=
    (indexedBareFailureProjector_props sys S_safe).1.one_sub
  have h_weyl := (duhamelWeyl_relative_partition_ratio_bound β
    (sys.H0 + scaleSplitTruncatedOp V_eff R_cut) R_split (1 - Pi_safe)
    hβ_pos.le hH_eff hR_split hH_dressed hPi_unsafe).2
  have h_exp_split : Real.exp (2 * β * ‖R_split‖) ≤ Real.exp (2 * β * δ_split) :=
    Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left h_split_norm (by positivity))
  have h_dressed_weyl :
      gibbsFailureProb H hH β (1 - Pi_safe_dress) ≤
        2 * Real.exp (2 * β * δ_split) *
          Real.exp (-(3 / 4 : ℝ) * c_β_hier * (β - β_tilde_c) * (((L ^ 3 : ℕ) : ℝ) ^ η)) +
          (Real.exp (2 * β * δ_split) - 1) := by
    rw [h_conj_eq]
    calc gibbsFailureProb ((sys.H0 + scaleSplitTruncatedOp V_eff R_cut) + R_split) hH_dressed β (1 - Pi_safe)
      _ ≤ Real.exp (2 * β * ‖R_split‖) *
            gibbsFailureProb (sys.H0 + scaleSplitTruncatedOp V_eff R_cut) hH_eff β (1 - Pi_safe) +
            (Real.exp (2 * β * ‖R_split‖) - 1) := h_weyl
      _ ≤ Real.exp (2 * β * δ_split) *
            (2 * Real.exp (-(3 / 4 : ℝ) * c_β_hier * (β - β_tilde_c) * (((L ^ 3 : ℕ) : ℝ) ^ η))) +
            (Real.exp (2 * β * δ_split) - 1) := by
          have h_m1 := mul_le_mul_of_nonneg_left h_eff_bound (Real.exp_pos (2 * β * ‖R_split‖)).le
          have h_m2 := mul_le_mul_of_nonneg_right h_exp_split
            (by positivity : 0 ≤ 2 * Real.exp (-(3 / 4 : ℝ) * c_β_hier * (β - β_tilde_c) * (((L ^ 3 : ℕ) : ℝ) ^ η)))
          linarith
      _ = 2 * Real.exp (2 * β * δ_split) *
            Real.exp (-(3 / 4 : ℝ) * c_β_hier * (β - β_tilde_c) * (((L ^ 3 : ℕ) : ℝ) ^ η)) +
            (Real.exp (2 * β * δ_split) - 1) := by ring
  have h_qac_upper :
      gibbsFailureProb H hH β (1 - Pi_safe_dress) ≤
        qacDressedGibbsUpperBound L η c_β_hier β β_tilde_c β_cross δ_split := by
    unfold qacDressedGibbsUpperBound; (try dsimp only)
    split_ifs with h_le
    · exact h_dressed_weyl
    · rw [h_conj_eq]; exact h_deep (lt_of_not_ge h_le)
  exact ⟨h_sandwich, h_unsafe_p0, h_dress_p0, h_eff_bound, h_conj_eq, h_dressed_weyl, h_qac_upper⟩

/-- Fixed-temperature window coupling threshold `directWorldlineThreshold` for any ceiling `β_max` (Part II, Section 6.3 (`subsec:main-theorems`), Theorem 6.3 (`thm:main-A`), and Section 5.1 (`subsec:direct-worldline-synthesis`), Theorem 5.1 (`thm:direct-worldline-intact-cluster-erasure`), Equation `eq:J-span-full-def`). -/
def directWorldlineThreshold (R_pert r_0 w_0 : ℕ) (C_rca β_c β_max : ℝ) : ℝ :=
  let Δ_RCA := rcaDiagonalCoercivityConstant 3 R_pert r_0 w_0 C_rca + 1
  let C_wl := ((kpCollarMaxCheckCard R_pert r_0 w_0 C_rca + 1 : ℕ) : ℝ)
  min (collarWalshCouplingThreshold R_pert r_0 w_0 C_rca)
    (min (worldlineCouplingThreshold (1 / 4) Δ_RCA)
      (worldlineSpanningThreshold Δ_RCA C_wl C_wl (max (2 * |β_c| + 1) β_max)
        (fun r => if r ≤ R_pert then (1 : ℝ) else 0) R_pert))

private lemma worldlineNativeKPSum_fin_pos (R_pert : ℕ) (C_wl β : ℝ)
    (hR_pos : 1 ≤ R_pert) (hC_wl_pos : 0 < C_wl) :
    0 < worldlineNativeKPSum (fun r => if r ≤ R_pert then (1 : ℝ) else 0) C_wl C_wl β R_pert := by
  unfold worldlineNativeKPSum
  let term (r : ℕ) : ℝ := C_wl * ((r : ℝ) ^ 6) * (if r ≤ R_pert then (1 : ℝ) else 0) *
    Real.exp (C_wl * (1 + β) * ((r : ℝ) ^ 3))
  have h1_mem : 1 ∈ Finset.Icc 1 R_pert := Finset.mem_Icc.mpr ⟨le_rfl, hR_pos⟩
  have h_term1_pos : 0 < term 1 := by dsimp [term]; rw [if_pos hR_pos]; positivity
  refine lt_of_lt_of_le h_term1_pos (Finset.single_le_sum (f := term) (fun r _ => ?_) h1_mem)
  dsimp [term]; split_ifs <;> positivity

theorem directWorldlineThreshold_pos (R_pert r_0 w_0 : ℕ) (C_rca β_c β_max : ℝ)
    (hR_pos : 1 ≤ R_pert) (_hC_rca : 0 ≤ C_rca) (_hβc_ge : 16 ≤ β_c) :
    0 < directWorldlineThreshold R_pert r_0 w_0 C_rca β_c β_max := by
  unfold directWorldlineThreshold
  have h_walsh_pos : 0 < collarWalshCouplingThreshold R_pert r_0 w_0 C_rca :=
    collarWalshCouplingThreshold_pos R_pert r_0 w_0 C_rca
  have h_rca_nn : 0 ≤ rcaDiagonalCoercivityConstant 3 R_pert r_0 w_0 C_rca := by
    unfold rcaDiagonalCoercivityConstant; positivity
  have hΔ_RCA_pos : 0 < rcaDiagonalCoercivityConstant 3 R_pert r_0 w_0 C_rca + 1 := by linarith
  have hC_wl_pos : (0 : ℝ) < ((kpCollarMaxCheckCard R_pert r_0 w_0 C_rca + 1 : ℕ) : ℝ) := by
    exact_mod_cast Nat.succ_pos _
  have h_wl_pos : 0 < worldlineCouplingThreshold (1 / 4)
      (rcaDiagonalCoercivityConstant 3 R_pert r_0 w_0 C_rca + 1) := by
    unfold worldlineCouplingThreshold; positivity
  have h_sum_pos := worldlineNativeKPSum_fin_pos R_pert
    ((kpCollarMaxCheckCard R_pert r_0 w_0 C_rca + 1 : ℕ) : ℝ) (max (2 * |β_c| + 1) β_max) hR_pos hC_wl_pos
  have h_max_pos : 0 < max (1 : ℝ) (max (2 * |β_c| + 1) β_max) := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  have h_span_pos : 0 < worldlineSpanningThreshold
      (rcaDiagonalCoercivityConstant 3 R_pert r_0 w_0 C_rca + 1)
      ((kpCollarMaxCheckCard R_pert r_0 w_0 C_rca + 1 : ℕ) : ℝ)
      ((kpCollarMaxCheckCard R_pert r_0 w_0 C_rca + 1 : ℕ) : ℝ)
      (max (2 * |β_c| + 1) β_max) (fun r => if r ≤ R_pert then (1 : ℝ) else 0) R_pert := by
    unfold worldlineSpanningThreshold
    exact lt_min (by positivity) (by positivity)
  exact lt_min h_walsh_pos (lt_min h_wl_pos h_span_pos)

/-- **Fixed-Temperature Window Witness Bound via Direct Worldline and Intact-Cluster Expansion (`exists_directWorldline_fixed_temp_witness_bound`)**
(Part II, Section 6.3 (`subsec:main-theorems`), Theorem 6.4 (`thm:main-B`), and Section 5.2 (`subsec:low-temp-crossover`), Theorem 5.3 (`thm:low-temperature-window-and-crossover`)):
Under any fixed-temperature window `β_c < β ≤ β_max` with `16 ≤ β_c` and coupling threshold
`J ≤ directWorldlineThreshold R_pert r_0 w_0 C_rca β_c β_max`, every positive check witness `W` in a static
3D CSS system satisfying `TQO1` and sector-filtered linear `TQO2` obeys
`gibbsFailureProb (sys.H0 + V.V_tot) hH β (positiveCheckWitnessProj sys W) ≤ Real.exp (-((β_c / 2 + min (β - β_c) 1) * (W.card : ℝ)))`. -/
theorem exists_directWorldline_fixed_temp_witness_bound
    {L q_code r_0 m_max w_0 L_star R_pert : ℕ} [NeZero L]
    (D_field : Box3D L → LocalCSSDescriptor q_code r_0 m_max) (h_valid : ValidDescriptorField D_field)
    (sys : SysCSS[L, q_code, m_max])
    (h_sys_checks : ∀ idx : IdxCSS[L, q_code, m_max],
      sys.checkProj idx = staticCSSCheckProj D_field idx ∧
      sys.support idx = staticCSSCheckSupport D_field idx ∧ sys.weight idx = 1)
    (h_geom : sys.IsGeometricallyLocal r_0 w_0)
    {C_rca β_c β_max J β : ℝ} (hR_pos : 1 ≤ R_pert) (hR_le : R_pert ≤ L_star) (h_scale_cal : SatisfiesWorldlineScaleCalibration L L_star R_pert r_0 C_rca) (hC_rca : 0 ≤ C_rca)
    (hβc_ge : 16 ≤ β_c) (hβ : β > β_c) (hβ_upper : β ≤ β_max) (hJ_nn : 0 ≤ J)
    (hJ_le : J ≤ directWorldlineThreshold R_pert r_0 w_0 C_rca β_c β_max)
    (h_tqo1 : SatisfiesTQO1 sys L_star)
    (h_tqo2 : SatisfiesSectorFilteredLinearTQO2 sys 1 L_star C_rca)
    (V : QuasiLocalPerturbation 3 L (SiteCSS[L, q_code]))
    (hV_range : HasFiniteRangeBound V R_pert J)
    (hH : IsSelfAdjoint (sys.H0 + V.totalPerturbation))
    (W : Finset (IdxCSS[L, q_code, m_max]))
    (hW_valid : (fun idx => decide (idx ∈ W)) ∈ realizableSyndromes D_field) :
    gibbsFailureProb (sys.H0 + V.totalPerturbation) hH β (positiveCheckWitnessProj sys W) ≤
      Real.exp (-((β_c / 2 + min (β - β_c) 1) * (W.card : ℝ))) := by
  let Δ_RCA := rcaDiagonalCoercivityConstant 3 R_pert r_0 w_0 C_rca + 1
  let C_wl := ((kpCollarMaxCheckCard R_pert r_0 w_0 C_rca + 1 : ℕ) : ℝ)
  let f_fin : ℕ → ℝ := fun r => if r ≤ R_pert then 1 else 0
  have h_rca_nn : 0 ≤ rcaDiagonalCoercivityConstant 3 R_pert r_0 w_0 C_rca := by
    unfold rcaDiagonalCoercivityConstant; positivity
  have hΔ_RCA_pos : 0 < Δ_RCA := by dsimp [Δ_RCA]; linarith
  have hC_wl_pos : 0 < C_wl := by dsimp [C_wl]; exact_mod_cast Nat.succ_pos _
  have h_rca_cal : rcaDiagonalCoercivityConstant 3 R_pert r_0 w_0 C_rca ≤ Δ_RCA := by
    dsimp [Δ_RCA]; linarith
  have hC_wl_cal : (kpCollarMaxCheckCard R_pert r_0 w_0 C_rca : ℝ) ≤ C_wl := by
    dsimp [C_wl]; push_cast; linarith
  have hf_nn : ∀ r, 0 ≤ f_fin r := fun r => by dsimp [f_fin]; split_ifs <;> norm_num
  have hf_le_one : ∀ r, f_fin r ≤ 1 := fun r => by dsimp [f_fin]; split_ifs <;> norm_num
  have hV_norm : ∀ r ∈ Finset.Icc 1 (min R_pert L), ∀ A ∈ boxCubes 3 L r, ‖V.term r A‖ ≤ J * f_fin r := by
    intro r hr A hA
    have hr_R : r ≤ R_pert := le_trans (Finset.mem_Icc.mp hr).2 (Nat.min_le_left R_pert L)
    have hr_L : r ∈ Finset.Icc 1 L := Finset.mem_Icc.mpr
      ⟨(Finset.mem_Icc.mp hr).1, le_trans (Finset.mem_Icc.mp hr).2 (Nat.min_le_right R_pert L)⟩
    have hf_r : f_fin r = 1 := if_pos hr_R
    rw [hf_r, mul_one]; exact (hV_range r hr_L A hA).1 hr_R
  have hV_tot_eq : V.totalPerturbation = scaleSplitTruncatedOp V R_pert :=
    totalPerturbation_eq_sum_Icc_min_of_hasFiniteRangeBound hV_range
  have hH_trunc : IsSelfAdjoint (sys.H0 + scaleSplitTruncatedOp V R_pert) := hV_tot_eq ▸ hH
  have hβ_gt_16 : 16 < β := lt_of_le_of_lt hβc_ge hβ
  have h_sum_pos : 0 < worldlineNativeKPSum f_fin C_wl C_wl β R_pert :=
    worldlineNativeKPSum_fin_pos R_pert C_wl β hR_pos hC_wl_pos
  have hJ_walsh : J ≤ collarWalshCouplingThreshold R_pert r_0 w_0 C_rca :=
    le_trans hJ_le (min_le_left _ _)
  have hJ_wl : J ≤ worldlineCouplingThreshold (1 / 4) Δ_RCA :=
    le_trans hJ_le (le_trans (min_le_right _ _) (min_le_left _ _))
  have hJ_span₀ : J ≤ worldlineSpanningThreshold Δ_RCA C_wl C_wl (max (2 * |β_c| + 1) β_max) f_fin R_pert :=
    le_trans hJ_le (le_trans (min_le_right _ _) (min_le_right _ _))
  have hβ_le_abs : β ≤ max (2 * |β_c| + 1) β_max := le_trans hβ_upper (le_max_right _ _)
  have h_thresh : J ≤ worldlineSpanningThreshold Δ_RCA C_wl C_wl β f_fin R_pert := by
    refine le_trans hJ_span₀ ?_
    unfold worldlineSpanningThreshold
    refine min_le_min le_rfl ?_
    have h_sum₀_pos := worldlineNativeKPSum_fin_pos R_pert C_wl (max (2 * |β_c| + 1) β_max) hR_pos hC_wl_pos
    have h_max_β_pos : 0 < max 1 β := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
    have h_max_le : max 1 β ≤ max 1 (max (2 * |β_c| + 1) β_max) := max_le_max le_rfl hβ_le_abs
    have h_sum_le : worldlineNativeKPSum f_fin C_wl C_wl β R_pert ≤
        worldlineNativeKPSum f_fin C_wl C_wl (max (2 * |β_c| + 1) β_max) R_pert := by
      unfold worldlineNativeKPSum
      refine Finset.sum_le_sum fun r _ => ?_
      refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_)
        (mul_nonneg (mul_nonneg hC_wl_pos.le (by positivity)) (hf_nn r))
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (by linarith) hC_wl_pos.le) (by positivity)
    exact one_div_le_one_div_of_le (by positivity)
      (mul_le_mul (mul_le_mul_of_nonneg_left h_max_le (by positivity)) h_sum_le h_sum_pos.le (by positivity))
  have h_core := directWorldline_truncated_css_witness_core_bound
    D_field h_valid sys h_sys_checks h_geom h_tqo1 h_tqo2 V f_fin hf_nn hf_le_one hV_norm hH_trunc
    hR_pos hR_le h_scale_cal hC_rca h_rca_cal hC_wl_cal hC_wl_cal hΔ_RCA_pos hβ_gt_16 hJ_nn
    h_sum_pos hJ_walsh hJ_wl h_thresh W hW_valid
  have h_eq_prob :
      gibbsFailureProb (sys.H0 + V.totalPerturbation) hH β (positiveCheckWitnessProj sys W) =
        gibbsFailureProb (sys.H0 + scaleSplitTruncatedOp V R_pert) hH_trunc β (positiveCheckWitnessProj sys W) := by
    congr 1; rw [hV_tot_eq]
  rw [h_eq_prob]
  refine le_trans h_core (Real.exp_le_exp.mpr ?_)
  have h_rate := (three_quarters_beta_ge_target_witness_rate hβc_ge hβ W.card).1
  have hW_nn : (0 : ℝ) ≤ (W.card : ℝ) := Nat.cast_nonneg W.card
  have h_mul := mul_le_mul_of_nonneg_right
    (by linarith : β_c / 2 + min (β - β_c) 1 ≤ (3 / 4 : ℝ) * β - 1) hW_nn
  linarith

end DirectWorldlineCluster

end
