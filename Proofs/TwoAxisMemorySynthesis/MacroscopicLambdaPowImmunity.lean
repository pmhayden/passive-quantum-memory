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

import Proofs.TwoAxisMemorySynthesis.WeldedLatticeRealization

open scoped Classical InnerProduct ComplexConjugate BigOperators
open Filter Topology Asymptotics ContinuousLinearMap PerturbedThermalBarrier
open WeldedHierarchy WeldedHierarchy.BDLDecoder

noncomputable section

set_option maxRecDepth 2000000
set_option maxHeartbeats 800000

/-!
# Macroscopic Lambda-Power Ball Parity Witnesses and Cube Safe-Subspace Immunity

Establishes ball parity witness families at Euclidean radius `2 * (37 * bdlLambda ^ k)` for the level-k welded CSS code and its dual, and proves exact vanishing of safe-subspace commutators `[A_op, O_dec]` on `Pi_safe` for all operators supported on lattice cubes up to side `37 * bdlLambda ^ k`.

## References

* Part I, Section 5.2 (`subsec:cluster-decoder`), Definition 5.2 (`def:multiscale-cluster-decoder`), Proposition 5.3 (`prop:cluster-decoder-witness`)
* Part I, Section 5.3 (`subsec:walsh-fourier-peierls`), Lemma 5.4 (`lem:percolating-cluster-bounds`)
* Part I, Section 5.4 (`subsec:safe-decoded-observables`), Proposition 5.7 (`prop:safe-subspace-immunity`)
-/

/-! ## 1. Unconditional Macroscopic Radius-`37 * bdlLambda ^ k` Ball Witness & Cube Safe-Subspace Immunity -/

/-- **Macroscopic Radius-$74\Lambda_{\mathrm{BDL}}^k$ Ball Parity Witness Theorem
    (`hasBallParityWitnessFamily_bdlWelded_lambdaPow`)**:
    At every level `k : ℕ`, both `bdlWeldedCode k` and `dualCode (bdlWeldedCode k)` admit a
    `HasBallParityWitnessFamily` at Euclidean radius `2 * ((37 * bdlLambda ^ k : ℕ) : ℝ)`. -/
theorem hasBallParityWitnessFamily_bdlWelded_lambdaPow (k : ℕ) :
    HasBallParityWitnessFamily (bdlWeldedCode k) (bdlWeldedLZ k) (bdlWeldedLX k)
      (2 * ((37 * bdlLambda ^ k : ℕ) : ℝ)) (clusterRawWeight k)
      ((bdlClusterStepBase ^ 8) ^ (clusterRawWeight k)) ∧
    HasBallParityWitnessFamily (dualCode (bdlWeldedCode k)) (bdlWeldedLX k) (bdlWeldedLZ k)
      (2 * ((37 * bdlLambda ^ k : ℕ) : ℝ)) (clusterRawWeight k)
      ((bdlClusterStepBase ^ 8) ^ (clusterRawWeight k)) := by
  have hr0 : (0 : ℝ) ≤ 2 * ((37 * bdlLambda ^ k : ℕ) : ℝ) := by positivity
  have h_sd : scaleDownRadius (2 * k) (2 * ((37 * bdlLambda ^ k : ℕ) : ℝ)) ≤ 7015 := by
    rcases k with _ | k'
    · simp only [pow_zero, mul_one, Nat.cast_ofNat, scaleDownRadius]; norm_num
    · have hlam : (10000 : ℝ) ≤ (bdlLambda : ℝ) := bdlLambda_ge_10000
      have h74 : (74 : ℝ) ≤ (bdlLambda : ℝ) ^ (k' + 1) := by
        rw [pow_succ]; nlinarith [one_le_pow₀ (by linarith : (1 : ℝ) ≤ (bdlLambda : ℝ)) (n := k')]
      have h_div : (2 * ((37 * bdlLambda ^ (k' + 1) : ℕ) : ℝ)) / ((bdlLambda : ℝ) ^ (2 * (k' + 1))) ≤ 1 := by
        rw [div_le_iff₀ (by positivity), Nat.cast_mul, Nat.cast_ofNat, Nat.cast_pow,
          two_mul (k' + 1), pow_add (bdlLambda : ℝ) (k' + 1) (k' + 1)]
        nlinarith [(by positivity : (0 : ℝ) ≤ (bdlLambda : ℝ) ^ (k' + 1))]
      linarith [scaleDownRadius_bound (2 * (k' + 1)) hr0]
  obtain ⟨hP, hD⟩ := hasBallParityWitnessFamily_bdlIterated_succ k hr0 h_sd
  exact ⟨hasBallParityWitnessFamily_transportBundled (bdlIteratedBundled_eq (k + 1)) hP,
         hasBallParityWitnessFamily_dual_transportBundled (bdlIteratedBundled_eq (k + 1)) hD⟩

lemma bdlLambda_pow_le_bdlBoxSide (k : ℕ) : bdlLambda ^ k ≤ bdlBoxSide k :=
  le_trans (Nat.pow_le_pow_left (by dsimp [bBDL]; omega) k)
    (Nat.pow_le_pow_right b_bdl_pos (by dsimp [bdlHierarchySteps]; omega))

lemma thirtySeven_mul_bdlLambda_pow_le_bdlBoxSide (k : ℕ) :
    37 * bdlLambda ^ k ≤ bdlBoxSide k := by
  have h37 : 37 ≤ bdlLambda := by
    exact_mod_cast (by linarith [bdlLambda_ge_10000] : (37 : ℝ) ≤ (bdlLambda : ℝ))
  dsimp only [bdlBoxSide, bBDL, bdlHierarchySteps]
  calc 37 * bdlLambda ^ k
    _ ≤ bdlLambda ^ k * bdlLambda := by rw [mul_comm]; exact Nat.mul_le_mul_left _ h37
    _ = bdlLambda ^ (k + 1) := (pow_succ bdlLambda k).symm
    _ ≤ bdlLambda ^ (2 * k + 4) := Nat.pow_le_pow_right bdlLambda_pos (by omega)

lemma boxCube_subset_of_le {D L r₁ r₂ : ℕ} (x0 : BoxD D L) (h_le : r₁ ≤ r₂) :
    boxCube x0 r₁ ⊆ boxCube x0 r₂ := by
  intro x hx; rw [boxCube, Finset.mem_filter] at hx ⊢
  exact ⟨hx.1, fun i => ⟨(hx.2 i).1, lt_of_lt_of_le (hx.2 i).2 (Nat.add_le_add_left h_le _)⟩⟩

lemma exists_boxCube_superset_of_mem_boxCubes {D L r R : ℕ} {A : Finset (BoxD D L)}
    (hr : r ∈ Finset.Icc 1 R) (hA : A ∈ boxCubes D L r) :
    ∃ v0 : BoxD D L, A ⊆ boxCube v0 R := by
  rcases Finset.mem_image.mp hA with ⟨v0, _, h_eq⟩
  exact ⟨v0, h_eq ▸ boxCube_subset_of_le v0 (Finset.mem_Icc.mp hr).2⟩

lemma singleton_subset_boxCube_of_pos {D L R : ℕ} (hR : 0 < R) (v : BoxD D L) :
    ({v} : Finset (BoxD D L)) ⊆ boxCube v R := by
  rw [Finset.singleton_subset_iff, boxCube, Finset.mem_filter]
  exact ⟨Finset.mem_univ v, fun i => ⟨le_refl _, Nat.lt_add_of_pos_right hR⟩⟩

lemma one_le_cast_pow_of_pos {n : ℕ} (hn : 0 < n) (k : ℕ) : (1 : ℝ) ≤ ((n ^ k : ℕ) : ℝ) := by
  exact_mod_cast Nat.one_le_pow k n hn

lemma ball3D_two_subset_ball3D_two_mul {R : ℝ} (hR : 1 ≤ R) (x0 : Point3D) {p : Point3D}
    (hp : p ∈ ball3D x0 2) : p ∈ ball3D x0 (2 * R) := by
  dsimp [ball3D] at hp ⊢; nlinarith

lemma snapPointToOpenBox_mem_ball3D_two_mul {L R : ℕ} [NeZero L] {M : ℝ}
    (hL : M + 1000 ≤ (L : ℝ) / 2) (hR : 0 < R) {p : Point3D} {v0 : Box3D L} (hp : ∀ μ, |p μ| ≤ M)
    (hv : snapPointToOpenBox L p ∈ boxCube v0 R) :
    p ∈ ball3D (fun μ => ((v0 μ).val : ℝ) - (L : ℝ) / 2 + 1 / 2) (2 * (R : ℝ)) := by
  have hR1 : (1 : ℝ) ≤ (R : ℝ) := Nat.one_le_cast.mpr hR
  have h_coord : ∀ μ : Fin 3,
      (p μ - (((v0 μ).val : ℝ) - (L : ℝ) / 2 + 1 / 2)) ^ 2 ≤ (R : ℝ) ^ 2 := by
    intro μ
    have h_snap := (snapPointToOpenBox_bounds hL hp μ).2
    have h_cube := (Finset.mem_filter.mp hv).2 μ
    have h_lo : ((v0 μ).val : ℝ) ≤ ((snapPointToOpenBox L p μ).val : ℝ) := Nat.cast_le.mpr h_cube.1
    have h_hi : ((snapPointToOpenBox L p μ).val : ℝ) + 1 ≤ ((v0 μ).val : ℝ) + (R : ℝ) := by
      have h_nat : (snapPointToOpenBox L p μ).val + 1 ≤ (v0 μ).val + R := h_cube.2
      exact_mod_cast h_nat
    nlinarith
  have h0 := h_coord 0; have h1 := h_coord 1; have h2 := h_coord 2
  dsimp [ball3D, distSq3D]; nlinarith [sq_nonneg (R : ℝ)]

/-- Every qubit `q : BDLWeldedQubit k` whose grid-snapped vertex `bdlGridVertexQ k q` lies in
    `boxCube v0 (37 * bdlLambda ^ k)` has 3D Euclidean position `(bdlWeldedCode k).posQ q` inside
    `Ball3D (bdlGridCenter k v0) (2 * ((37 * bdlLambda ^ k : ℕ) : ℝ))`. -/
lemma posQ_mem_ball3D_lambdaPow_of_bdlGridVertexQ_mem_boxCube (k : ℕ)
    (v0 : Box3D (bdlBoxSide k)) (q : BDLWeldedQubit k)
    (hq : bdlGridVertexQ k q ∈ boxCube v0 (37 * bdlLambda ^ k)) :
    (bdlWeldedCode k).posQ q ∈ ball3D (bdlGridCenter k v0) (2 * ((37 * bdlLambda ^ k : ℕ) : ℝ)) :=
  snapPointToOpenBox_mem_ball3D_two_mul (bdlCoordBound_add_1000_le_half_L k)
    (Nat.mul_pos (by decide) (Nat.pow_pos bdlLambda_pos))
    ((hasBounded3DCoords_bdlWeldedBundled k).1 q) hq

private lemma weylPauliZX_mul_weylPauliZ_bdlPushChain_phase (k : ℕ)
    (a b : BoxSlot3D (bdlBoxSide k) qCodeBDL → ZMod 2) (c : BDLWeldedQubit k → ZMod 2) :
    (weylPauliZ a * weylPauliX b) * weylPauliZ (bdlPushChain k c) =
      signScalar (dualPairing c (bdlPullChain k b)) •
        (weylPauliZ (bdlPushChain k c) * (weylPauliZ a * weylPauliX b)) := by
  calc (weylPauliZ a * weylPauliX b) * weylPauliZ (bdlPushChain k c)
    _ = weylPauliZ a * (weylPauliX b * weylPauliZ (bdlPushChain k c)) := by rw [mul_assoc]
    _ = pauliPhase (bdlPushChain k c) b •
          ((weylPauliZ a * weylPauliZ (bdlPushChain k c)) * weylPauliX b) := by
      rw [weylPauliX_mul_weylPauliZ, clm_mul_smul, mul_assoc]
    _ = signScalar (dualPairing c (bdlPullChain k b)) •
          (weylPauliZ (bdlPushChain k c) * (weylPauliZ a * weylPauliX b)) := by
      rw [(weylPauliZ_comm a (bdlPushChain k c)).eq, mul_assoc,
        pauliPhase_eq_signScalar, sum_bdlPushChain_mul_eq_dualPairing_bdlPullChain]

private lemma weylPauliZX_mul_weylPauliX_bdlPushChain_phase (k : ℕ)
    (a b : BoxSlot3D (bdlBoxSide k) qCodeBDL → ZMod 2) (c : BDLWeldedQubit k → ZMod 2) :
    (weylPauliZ a * weylPauliX b) * weylPauliX (bdlPushChain k c) =
      signScalar (dualPairing c (bdlPullChain k a)) •
        (weylPauliX (bdlPushChain k c) * (weylPauliZ a * weylPauliX b)) := by
  have hXZ := weylPauliX_mul_weylPauliZ a (bdlPushChain k c)
  rw [pauliPhase_eq_signScalar, sum_mul_bdlPushChain_eq_dualPairing_bdlPullChain] at hXZ
  have hZX : weylPauliZ a * weylPauliX (bdlPushChain k c) =
      signScalar (dualPairing c (bdlPullChain k a)) •
        (weylPauliX (bdlPushChain k c) * weylPauliZ a) := by
    symm; rw [hXZ, smul_smul, signScalar_mul_self, one_smul]
  calc (weylPauliZ a * weylPauliX b) * weylPauliX (bdlPushChain k c)
    _ = (weylPauliZ a * weylPauliX (bdlPushChain k c)) * weylPauliX b := by
      rw [mul_assoc, (weylPauliX_comm b (bdlPushChain k c)).eq, ← mul_assoc]
    _ = signScalar (dualPairing c (bdlPullChain k a)) •
          (weylPauliX (bdlPushChain k c) * (weylPauliZ a * weylPauliX b)) := by
      rw [hZX, clm_smul_mul, mul_assoc]

private lemma commutator_eq_zero_of_isSupportedOn_disjoint_weylPauli {L q_code : ℕ} (A : Finset (Box3D L))
    (P O A_op : ManyBodyHilbertSpace (UniformSite3D L (CodeSlotConfig q_code)) →L[ℂ]
      ManyBodyHilbertSpace (UniformSite3D L (CodeSlotConfig q_code)))
    (hA : IsSupportedOn (UniformSite3D L (CodeSlotConfig q_code)) A A_op)
    (h_pauli : ∀ a b : BoxSlot3D L q_code → ZMod 2,
      BoxSlotChainSupportedIn a A → BoxSlotChainSupportedIn b A →
      P * ((weylPauliZ a * weylPauliX b) * O - O * (weylPauliZ a * weylPauliX b)) * P = 0) :
    P * (A_op * O - O * A_op) * P = 0 := by
  obtain ⟨ι, hι_fin, w_coeff, a_fam, b_fam, ha_supp, hb_supp, hA_eq⟩ :=
    exists_weylPauli_expansion_of_isSupportedOn A hA
  letI : Fintype ι := hι_fin
  rw [hA_eq]; ext φ : 1
  simp only [ContinuousLinearMap.mul_apply, ContinuousLinearMap.sub_apply,
    ContinuousLinearMap.sum_apply, ContinuousLinearMap.smul_apply,
    map_sub, map_sum, map_smul, ContinuousLinearMap.zero_apply]
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_eq_zero fun j _ => ?_
  have hj := congr_arg (fun T => T φ) (h_pauli (a_fam j) (b_fam j) (ha_supp j) (hb_supp j))
  simp only [ContinuousLinearMap.mul_apply, ContinuousLinearMap.sub_apply,
    ContinuousLinearMap.zero_apply, map_sub] at hj
  rw [← smul_sub, hj, smul_zero]

/-- Two-sided safe-syndrome immunity for any operator `A_op` supported on a subset
    `A ⊆ boxCube v0 (37 * bdlLambda ^ k)` at hierarchy level `k`. -/
lemma bdlSafeSyndromeSet_subset_boxCube_safe_immunity (k : ℕ)
    (ψ_Z : (BDLWeldedCheckX k → ZMod 2) → ZMod 2) (W_Z : Finset (BDLWeldedCheckX k → ZMod 2))
    (ψ_X : (BDLWeldedCheckZ k → ZMod 2) → ZMod 2) (W_X : Finset (BDLWeldedCheckZ k → ZMod 2))
    (hWZ_fail : ∀ (e_err e' : BDLWeldedQubit k → ZMod 2) (x0 : Point3D),
      (∀ q : BDLWeldedQubit k, e_err q ≠ e' q →
        (bdlWeldedCode k).posQ q ∈ ball3D x0 (2 * ((37 * bdlLambda ^ k : ℕ) : ℝ))) →
      ψ_Z (syndrome (bdlWeldedCode k) e') + dualPairing (bdlWeldedLX k) e' ≠
        ψ_Z (syndrome (bdlWeldedCode k) e_err) + dualPairing (bdlWeldedLX k) e_err →
      ∃ c ∈ W_Z, (∀ m : BDLWeldedCheckX k, c m ≠ 0 → syndrome (bdlWeldedCode k) e_err m ≠ 0) ∨
               (∀ m : BDLWeldedCheckX k, c m ≠ 0 → syndrome (bdlWeldedCode k) e' m ≠ 0))
    (hWX_fail : ∀ (e_err e' : BDLWeldedQubit k → ZMod 2) (x0 : Point3D),
      (∀ q : BDLWeldedQubit k, e_err q ≠ e' q →
        (bdlWeldedCode k).posQ q ∈ ball3D x0 (2 * ((37 * bdlLambda ^ k : ℕ) : ℝ))) →
      ψ_X (syndrome (dualCode (bdlWeldedCode k)) e') + dualPairing (bdlWeldedLZ k) e' ≠
        ψ_X (syndrome (dualCode (bdlWeldedCode k)) e_err) + dualPairing (bdlWeldedLZ k) e_err →
      ∃ c ∈ W_X, (∀ m : BDLWeldedCheckZ k, c m ≠ 0 → syndrome (dualCode (bdlWeldedCode k)) e_err m ≠ 0) ∨
               (∀ m : BDLWeldedCheckZ k, c m ≠ 0 → syndrome (dualCode (bdlWeldedCode k)) e' m ≠ 0))
    (v0 : Box3D (bdlBoxSide k)) (A : Finset (Box3D (bdlBoxSide k)))
    (hA_sub : A ⊆ boxCube v0 (37 * bdlLambda ^ k))
    (A_op : ManyBodyHilbertSpace (UniformSite3D (bdlBoxSide k) (CodeSlotConfig qCodeBDL)) →L[ℂ]
      ManyBodyHilbertSpace (UniformSite3D (bdlBoxSide k) (CodeSlotConfig qCodeBDL)))
    (hA_op : IsSupportedOn (UniformSite3D (bdlBoxSide k) (CodeSlotConfig qCodeBDL)) A A_op) :
    let sys := bdlInhomogeneousSystem k
    let Pi_safe := syndromeSubsetProj sys (bdlSafeSyndromeSet k W_Z W_X)
    let O_dec_Z := weylPauliZ (bdlPushChain k (bdlWeldedLZ k)) *
      syndromeSignOp sys (fun σ => ψ_X (bdlPullSynZ k σ))
    let O_dec_X := weylPauliX (bdlPushChain k (bdlWeldedLX k)) *
      syndromeSignOp sys (fun σ => ψ_Z (bdlPullSynX k σ))
    Pi_safe * (A_op * O_dec_Z - O_dec_Z * A_op) * Pi_safe = 0 ∧
    Pi_safe * (A_op * O_dec_X - O_dec_X * A_op) * Pi_safe = 0 := by
  intro sys Pi_safe O_dec_Z O_dec_X
  have hZ_comm : ∀ i, Commute (weylPauliZ (bdlPushChain k (bdlWeldedLZ k))) (sys.checkProj i) :=
    fun i => (weylPauliZ_bdlPushChain_commute_checkProj k (bdlWeldedLZ k) (syndrome_bdlWeldedLZ k) i).symm
  have hX_comm : ∀ i, Commute (weylPauliX (bdlPushChain k (bdlWeldedLX k))) (sys.checkProj i) :=
    fun i => (weylPauliX_bdlPushChain_commute_checkProj k (bdlWeldedLX k) (syndrome_bdlWeldedLX k) i).symm
  have h_alg : ∀ x u y z : ZMod 2, x + (y + z) = u + y → x = u + z := by decide
  have h_ball : ∀ c : BoxSlot3D (bdlBoxSide k) qCodeBDL → ZMod 2, BoxSlotChainSupportedIn c A →
      ∀ q : BDLWeldedQubit k, bdlPullChain k c q ≠ 0 →
        (bdlWeldedCode k).posQ q ∈ ball3D (bdlGridCenter k v0) (2 * ((37 * bdlLambda ^ k : ℕ) : ℝ)) := by
    intro c hc_supp q hq_ne
    apply posQ_mem_ball3D_lambdaPow_of_bdlGridVertexQ_mem_boxCube k v0 q
    have hp_mem := hc_supp (bdlQubitSiteSlot k q) hq_ne
    rw [bdlQubitSiteSlot_eq k q] at hp_mem; exact hA_sub hp_mem
  have h_pauli : ∀ a b : BoxSlot3D (bdlBoxSide k) qCodeBDL → ZMod 2,
      BoxSlotChainSupportedIn a A → BoxSlotChainSupportedIn b A →
      Pi_safe * ((weylPauliZ a * weylPauliX b) * O_dec_Z - O_dec_Z * (weylPauliZ a * weylPauliX b)) * Pi_safe = 0 ∧
      Pi_safe * ((weylPauliZ a * weylPauliX b) * O_dec_X - O_dec_X * (weylPauliZ a * weylPauliX b)) * Pi_safe = 0 := by
    intro a b ha_supp hb_supp
    refine ⟨?_, ?_⟩
    · apply syndromeSubsetProj_commutator_eq_zero_of_checkFlip sys hZ_comm
        (fun σ => ψ_X (bdlPullSynZ k σ)) (bdlSafeSyndromeSet k W_Z W_X)
        (weylPauliZX_mul_staticCSSCheckProj (bdlLocalDescriptor k) a b)
        (weylPauliZX_mul_weylPauliZ_bdlPushChain_phase k a b (bdlWeldedLZ k))
      intro σ hσ h_nz hσ'
      obtain ⟨a₀, b₀, hσ_eq, _⟩ := exists_chains_of_syndromeProjector_ne_zero
        (bdlLocalDescriptor k) (bdlLocalDescriptor_validDescriptorField k) σ h_nz
      let e_err := bdlPullChain k b₀; let e' := e_err + bdlPullChain k b
      have h_syn_err : bdlPullSynZ k σ = syndrome (dualCode (bdlWeldedCode k)) e_err := by
        rw [hσ_eq, bdlPullSynZ_staticCSSPauliFlip]
      have h_syn_e' : bdlPullSynZ k (fun i => xor (σ i) (staticCSSPauliFlip (bdlLocalDescriptor k) a b i)) =
          syndrome (dualCode (bdlWeldedCode k)) e' := by
        rw [bdlPullSynZ_xor_staticCSSPauliFlip, h_syn_err, map_add]
      have h_diff : ∀ q : BDLWeldedQubit k, e_err q ≠ e' q →
          (bdlWeldedCode k).posQ q ∈ ball3D (bdlGridCenter k v0) (2 * ((37 * bdlLambda ^ k : ℕ) : ℝ)) :=
        fun q hq => h_ball b hb_supp q (fun hb0 => hq (by dsimp [e']; rw [hb0, add_zero]))
      have h_eq_parity : ψ_X (syndrome (dualCode (bdlWeldedCode k)) e') + dualPairing (bdlWeldedLZ k) e' =
          ψ_X (syndrome (dualCode (bdlWeldedCode k)) e_err) + dualPairing (bdlWeldedLZ k) e_err := by
        by_contra h_disc
        obtain ⟨c, hcW, h1 | h2⟩ := hWX_fail e_err e' (bdlGridCenter k v0) h_diff h_disc
        · exact (Finset.mem_filter.mp hσ).2.2 c hcW (by rwa [h_syn_err])
        · exact (Finset.mem_filter.mp hσ').2.2 c hcW (by rwa [h_syn_e'])
      rw [h_syn_e', h_syn_err]
      rw [dualPairing_add_right_zmod2 (bdlWeldedLZ k) e_err (bdlPullChain k b)] at h_eq_parity
      exact h_alg _ _ _ _ h_eq_parity
    · apply syndromeSubsetProj_commutator_eq_zero_of_checkFlip sys hX_comm
        (fun σ => ψ_Z (bdlPullSynX k σ)) (bdlSafeSyndromeSet k W_Z W_X)
        (weylPauliZX_mul_staticCSSCheckProj (bdlLocalDescriptor k) a b)
        (weylPauliZX_mul_weylPauliX_bdlPushChain_phase k a b (bdlWeldedLX k))
      intro σ hσ h_nz hσ'
      obtain ⟨a₀, b₀, hσ_eq, _⟩ := exists_chains_of_syndromeProjector_ne_zero
        (bdlLocalDescriptor k) (bdlLocalDescriptor_validDescriptorField k) σ h_nz
      let e_err := bdlPullChain k a₀; let e' := e_err + bdlPullChain k a
      have h_syn_err : bdlPullSynX k σ = syndrome (bdlWeldedCode k) e_err := by
        rw [hσ_eq, bdlPullSynX_staticCSSPauliFlip]
      have h_syn_e' : bdlPullSynX k (fun i => xor (σ i) (staticCSSPauliFlip (bdlLocalDescriptor k) a b i)) =
          syndrome (bdlWeldedCode k) e' := by
        rw [bdlPullSynX_xor_staticCSSPauliFlip, h_syn_err, map_add]
      have h_diff : ∀ q : BDLWeldedQubit k, e_err q ≠ e' q →
          (bdlWeldedCode k).posQ q ∈ ball3D (bdlGridCenter k v0) (2 * ((37 * bdlLambda ^ k : ℕ) : ℝ)) :=
        fun q hq => h_ball a ha_supp q (fun ha0 => hq (by dsimp [e']; rw [ha0, add_zero]))
      have h_eq_parity : ψ_Z (syndrome (bdlWeldedCode k) e') + dualPairing (bdlWeldedLX k) e' =
          ψ_Z (syndrome (bdlWeldedCode k) e_err) + dualPairing (bdlWeldedLX k) e_err := by
        by_contra h_disc
        obtain ⟨c, hcW, h1 | h2⟩ := hWZ_fail e_err e' (bdlGridCenter k v0) h_diff h_disc
        · exact (Finset.mem_filter.mp hσ).2.1 c hcW (by rwa [h_syn_err])
        · exact (Finset.mem_filter.mp hσ').2.1 c hcW (by rwa [h_syn_e'])
      rw [h_syn_e', h_syn_err]
      rw [dualPairing_add_right_zmod2 (bdlWeldedLX k) e_err (bdlPullChain k a)] at h_eq_parity
      exact h_alg _ _ _ _ h_eq_parity
  exact ⟨commutator_eq_zero_of_isSupportedOn_disjoint_weylPauli A Pi_safe O_dec_Z A_op hA_op
      (fun a b ha hb => (h_pauli a b ha hb).1),
    commutator_eq_zero_of_isSupportedOn_disjoint_weylPauli A Pi_safe O_dec_X A_op hA_op
      (fun a b ha hb => (h_pauli a b ha hb).2)⟩

/-- **Unconditional Macroscopic Radius-`37 * bdlLambda ^ k` Cube Operator Safe-Subspace Immunity
    (`bdlSafeSyndromeSet_cube_op_safe_immunity_lambdaPow`)**:
    For every cube side `r ∈ Finset.Icc 1 (min (37 * bdlLambda ^ k) (bdlBoxSide k))`,
    every open-box cube `A ∈ boxCubes 3 (bdlBoxSide k) r`, and every operator `M_A` supported on `A`,
    the two-sided commutator sandwich with `Pi_safe` vanishes identically. -/
theorem bdlSafeSyndromeSet_cube_op_safe_immunity_lambdaPow (k : ℕ)
    (ψ_Z : (BDLWeldedCheckX k → ZMod 2) → ZMod 2) (W_Z : Finset (BDLWeldedCheckX k → ZMod 2))
    (ψ_X : (BDLWeldedCheckZ k → ZMod 2) → ZMod 2) (W_X : Finset (BDLWeldedCheckZ k → ZMod 2))
    (hWZ_fail : ∀ (e_err e' : BDLWeldedQubit k → ZMod 2) (x0 : Point3D),
      (∀ q : BDLWeldedQubit k, e_err q ≠ e' q →
        (bdlWeldedCode k).posQ q ∈ ball3D x0 (2 * ((37 * bdlLambda ^ k : ℕ) : ℝ))) →
      ψ_Z (syndrome (bdlWeldedCode k) e') + dualPairing (bdlWeldedLX k) e' ≠
        ψ_Z (syndrome (bdlWeldedCode k) e_err) + dualPairing (bdlWeldedLX k) e_err →
      ∃ c ∈ W_Z, (∀ m : BDLWeldedCheckX k, c m ≠ 0 → syndrome (bdlWeldedCode k) e_err m ≠ 0) ∨
               (∀ m : BDLWeldedCheckX k, c m ≠ 0 → syndrome (bdlWeldedCode k) e' m ≠ 0))
    (hWX_fail : ∀ (e_err e' : BDLWeldedQubit k → ZMod 2) (x0 : Point3D),
      (∀ q : BDLWeldedQubit k, e_err q ≠ e' q →
        (bdlWeldedCode k).posQ q ∈ ball3D x0 (2 * ((37 * bdlLambda ^ k : ℕ) : ℝ))) →
      ψ_X (syndrome (dualCode (bdlWeldedCode k)) e') + dualPairing (bdlWeldedLZ k) e' ≠
        ψ_X (syndrome (dualCode (bdlWeldedCode k)) e_err) + dualPairing (bdlWeldedLZ k) e_err →
      ∃ c ∈ W_X, (∀ m : BDLWeldedCheckZ k, c m ≠ 0 → syndrome (dualCode (bdlWeldedCode k)) e_err m ≠ 0) ∨
               (∀ m : BDLWeldedCheckZ k, c m ≠ 0 → syndrome (dualCode (bdlWeldedCode k)) e' m ≠ 0))
    (r : ℕ) (hr : r ∈ Finset.Icc 1 (min (37 * bdlLambda ^ k) (bdlBoxSide k)))
    (A : Finset (Box3D (bdlBoxSide k))) (hA : A ∈ boxCubes 3 (bdlBoxSide k) r)
    (M_A : ManyBodyHilbertSpace (UniformSite3D (bdlBoxSide k) (CodeSlotConfig qCodeBDL)) →L[ℂ]
      ManyBodyHilbertSpace (UniformSite3D (bdlBoxSide k) (CodeSlotConfig qCodeBDL)))
    (hM_A : IsSupportedOn (UniformSite3D (bdlBoxSide k) (CodeSlotConfig qCodeBDL)) A M_A) :
    let sys := bdlInhomogeneousSystem k
    let Pi_safe := syndromeSubsetProj sys (bdlSafeSyndromeSet k W_Z W_X)
    let O_dec_Z := weylPauliZ (bdlPushChain k (bdlWeldedLZ k)) *
      syndromeSignOp sys (fun σ => ψ_X (bdlPullSynZ k σ))
    let O_dec_X := weylPauliX (bdlPushChain k (bdlWeldedLX k)) *
      syndromeSignOp sys (fun σ => ψ_Z (bdlPullSynX k σ))
    Pi_safe * (M_A * O_dec_Z - O_dec_Z * M_A) * Pi_safe = 0 ∧
    Pi_safe * (M_A * O_dec_X - O_dec_X * M_A) * Pi_safe = 0 := by
  have hr37 : r ∈ Finset.Icc 1 (37 * bdlLambda ^ k) :=
    Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp hr).1, le_trans (Finset.mem_Icc.mp hr).2 (min_le_left _ _)⟩
  rcases exists_boxCube_superset_of_mem_boxCubes hr37 hA with ⟨v0, hv0⟩
  exact bdlSafeSyndromeSet_subset_boxCube_safe_immunity k ψ_Z W_Z ψ_X W_X hWZ_fail hWX_fail
    v0 A hv0 M_A hM_A

/-- **Unconditional Macroscopic Radius-`37 * bdlLambda ^ k` Cube Safe-Subspace Immunity (`bdlSafeSyndromeSet_cube_safe_immunity_lambdaPow`)**:
    For every quasi-local perturbation `V` on `Box3D (bdlBoxSide k)`, every interaction scale
    `r ∈ Finset.Icc 1 (37 * bdlLambda ^ k)`, and every open-box cube `A ∈ BoxCubes 3 (bdlBoxSide k) r`,
    the two-sided commutator sandwich with `Pi_safe` vanishes identically. -/
theorem bdlSafeSyndromeSet_cube_safe_immunity_lambdaPow (k : ℕ)
    (ψ_Z : (BDLWeldedCheckX k → ZMod 2) → ZMod 2) (W_Z : Finset (BDLWeldedCheckX k → ZMod 2))
    (ψ_X : (BDLWeldedCheckZ k → ZMod 2) → ZMod 2) (W_X : Finset (BDLWeldedCheckZ k → ZMod 2))
    (hWZ_fail : ∀ (e_err e' : BDLWeldedQubit k → ZMod 2) (x0 : Point3D),
      (∀ q : BDLWeldedQubit k, e_err q ≠ e' q →
        (bdlWeldedCode k).posQ q ∈ ball3D x0 (2 * ((37 * bdlLambda ^ k : ℕ) : ℝ))) →
      ψ_Z (syndrome (bdlWeldedCode k) e') + dualPairing (bdlWeldedLX k) e' ≠
        ψ_Z (syndrome (bdlWeldedCode k) e_err) + dualPairing (bdlWeldedLX k) e_err →
      ∃ c ∈ W_Z, (∀ m : BDLWeldedCheckX k, c m ≠ 0 → syndrome (bdlWeldedCode k) e_err m ≠ 0) ∨
               (∀ m : BDLWeldedCheckX k, c m ≠ 0 → syndrome (bdlWeldedCode k) e' m ≠ 0))
    (hWX_fail : ∀ (e_err e' : BDLWeldedQubit k → ZMod 2) (x0 : Point3D),
      (∀ q : BDLWeldedQubit k, e_err q ≠ e' q →
        (bdlWeldedCode k).posQ q ∈ ball3D x0 (2 * ((37 * bdlLambda ^ k : ℕ) : ℝ))) →
      ψ_X (syndrome (dualCode (bdlWeldedCode k)) e') + dualPairing (bdlWeldedLZ k) e' ≠
        ψ_X (syndrome (dualCode (bdlWeldedCode k)) e_err) + dualPairing (bdlWeldedLZ k) e_err →
      ∃ c ∈ W_X, (∀ m : BDLWeldedCheckZ k, c m ≠ 0 → syndrome (dualCode (bdlWeldedCode k)) e_err m ≠ 0) ∨
               (∀ m : BDLWeldedCheckZ k, c m ≠ 0 → syndrome (dualCode (bdlWeldedCode k)) e' m ≠ 0))
    (V : QuasiLocalPerturbation 3 (bdlBoxSide k)
      (UniformSite3D (bdlBoxSide k) (CodeSlotConfig qCodeBDL)))
    (r : ℕ) (hr : r ∈ Finset.Icc 1 (37 * bdlLambda ^ k))
    (A : Finset (Box3D (bdlBoxSide k))) (hA : A ∈ boxCubes 3 (bdlBoxSide k) r) :
    let sys := bdlInhomogeneousSystem k
    let Pi_safe := syndromeSubsetProj sys (bdlSafeSyndromeSet k W_Z W_X)
    let O_dec_Z := weylPauliZ (bdlPushChain k (bdlWeldedLZ k)) *
      syndromeSignOp sys (fun σ => ψ_X (bdlPullSynZ k σ))
    let O_dec_X := weylPauliX (bdlPushChain k (bdlWeldedLX k)) *
      syndromeSignOp sys (fun σ => ψ_Z (bdlPullSynX k σ))
    Pi_safe * (V.term r A * O_dec_Z - O_dec_Z * V.term r A) * Pi_safe = 0 ∧
    Pi_safe * (V.term r A * O_dec_X - O_dec_X * V.term r A) * Pi_safe = 0 := by
  have hL : r ≤ bdlBoxSide k :=
    le_trans (Finset.mem_Icc.mp hr).2 (thirtySeven_mul_bdlLambda_pow_le_bdlBoxSide k)
  have hr_min : r ∈ Finset.Icc 1 (min (37 * bdlLambda ^ k) (bdlBoxSide k)) :=
    Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp hr).1, le_min (Finset.mem_Icc.mp hr).2 hL⟩
  have hrL : r ∈ Finset.Icc 1 (bdlBoxSide k) :=
    Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp hr).1, hL⟩
  exact bdlSafeSyndromeSet_cube_op_safe_immunity_lambdaPow k ψ_Z W_Z ψ_X W_X hWZ_fail hWX_fail
    r hr_min A hA (V.term r A) (V.is_supported r hrL A hA)

theorem bdl_inhomogeneous_safe_projector_and_macroscopic_immunity_exists (k : ℕ) :
    let L := bdlBoxSide k; let D_field := bdlLocalDescriptor k
    ∃ (sys : IndexedCommutingProjectorHamiltonian 3 L
        (UniformSite3D L (CodeSlotConfig qCodeBDL)) (StaticCSSCheckIdx L qCodeBDL mMaxBDL))
      (Z_log X_log Pi_safe O_dec_Z O_dec_X :
        ManyBodyHilbertSpace (UniformSite3D L (CodeSlotConfig qCodeBDL)) →L[ℂ]
          ManyBodyHilbertSpace (UniformSite3D L (CodeSlotConfig qCodeBDL))),
      (∀ idx : StaticCSSCheckIdx L qCodeBDL mMaxBDL,
        sys.checkProj idx = staticCSSCheckProj D_field idx ∧
        sys.support idx = staticCSSCheckSupport D_field idx ∧ sys.weight idx = 1) ∧
      (sys.P0 ≠ 0 ∧ sys.P0 ≠ 1) ∧ SatisfiesTQO1 sys (bdlLinearTQORadius k) ∧
      SatisfiesLinearTQO2 sys (bdlLinearTQORadius k) (collarConstRCABDL : ℝ) ∧
      SatisfiesSectorFilteredLinearTQO2 sys 1 (bdlLinearTQORadius k) (collarConstRCABDL : ℝ) ∧
      (IsSelfAdjoint Z_log ∧ Z_log * Z_log = 1 ∧ Commute sys.H0 Z_log ∧ Commute sys.P0 Z_log) ∧
      (IsSelfAdjoint X_log ∧ X_log * X_log = 1 ∧ Commute sys.H0 X_log ∧ Commute sys.P0 X_log) ∧
      (Z_log * X_log + X_log * Z_log) * sys.P0 = 0 ∧ (Z_log * sys.P0 ≠ 0 ∧ X_log * sys.P0 ≠ 0) ∧
      (IsStarProjection Pi_safe ∧ Pi_safe ≠ 0 ∧ Pi_safe ≠ 1 ∧
        Commute sys.H0 Pi_safe ∧ sys.P0 * Pi_safe = sys.P0) ∧
      (IsSelfAdjoint O_dec_Z ∧ O_dec_Z * O_dec_Z = 1 ∧ ‖O_dec_Z‖ ≤ 1 ∧
        Commute sys.H0 O_dec_Z ∧ O_dec_Z * sys.P0 = Z_log * sys.P0 ∧
        Pi_safe * (sys.P0 - O_dec_Z * sys.P0 * O_dec_Z†) * Pi_safe = 0) ∧
      (IsSelfAdjoint O_dec_X ∧ O_dec_X * O_dec_X = 1 ∧ ‖O_dec_X‖ ≤ 1 ∧
        Commute sys.H0 O_dec_X ∧ O_dec_X * sys.P0 = X_log * sys.P0 ∧
        Pi_safe * (sys.P0 - O_dec_X * sys.P0 * O_dec_X†) * Pi_safe = 0) ∧
      (∀ (v : Box3D L) (A_v : ManyBodyHilbertSpace (UniformSite3D L (CodeSlotConfig qCodeBDL)) →L[ℂ]
           ManyBodyHilbertSpace (UniformSite3D L (CodeSlotConfig qCodeBDL))),
         IsSupportedOn (UniformSite3D L (CodeSlotConfig qCodeBDL)) {v} A_v →
         Pi_safe * (A_v * O_dec_Z - O_dec_Z * A_v) * Pi_safe = 0 ∧
         Pi_safe * (A_v * O_dec_X - O_dec_X * A_v) * Pi_safe = 0) ∧
      (∀ (V : QuasiLocalPerturbation 3 L (UniformSite3D L (CodeSlotConfig qCodeBDL))),
         ∀ r ∈ Finset.Icc 1 (bdlLambda ^ k), ∀ A ∈ boxCubes 3 L r,
           Pi_safe * (V.term r A * O_dec_Z - O_dec_Z * V.term r A) * Pi_safe = 0 ∧
           Pi_safe * (V.term r A * O_dec_X - O_dec_X * V.term r A) * Pi_safe = 0) ∧
      (∀ β : ℝ, β > betaCritBDL →
        gibbsFailureProb sys.H0 sys.isSelfAdjoint_H0 β (1 - Pi_safe) ≤
          Real.exp (- bdlFreeEnergyBarrier k β)) := by
  obtain ⟨⟨ψ_Z, W_Z, hψZ0, hWZ_card, hWZ_wt, hWZ_fail⟩,
          ⟨ψ_X, W_X, hψX0, hWX_card, hWX_wt, hWX_fail⟩⟩ :=
    hasBallParityWitnessFamily_bdlWelded_lambdaPow k
  have h37_pos : 0 < 37 * bdlLambda ^ k := Nat.mul_pos (by decide) (Nat.pow_pos bdlLambda_pos)
  have hWZ_fail_two : ∀ (e_err e' : BDLWeldedQubit k → ZMod 2) (x0 : Point3D),
      (∀ q : BDLWeldedQubit k, e_err q ≠ e' q → (bdlWeldedCode k).posQ q ∈ ball3D x0 2) →
      ψ_Z (syndrome (bdlWeldedCode k) e') + dualPairing (bdlWeldedLX k) e' ≠
        ψ_Z (syndrome (bdlWeldedCode k) e_err) + dualPairing (bdlWeldedLX k) e_err →
      ∃ c ∈ W_Z, (∀ m : BDLWeldedCheckX k, c m ≠ 0 → syndrome (bdlWeldedCode k) e_err m ≠ 0) ∨
               (∀ m : BDLWeldedCheckX k, c m ≠ 0 → syndrome (bdlWeldedCode k) e' m ≠ 0) :=
    fun e_err e' x0 h_diff => hWZ_fail e_err e' x0
      (fun q hq => ball3D_two_subset_ball3D_two_mul
        (Nat.one_le_cast.mpr h37_pos) x0 (h_diff q hq))
  have h_tqo := bdlInhomogeneousSystem_satisfiesOperatorTQO k
  have h_bare := bdl_bare_logical_props k (bdlWeldedLZ k) (bdlWeldedLX k)
    (syndrome_bdlWeldedLZ k) (syndrome_bdlWeldedLX k) (dualPairing_bdlWeldedLZ_bdlWeldedLX k)
  have hw_ge1 : (1 : ℝ) ≤ ((clusterRawWeight k : ℕ) : ℝ) :=
    (one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 3 / 2)).trans (three_div_two_pow_le_clusterRawWeight k)
  have h0_mem : (fun _ => false) ∈ bdlSafeSyndromeSet k W_Z W_X :=
    false_mem_bdlSafeSyndromeSet k W_Z W_X
      (fun c hc => hw_ge1.trans (hWZ_wt c hc)) (fun c hc => hw_ge1.trans (hWX_wt c hc))
  have h_sd := safeAndDecoded_props_of_commute (bdlInhomogeneousSystem k)
    (weylPauliZ (bdlPushChain k (bdlWeldedLZ k))) (weylPauliX (bdlPushChain k (bdlWeldedLX k)))
    (bdlInhomogeneousSystem_P0_ne_zero_and_ne_one k).1 h_bare.1.1 h_bare.1.2.1
    (weylPauliZ_bdlPushChain_commute_checkProj k (bdlWeldedLZ k) (syndrome_bdlWeldedLZ k))
    h_bare.2.1.1 h_bare.2.1.2.1
    (weylPauliX_bdlPushChain_commute_checkProj k (bdlWeldedLX k) (syndrome_bdlWeldedLX k))
    (bdlSafeSyndromeSet k W_Z W_X) h0_mem
    (syndromeSubsetProj_bdlSafeSyndromeSet_ne_one k ψ_Z W_Z W_X hψZ0 hWZ_fail_two)
    (fun σ => ψ_X (bdlPullSynZ k σ)) (fun σ => ψ_Z (bdlPullSynX k σ))
    (by (try dsimp only); rw [bdlPullSynZ_false]; exact hψX0) (by (try dsimp only); rw [bdlPullSynX_false]; exact hψZ0)
  refine ⟨bdlInhomogeneousSystem k, weylPauliZ (bdlPushChain k (bdlWeldedLZ k)),
    weylPauliX (bdlPushChain k (bdlWeldedLX k)),
    syndromeSubsetProj (bdlInhomogeneousSystem k) (bdlSafeSyndromeSet k W_Z W_X),
    weylPauliZ (bdlPushChain k (bdlWeldedLZ k)) *
      syndromeSignOp (bdlInhomogeneousSystem k) (fun σ => ψ_X (bdlPullSynZ k σ)),
    weylPauliX (bdlPushChain k (bdlWeldedLX k)) *
      syndromeSignOp (bdlInhomogeneousSystem k) (fun σ => ψ_Z (bdlPullSynX k σ)),
    fun _ => ⟨rfl, rfl, rfl⟩, bdlInhomogeneousSystem_P0_ne_zero_and_ne_one k,
    h_tqo.1, h_tqo.2.1, h_tqo.2.2, h_bare.1, h_bare.2.1, h_bare.2.2.1, h_bare.2.2.2,
    h_sd.1, h_sd.2.1, h_sd.2.2,
    fun v A_v hA_v => bdlSafeSyndromeSet_subset_boxCube_safe_immunity k ψ_Z W_Z ψ_X W_X
      hWZ_fail hWX_fail v {v} (singleton_subset_boxCube_of_pos h37_pos v) A_v hA_v,
    fun V r hr A hA => bdlSafeSyndromeSet_cube_safe_immunity_lambdaPow k ψ_Z W_Z ψ_X W_X
      hWZ_fail hWX_fail V r
      (Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp hr).1,
        le_trans (Finset.mem_Icc.mp hr).2 (Nat.le_mul_of_pos_left _ (by decide))⟩) A hA,
    fun β hβ => gibbsFailureProb_bdlSafeSyndromeSet_le k W_Z W_X hWZ_card hWZ_wt hWX_card hWX_wt β hβ⟩

end
