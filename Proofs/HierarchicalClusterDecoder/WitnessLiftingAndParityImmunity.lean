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

import Proofs.HierarchicalClusterDecoder.TwoHopTannerContraction

/-!
# Two-Hop Pool Contraction, Witness Lifting, and Recursive Parity Rule Immunity

Packages the 16/27 two-hop bipartite contraction theorems (`two_hop_bipartite_pool_contraction`, `two_hop_cluster_disjoint_weight_add`) and lifts parity witness pools across bounded-degree two-hop neighborhoods (`liftWitnessFamily_of_pool`, `liftWitnessFamily_rx_twoHop_step`). Defines the recursive parity decoding rules `rxCleanedParityRule` and `rzCoarseParityRule` and proves their exact logical discrepancy transfer (`rxCleanedParityRule_discrepancy_eq`, `rzCoarseParityRule_discrepancy_eq`).

## References

* Part I, Section 4.3 (`subsec:stage2-star`), Theorem 4.3 (`thm:16-27-contraction`)
* Part I, Section 5.2 (`subsec:cluster-decoder`), Definition 5.2 (`def:multiscale-cluster-decoder`), Proposition 5.3 (`prop:cluster-decoder-witness`)
* Part II, Section 4 (`subsec:welded-hierarchy-cleaner`), Definition 4.2 (`def:multiscale-cluster-decoder`), Lemma 4.4 (`lem:two-stage-cleaner-contraction`)
-/

noncomputable section

open scoped Classical
open BigOperators

set_option maxHeartbeats 800000

namespace WeldedHierarchy

/-- **Two-Hop Bipartite Tanner Neighborhood Bound (Part I, Section 4.3, Theorem 4.3 (`thm:16-27-contraction`))**:
    For any subset $K_Z$ of active coarse $Z$-checks in `pcode` under bounded check degrees
    ($d_Z \le 8$, $d_{Q,X} \le 4$), the two-hop Tanner neighborhood has cardinality at most
    $41 \cdot |K_Z|$. -/
theorem two_hop_bipartite_pool_bound {Q M_Z M_X : Type}
    [Fintype Q] [DecidableEq Q] [Fintype M_Z] [DecidableEq M_Z] [Fintype M_X] [DecidableEq M_X]
    (pcode : CSSCode3D Q M_Z M_X)
    (hdZ : ∀ z0 : M_Z, (Finset.univ.filter (fun q0 : Q => pcode.checkZ z0 q0 ≠ 0)).card ≤ 8)
    (hdQX : ∀ q0 : Q, (Finset.univ.filter (fun x : M_X => pcode.checkX x q0 ≠ 0)).card ≤ 4)
    (K_Z : Finset M_Z) :
    (BDLDecoder.twoHopTannerOfZ pcode K_Z).card ≤ 41 * K_Z.card :=
  BDLDecoder.card_twoHopTannerOfZ_le pcode hdZ hdQX K_Z

/-- **Stage-2 Star Cleaner Contraction (`stage2_star_cleaner_exists`, Part I, Lemma 4.2 (`lem:stage2-star-cleaner`), Theorem 4.3 (`thm:16-27-contraction`))**:
    After Stage-1 cylinder cleaning zeroes out `restrictCX2` on all cylinders $x \in M_X$, for every
    coarse qubit $q_0 \in Q$ there exists a local star cleaner $v_{q_0}$ supported in $Y_{q_0}$ that
    clears the restricted star syndrome `restrictCQ2` while exporting at most $4/3$ of the collapsed
    net star syndrome weight: $3 |\mathrm{export}_{Q \to Z}(v_{q_0})| \le 4\,\mathrm{wt}_{\mathrm{net}}(\sigma_1|_{Y_{q_0}})$. -/
theorem stage2_star_cleaner_exists {Q M_Z M_X : Type}
    [Fintype Q] [DecidableEq Q] [Fintype M_Z] [DecidableEq M_Z] [Fintype M_X] [DecidableEq M_X]
    (pcode : CSSCode3D Q M_Z M_X) (M : ℕ)
    (hov : ∀ (x' : M_X) (z' : M_Z),
      (Finset.univ.filter (fun q' : Q => pcode.checkX x' q' ≠ 0 ∧ pcode.checkZ z' q' ≠ 0)).card ≤ 2)
    (h_conn : HasConnectedXLinks pcode)
    (h1 : BDLStepXQ pcode M → ZMod 2)
    (h1_cyl : ∀ x : M_X,
      BDLDecoder.restrictCX2 pcode M x (syndrome (dualCode (bdlCylinderStepX pcode M)) h1) = 0)
    (q0 : Q) :
    ∃ v_q0 : BDLStepXQ pcode M → ZMod 2,
      (∀ q, v_q0 q ≠ 0 → ∃ qQ, q = Sum.inr qQ ∧ BDLDecoder.cQ1OwnerQ pcode M qQ = q0) ∧
      BDLDecoder.restrictCQ2 pcode M q0
        (syndrome (dualCode (bdlCylinderStepX pcode M)) (h1 + v_q0)) = 0 ∧
      3 * (Finset.univ.filter (fun mZ : BDLCZ2 M_Z => BDLDecoder.exportQZ pcode M v_q0 mZ ≠ 0)).card ≤
        4 * BDLDecoder.weightNetCQ2OnStar pcode M q0
          (BDLDecoder.restrictCQ2 pcode M q0 (syndrome (dualCode (bdlCylinderStepX pcode M)) h1)) ∧
      (BDLDecoder.restrictCQ2 pcode M q0
        (syndrome (dualCode (bdlCylinderStepX pcode M)) h1) = 0 → v_q0 = 0) :=
  BDLDecoder.exists_local_star_cleaner pcode M hov h_conn h1 h1_cyl q0

/-- **Component-Wise $27/16$ Syndrome Contraction
    (`two_hop_bipartite_component_contraction`, Part I, Theorem 4.3 (`thm:16-27-contraction`))**:
    Combining the 3-copy coarse $Z$-check bound ($3|K_Z| \le |\sigma|_{Z} + |\mathrm{export}_{Q \to Z}|$),
    the $4/3$ Stage-2 star cleaner bound, and the $4/3$ Stage-1 cylinder cleaner bound yields
    $$27 |\mathcal{R}_X^{\mathrm{syn}}(\sigma)|_K \le 16 |\sigma|_K$$
    on any backward-export-closed Tanner vertex subset $K$. -/
theorem two_hop_bipartite_component_contraction {Q M_Z M_X : Type}
    [Fintype Q] [DecidableEq Q] [Fintype M_Z] [DecidableEq M_Z] [Fintype M_X] [DecidableEq M_X]
    (pcode : CSSCode3D Q M_Z M_X) (M : ℕ)
    (hov : ∀ (x' : M_X) (z' : M_Z),
      (Finset.univ.filter (fun q' : Q => pcode.checkX x' q' ≠ 0 ∧ pcode.checkZ z' q' ≠ 0)).card ≤ 2)
    (hZ : ∀ q0 : Q, ∃ z0 : M_Z, pcode.checkZ z0 q0 ≠ 0)
    (h_conn : HasConnectedXLinks pcode)
    (K : Finset (BDLDecoder.TannerVertex Q M_Z M_X))
    (S : BDLStepXMZ pcode M → ZMod 2)
    (hS : ∃ h : BDLStepXQ pcode M → ZMod 2,
      syndrome (dualCode (bdlCylinderStepX pcode M)) h = S)
    (hK_Z_to_Q : ∀ z0 : M_Z, ∀ q0 : Q,
      BDLDecoder.inVZ z0 ∈ K → pcode.checkZ z0 q0 ≠ 0 →
      (∃ b : Fin 3, BDLDecoder.exportQZ pcode M
        (BDLDecoder.cleanStarQ pcode M (S + syndrome (dualCode (bdlCylinderStepX pcode M))
          (BDLDecoder.cleanStage1X pcode M S)) q0) (z0, b) ≠ 0) →
      BDLDecoder.inVQ q0 ∈ K)
    (hK_Q_to_X : ∀ q0 : Q, ∀ x : M_X,
      BDLDecoder.inVQ q0 ∈ K → pcode.checkX x q0 ≠ 0 →
      BDLDecoder.restrictCQ2 pcode M q0
        (syndrome (dualCode (bdlCylinderStepX pcode M)) (BDLDecoder.cleanCylinderX pcode M S x)) ≠ 0 →
      BDLDecoder.inVX x ∈ K) :
    27 * (BDLDecoder.activeCoarseZInK pcode M K S).card ≤
      16 * BDLDecoder.syndromeWeightNat (BDLDecoder.restrictStepXMZ pcode M K S) :=
  BDLDecoder.rxCleanedCoarseSyndrome_component_contraction pcode M hov hZ h_conn K S hS hK_Z_to_Q hK_Q_to_X

/-- **Two-Hop Bipartite Syndrome Contraction
    (`two_hop_bipartite_syndrome_contraction`, Part I, Theorem 4.3 (`thm:16-27-contraction`))**:
    For any subset $K_Z \subseteq M_Z$ of active coarse $Z$-checks in $\mathcal{R}_X^{\mathrm{syn}}(S)$,
    the deterministic two-hop Tanner neighborhood $\mathcal{P}_2(K_Z) = \mathrm{twoHopTannerOfZ}\;K_Z$
    satisfies $27 |K_Z| \le 16 |\sigma|_{\mathcal{P}_2(K_Z)}$. -/
theorem two_hop_bipartite_syndrome_contraction {Q M_Z M_X : Type}
    [Fintype Q] [DecidableEq Q] [Fintype M_Z] [DecidableEq M_Z] [Fintype M_X] [DecidableEq M_X]
    (pcode : CSSCode3D Q M_Z M_X) (M : ℕ)
    (hov : ∀ (x' : M_X) (z' : M_Z),
      (Finset.univ.filter (fun q' : Q => pcode.checkX x' q' ≠ 0 ∧ pcode.checkZ z' q' ≠ 0)).card ≤ 2)
    (hZ : ∀ q0 : Q, ∃ z0 : M_Z, pcode.checkZ z0 q0 ≠ 0)
    (h_conn : HasConnectedXLinks pcode)
    (K_Z : Finset M_Z)
    (S : BDLStepXMZ pcode M → ZMod 2)
    (hS : ∃ h : BDLStepXQ pcode M → ZMod 2,
      syndrome (dualCode (bdlCylinderStepX pcode M)) h = S)
    (hKZ_active : ∀ z0 ∈ K_Z, BDLDecoder.rxCleanedCoarseSyndrome pcode M S z0 ≠ 0) :
    27 * K_Z.card ≤
      16 * BDLDecoder.syndromeWeightNat
        (BDLDecoder.restrictStepXMZ pcode M (BDLDecoder.twoHopTannerOfZ pcode K_Z) S) :=
  BDLDecoder.rxCleanedCoarseSyndrome_twoHop_contraction pcode M hov hZ h_conn K_Z S hS hKZ_active

/-- **Fine Two-Hop Pool Active Check Lower Bound (`two_hop_bipartite_pool_contraction`, Part I, Theorem 4.3 (`thm:16-27-contraction`), Proposition 5.3 (`prop:cluster-decoder-witness`))**:
    Whenever every coarse check $z_0 \in K_Z$ is active in `rxCleanedCoarseSyndrome pcode M S`,
    at least $(27 |K_Z| + 15) / 16 = \lceil 27 |K_Z| / 16 \rceil$ fine checks in
    `fineTwoHopPool pcode M K_Z` are active in $S$. -/
theorem two_hop_bipartite_pool_contraction {Q M_Z M_X : Type}
    [Fintype Q] [DecidableEq Q] [Fintype M_Z] [DecidableEq M_Z] [Fintype M_X] [DecidableEq M_X]
    (pcode : CSSCode3D Q M_Z M_X) (M : ℕ)
    (hov : ∀ (x' : M_X) (z' : M_Z),
      (Finset.univ.filter (fun q' : Q => pcode.checkX x' q' ≠ 0 ∧ pcode.checkZ z' q' ≠ 0)).card ≤ 2)
    (hZ : ∀ q0 : Q, ∃ z0 : M_Z, pcode.checkZ z0 q0 ≠ 0)
    (h_conn : HasConnectedXLinks pcode)
    (K_Z : Finset M_Z)
    (S : BDLStepXMZ pcode M → ZMod 2)
    (hS : ∃ h : BDLStepXQ pcode M → ZMod 2,
      syndrome (dualCode (bdlCylinderStepX pcode M)) h = S)
    (hKZ_active : ∀ z0 ∈ K_Z, BDLDecoder.rxCleanedCoarseSyndrome pcode M S z0 ≠ 0) :
    (27 * K_Z.card + 15) / 16 ≤
      ((BDLDecoder.fineTwoHopPool pcode M K_Z).filter (fun mZ => S mZ ≠ 0)).card := by
  have h := BDLDecoder.rxCleanedCoarseSyndrome_twoHop_contraction pcode M hov hZ h_conn K_Z S hS hKZ_active
  rw [BDLDecoder.syndromeWeightNat_restrictStepXMZ_eq_card_filter_fineTwoHopPool] at h
  omega

/-- **Two-Hop Cluster Decomposition (`two_hop_cluster_disjoint_weight_add`, Part I, Lemma 5.4 (`lem:percolating-cluster-bounds`))**:
    For any two coarse $Z$-check subsets $K_1, K_2 \subseteq M_Z$ whose two-hop fine check pools
    `fineTwoHopPool pcode M K_1` and `fineTwoHopPool pcode M K_2` are disjoint, the active fine
    syndrome weight in their union decomposes additively across the two clusters. -/
theorem two_hop_cluster_disjoint_weight_add {Q M_Z M_X : Type}
    [Fintype Q] [DecidableEq Q] [Fintype M_Z] [DecidableEq M_Z] [Fintype M_X] [DecidableEq M_X]
    (pcode : CSSCode3D Q M_Z M_X) (M : ℕ)
    (K_1 K_2 : Finset M_Z)
    (h_disj : Disjoint (BDLDecoder.fineTwoHopPool pcode M K_1) (BDLDecoder.fineTwoHopPool pcode M K_2))
    (S : BDLStepXMZ pcode M → ZMod 2) :
    (((BDLDecoder.fineTwoHopPool pcode M K_1 ∪ BDLDecoder.fineTwoHopPool pcode M K_2).filter
      (fun mZ => S mZ ≠ 0)).card) =
    ((BDLDecoder.fineTwoHopPool pcode M K_1).filter (fun mZ => S mZ ≠ 0)).card +
    ((BDLDecoder.fineTwoHopPool pcode M K_2).filter (fun mZ => S mZ ≠ 0)).card := by
  rw [Finset.filter_union,
      Finset.card_union_of_disjoint (Finset.disjoint_filter_filter h_disj)]

namespace BDLDecoder

/-! ## 1. Indicator Syndromes and Pool-Based Witness Family Lifting -/

/-- Indicator syndrome `indSyndrome K : M → ZMod 2` of a check subset `K : Finset M`. -/
def indSyndrome {M : Type} [DecidableEq M] (K : Finset M) : M → ZMod 2 :=
  fun m => if m ∈ K then 1 else 0

/-- The integer syndrome weight of `indSyndrome K` equals `K.card`. -/
lemma syndromeWeightNat_indSyndrome {M : Type} [Fintype M] [DecidableEq M] (K : Finset M) :
    syndromeWeightNat (indSyndrome K) = K.card := by
  dsimp [syndromeWeightNat]
  have h_eq : Finset.univ.filter (fun m : M => indSyndrome K m ≠ 0) = K := by
    ext m
    by_cases hm : m ∈ K <;> simp [indSyndrome, hm]
  rw [h_eq]

/-- The real syndrome weight of `indSyndrome K` equals `(K.card : ℝ)`. -/
lemma syndromeWeight_indSyndrome {M : Type} [Fintype M] [DecidableEq M] (K : Finset M) :
    syndromeWeight (indSyndrome K) = (K.card : ℝ) := by
  rw [syndromeWeight_eq_natCast, syndromeWeightNat_indSyndrome]

/-- Abstract pool-based witness-family lifting over arbitrary finite types `M_0, M_1`. -/
lemma liftWitnessFamily_of_pool {M_0 M_1 : Type}
    [Fintype M_0] [DecidableEq M_0] [Fintype M_1] [DecidableEq M_1]
    (pool : Finset M_0 → Finset M_1) (B w_0 w_1 N_0 : ℕ)
    (h_pool : ∀ K_0 : Finset M_0, (pool K_0).card ≤ B * K_0.card)
    (W_0 : Finset (M_0 → ZMod 2))
    (h_card : W_0.card ≤ N_0)
    (h_wt : ∀ c0 ∈ W_0, (w_0 : ℝ) ≤ syndromeWeight c0) :
    ∃ W_1 : Finset (M_1 → ZMod 2),
      W_1.card ≤ N_0 * (2 ^ B) ^ w_0 ∧
      (∀ c1 ∈ W_1, (w_1 : ℝ) ≤ syndromeWeight c1) ∧
      (∀ (s1 : M_1 → ZMod 2) (c0 : M_0 → ZMod 2), c0 ∈ W_0 →
        w_1 ≤ ((pool (chooseSupp w_0 c0)).filter (fun m1 => s1 m1 ≠ 0)).card →
        ∃ c1 ∈ W_1, ∀ m1 : M_1, c1 m1 ≠ 0 → s1 m1 ≠ 0) := by
  classical
  let branch : (M_0 → ZMod 2) → Finset (M_1 → ZMod 2) := fun c0 =>
    ((pool (chooseSupp w_0 c0)).powersetCard w_1).image indSyndrome
  let W_1 : Finset (M_1 → ZMod 2) := W_0.biUnion branch
  refine ⟨W_1, ?_, ?_, ?_⟩
  · calc W_1.card
      _ ≤ ∑ c0 ∈ W_0, (branch c0).card := Finset.card_biUnion_le
      _ ≤ ∑ _c0 ∈ W_0, (2 ^ B) ^ w_0 := by
        refine Finset.sum_le_sum (fun c0 hc0 => ?_)
        have hw_real := h_wt c0 hc0
        dsimp [syndromeWeight] at hw_real
        have hw : w_0 ≤ (Finset.univ.filter (fun m0 => c0 m0 ≠ 0)).card := by
          exact_mod_cast hw_real
        have hK_card : (chooseSupp w_0 c0).card = w_0 := by
          dsimp [chooseSupp]; rw [dif_pos hw]
          exact (Classical.choose_spec (Finset.exists_subset_card_eq hw)).2
        have h_sub_pow : (pool (chooseSupp w_0 c0)).powersetCard w_1 ⊆
            (pool (chooseSupp w_0 c0)).powerset := by
          intro K hK
          exact Finset.mem_powerset.mpr (Finset.mem_powersetCard.mp hK).1
        have h_pool_le : (pool (chooseSupp w_0 c0)).card ≤ B * w_0 := by
          calc (pool (chooseSupp w_0 c0)).card
            _ ≤ B * (chooseSupp w_0 c0).card := h_pool (chooseSupp w_0 c0)
            _ = B * w_0 := by rw [hK_card]
        calc (branch c0).card
          _ ≤ ((pool (chooseSupp w_0 c0)).powersetCard w_1).card := Finset.card_image_le
          _ ≤ (pool (chooseSupp w_0 c0)).powerset.card := Finset.card_le_card h_sub_pow
          _ = 2 ^ (pool (chooseSupp w_0 c0)).card := Finset.card_powerset _
          _ ≤ 2 ^ (B * w_0) := Nat.pow_le_pow_right (by omega) h_pool_le
          _ = (2 ^ B) ^ w_0 := by rw [Nat.pow_mul]
      _ = W_0.card * (2 ^ B) ^ w_0 := by rw [Finset.sum_const, smul_eq_mul]
      _ ≤ N_0 * (2 ^ B) ^ w_0 := Nat.mul_le_mul_right _ h_card
  · intro c1 hc1
    rcases Finset.mem_biUnion.mp hc1 with ⟨c0, _, hc1_br⟩
    rcases Finset.mem_image.mp hc1_br with ⟨K1, hK1, rfl⟩
    rw [syndromeWeight_indSyndrome, (Finset.mem_powersetCard.mp hK1).2]
  · intro s1 c0 hc0 hw1_le
    obtain ⟨K1, hK1_sub, hK1_card⟩ := Finset.exists_subset_card_eq hw1_le
    have hK1_pool : K1 ⊆ pool (chooseSupp w_0 c0) :=
      hK1_sub.trans (Finset.filter_subset _ _)
    refine ⟨indSyndrome K1, ?_, ?_⟩
    · exact Finset.mem_biUnion.mpr ⟨c0, hc0,
        Finset.mem_image.mpr ⟨K1, Finset.mem_powersetCard.mpr ⟨hK1_pool, hK1_card⟩, rfl⟩⟩
    · intro m1 hm1
      dsimp [indSyndrome] at hm1
      split_ifs at hm1 with hmK1
      · exact (Finset.mem_filter.mp (hK1_sub hmK1)).2
      · exact False.elim (hm1 rfl)

/-- Single-step dual $\mathcal{R}_X^{(3)}$ witness-family lifting via `fineTwoHopPool` and `powersetCard`. -/
theorem liftWitnessFamily_rx_twoHop_step {Q M_Z M_X : Type}
    [Fintype Q] [DecidableEq Q] [Fintype M_Z] [DecidableEq M_Z] [Fintype M_X] [DecidableEq M_X]
    (pcode : CSSCode3D Q M_Z M_X) (M F w_0 N_0 : ℕ)
    (hov : ∀ (x' : M_X) (z' : M_Z),
      (Finset.univ.filter (fun q' : Q => pcode.checkX x' q' ≠ 0 ∧ pcode.checkZ z' q' ≠ 0)).card ≤ 2)
    (hZ : ∀ q0 : Q, ∃ z0 : M_Z, pcode.checkZ z0 q0 ≠ 0)
    (h_conn : HasConnectedXLinks pcode)
    (h_pool : ∀ K_Z : Finset M_Z, (fineTwoHopPool pcode M K_Z).card ≤ 41 * F * K_Z.card)
    (W_0 : Finset (M_Z → ZMod 2))
    (h_card : W_0.card ≤ N_0)
    (h_wt : ∀ c0 ∈ W_0, (w_0 : ℝ) ≤ syndromeWeight c0) :
    let w_1 := (27 * w_0 + 15) / 16
    ∃ W_1 : Finset (BDLStepXMZ pcode M → ZMod 2),
      W_1.card ≤ N_0 * (2 ^ (41 * F)) ^ w_0 ∧
      (∀ c1 ∈ W_1, (w_1 : ℝ) ≤ syndromeWeight c1) ∧
      (∀ (h : BDLStepXQ pcode M → ZMod 2) (c0 : M_Z → ZMod 2), c0 ∈ W_0 →
        (∀ z0 : M_Z, c0 z0 ≠ 0 →
          rxCleanedCoarseSyndrome pcode M (syndrome (dualCode (bdlCylinderStepX pcode M)) h) z0 ≠ 0) →
        ∃ c1 ∈ W_1, ∀ mZ : BDLStepXMZ pcode M, c1 mZ ≠ 0 →
          syndrome (dualCode (bdlCylinderStepX pcode M)) h mZ ≠ 0) := by
  intro w_1
  obtain ⟨W_1, hW1_card, hW1_wt, hW1_lift⟩ :=
    liftWitnessFamily_of_pool (fineTwoHopPool pcode M) (41 * F) w_0 w_1 N_0 h_pool W_0 h_card h_wt
  refine ⟨W_1, hW1_card, hW1_wt, ?_⟩
  intro h c0 hc0 h_act
  let S := syndrome (dualCode (bdlCylinderStepX pcode M)) h
  have hw_real := h_wt c0 hc0
  dsimp [syndromeWeight] at hw_real
  have hw : w_0 ≤ (Finset.univ.filter (fun z0 => c0 z0 ≠ 0)).card := by
    exact_mod_cast hw_real
  let K_Z := chooseSupp w_0 c0
  have hK_spec : K_Z ⊆ Finset.univ.filter (fun z0 => c0 z0 ≠ 0) ∧ K_Z.card = w_0 := by
    dsimp [K_Z, chooseSupp]; rw [dif_pos hw]
    exact Classical.choose_spec (Finset.exists_subset_card_eq hw)
  have hKZ_act : ∀ z0 ∈ K_Z, rxCleanedCoarseSyndrome pcode M S z0 ≠ 0 := by
    intro z0 hz0
    exact h_act z0 (Finset.mem_filter.mp (hK_spec.1 hz0)).2
  have h_contr := rxCleanedCoarseSyndrome_twoHop_contraction pcode M hov hZ h_conn K_Z S ⟨h, rfl⟩ hKZ_act
  rw [syndromeWeightNat_restrictStepXMZ_eq_card_filter_fineTwoHopPool, hK_spec.2] at h_contr
  apply hW1_lift S c0 hc0
  dsimp [w_1, K_Z] at h_contr ⊢
  omega

/-! ## 2. Zero-Preservation and Discrepancy of Coarse Parity Rules -/

/-- Stage-1 cylinder cleaner `cleanStage1X` maps the zero error chain to zero. -/
lemma cleanStage1X_zero {Q M_Z M_X : Type}
    [Fintype Q] [DecidableEq Q] [Fintype M_Z] [DecidableEq M_Z] [Fintype M_X] [DecidableEq M_X]
    (pcode : CSSCode3D Q M_Z M_X) (M : ℕ) :
    cleanStage1X pcode M 0 = 0 := by
  dsimp [cleanStage1X]
  apply Finset.sum_eq_zero
  intro x _
  apply cleanCylinderX_eq_zero_of_restrictCX2_eq_zero
  ext mZ; dsimp [restrictCX2, restrictStepXMZ]; exact ite_self _

/-- Stage-2 star cleaner `cleanStage2Q` maps the zero error chain to zero. -/
lemma cleanStage2Q_zero {Q M_Z M_X : Type}
    [Fintype Q] [DecidableEq Q] [Fintype M_Z] [DecidableEq M_Z] [Fintype M_X] [DecidableEq M_X]
    (pcode : CSSCode3D Q M_Z M_X) (M : ℕ) :
    cleanStage2Q pcode M 0 = 0 := by
  dsimp [cleanStage2Q]
  apply Finset.sum_eq_zero
  intro q0 _
  apply cleanStarQ_eq_zero_of_restrictCQ2_eq_zero
  ext mZ; dsimp [restrictCQ2, restrictStepXMZ]; exact ite_self _

/-- Two-stage cleaner `cleanTwoStageRX` maps the zero error chain to zero. -/
lemma cleanTwoStageRX_zero {Q M_Z M_X : Type}
    [Fintype Q] [DecidableEq Q] [Fintype M_Z] [DecidableEq M_Z] [Fintype M_X] [DecidableEq M_X]
    (pcode : CSSCode3D Q M_Z M_X) (M : ℕ) :
    cleanTwoStageRX pcode M 0 = 0 := by
  dsimp [cleanTwoStageRX]
  rw [cleanStage1X_zero, map_zero, add_zero, cleanStage2Q_zero, add_zero]

/-- `rxCleanedCoarseSyndrome` maps the zero fine syndrome to the zero coarse syndrome. -/
lemma rxCleanedCoarseSyndrome_zero {Q M_Z M_X : Type}
    [Fintype Q] [DecidableEq Q] [Fintype M_Z] [DecidableEq M_Z] [Fintype M_X] [DecidableEq M_X]
    (pcode : CSSCode3D Q M_Z M_X) (M : ℕ) :
    rxCleanedCoarseSyndrome pcode M 0 = 0 := by
  ext z0
  dsimp [rxCleanedCoarseSyndrome]
  rw [cleanTwoStageRX_zero, map_zero]
  rfl

/-- Dual $\mathcal{R}_X^{(3)}$ cluster parity rule (`rxCleanedParityRule`). -/
noncomputable def rxCleanedParityRule {Q M_Z M_X : Type}
    [Fintype Q] [DecidableEq Q] [Fintype M_Z] [DecidableEq M_Z] [Fintype M_X] [DecidableEq M_X]
    (pcode : CSSCode3D Q M_Z M_X) (M : ℕ)
    (ψ_0 : (M_Z → ZMod 2) → ZMod 2) (L_Z : Q → ZMod 2)
    (S : BDLStepXMZ pcode M → ZMod 2) : ZMod 2 :=
  ψ_0 (rxCleanedCoarseSyndrome pcode M S) +
    dualPairing (liftCylinderLZ pcode M L_Z) (cleanTwoStageRX pcode M S)

/-- `rxCleanedParityRule` evaluates to `false` on the zero syndrome. -/
lemma rxCleanedParityRule_zero {Q M_Z M_X : Type}
    [Fintype Q] [DecidableEq Q] [Fintype M_Z] [DecidableEq M_Z] [Fintype M_X] [DecidableEq M_X]
    (pcode : CSSCode3D Q M_Z M_X) (M : ℕ)
    (ψ_0 : (M_Z → ZMod 2) → ZMod 2) (hψ0 : ψ_0 0 = 0) (L_Z : Q → ZMod 2) :
    rxCleanedParityRule pcode M ψ_0 L_Z 0 = 0 := by
  have hp0 : dualPairing (liftCylinderLZ pcode M L_Z) 0 = 0 := by
    dsimp [dualPairing]; simp
  dsimp [rxCleanedParityRule]
  rw [rxCleanedCoarseSyndrome_zero, hψ0, cleanTwoStageRX_zero, hp0, add_zero]

/-- **Exact Dual Step Discrepancy Invariance (`rxCleanedParityRule_discrepancy_eq`, Part I, Proposition 5.3 (`prop:cluster-decoder-witness`)):**
    For every fine 1-cochain `h : BDLStepXQ pcode M → ZMod 2`, the fine logical discrepancy of
    `rxCleanedParityRule` equals the coarse logical discrepancy evaluated on the 2-stage cleaned
    coarse projection `rxCleanedCoarseProj pcode M h`. -/
theorem rxCleanedParityRule_discrepancy_eq {Q M_Z M_X : Type}
    [Fintype Q] [DecidableEq Q] [Fintype M_Z] [DecidableEq M_Z] [Fintype M_X] [DecidableEq M_X]
    (pcode : CSSCode3D Q M_Z M_X) (M : ℕ)
    (hov : ∀ (x' : M_X) (z' : M_Z),
      (Finset.univ.filter (fun q' : Q => pcode.checkX x' q' ≠ 0 ∧ pcode.checkZ z' q' ≠ 0)).card ≤ 2)
    (hq_z : ∀ q, ∃ z, pcode.checkZ z q ≠ 0)
    (h_conn : HasConnectedXLinks pcode)
    (ψ_0 : (M_Z → ZMod 2) → ZMod 2) (L_Z : Q → ZMod 2)
    (h : BDLStepXQ pcode M → ZMod 2) :
    let D_1 := dualCode (bdlCylinderStepX pcode M)
    let h_coarse := rxCleanedCoarseProj pcode M h
    rxCleanedParityRule pcode M ψ_0 L_Z (syndrome D_1 h) +
      dualPairing (liftCylinderLZ pcode M L_Z) h =
    ψ_0 (syndrome (dualCode pcode) h_coarse) + dualPairing L_Z h_coarse := by
  intro D_1 h_coarse
  have h_syn := (rxCleanedCoarseProj_syndrome_eq pcode M hov hq_z h_conn h).1
  have h_proj_eq : h_coarse =
      projCylinderLX pcode M (h + cleanTwoStageRX pcode M (syndrome D_1 h)) := by
    dsimp [h_coarse, rxCleanedCoarseProj]
    exact projCylinderLXLayer_zero_eq pcode M _
  have h_pair : dualPairing (liftCylinderLZ pcode M L_Z) (cleanTwoStageRX pcode M (syndrome D_1 h)) +
      dualPairing (liftCylinderLZ pcode M L_Z) h =
      dualPairing L_Z h_coarse := by
    rw [add_comm, ← dualPairing_add_right_zmod2, dualPairing_liftCylinderLZ_left, ← h_proj_eq]
  dsimp [rxCleanedParityRule]
  rw [add_assoc, h_pair, ← h_syn]

/-- Primal $\mathcal{R}_Z^{(3)}$ coarse parity rule (`rzCoarseParityRule`). -/
noncomputable def rzCoarseParityRule {Q M_Z M_X : Type}
    [Fintype Q] [DecidableEq Q] [Fintype M_Z] [DecidableEq M_Z] [Fintype M_X] [DecidableEq M_X]
    (pcode : CSSCode3D Q M_Z M_X) (M : ℕ)
    (ψ_0 : (M_X → ZMod 2) → ZMod 2)
    (S : BDLStepXMX pcode M → ZMod 2) : ZMod 2 :=
  ψ_0 (coarseSyndromeStepXMX pcode M S)

/-- `rzCoarseParityRule` evaluates to `false` on the zero syndrome. -/
lemma rzCoarseParityRule_zero {Q M_Z M_X : Type}
    [Fintype Q] [DecidableEq Q] [Fintype M_Z] [DecidableEq M_Z] [Fintype M_X] [DecidableEq M_X]
    (pcode : CSSCode3D Q M_Z M_X) (M : ℕ)
    (ψ_0 : (M_X → ZMod 2) → ZMod 2) (hψ0 : ψ_0 0 = 0) :
    rzCoarseParityRule pcode M ψ_0 0 = 0 := by
  dsimp [rzCoarseParityRule]
  have h0 : coarseSyndromeStepXMX pcode M 0 = 0 := by
    ext x0; dsimp [coarseSyndromeStepXMX]; simp
  rw [h0, hψ0]

/-- **Exact Primal Step Discrepancy Invariance (`rzCoarseParityRule_discrepancy_eq`, Part I, Proposition 5.3 (`prop:cluster-decoder-witness`)):**
    For every fine 1-chain `e : BDLStepXQ pcode M → ZMod 2`, the fine logical discrepancy of
    `rzCoarseParityRule` equals the coarse logical discrepancy evaluated on `projCylinderLZ pcode M e`. -/
theorem rzCoarseParityRule_discrepancy_eq {Q M_Z M_X : Type}
    [Fintype Q] [DecidableEq Q] [Fintype M_Z] [DecidableEq M_Z] [Fintype M_X] [DecidableEq M_X]
    (pcode : CSSCode3D Q M_Z M_X) (M : ℕ)
    (ψ_0 : (M_X → ZMod 2) → ZMod 2) (L_X : Q → ZMod 2)
    (e : BDLStepXQ pcode M → ZMod 2) :
    let C_1 := bdlCylinderStepX pcode M
    let e_coarse := projCylinderLZ pcode M e
    rzCoarseParityRule pcode M ψ_0 (syndrome C_1 e) +
      dualPairing (liftCylinderLX pcode M L_X) e =
    ψ_0 (syndrome pcode e_coarse) + dualPairing L_X e_coarse := by
  intro C_1 e_coarse
  dsimp [rzCoarseParityRule]
  rw [coarseSyndromeStepXMX_syndrome_eq pcode M e,
      dualPairing_comm (liftCylinderLX pcode M L_X) e,
      dualPairing_liftCylinderLX_right pcode M e L_X,
      dualPairing_comm e_coarse L_X]

end BDLDecoder
end WeldedHierarchy
