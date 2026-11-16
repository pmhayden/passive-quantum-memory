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

import Defs.BDLSubstitutionCode
import Proofs.Step1LLLDensity.SphericalCapAndLLL

/-!
# Open-Box Cubic Grid Realization, Fiber Bounds, and Local CSS Descriptor Validity

Establishes inductive 3D coordinate bounds `HasBounded3DCoords` for `bdlWeldedBundled k` (`hasBounded3DCoords_bdlWeldedBundled`), open-cubic-grid snapping properties (`snapPointToOpenBox_bounds`), and uniform per-site fiber cardinality bounds (`bdlFiber_card_bounds`). Proves injectivity of the site-slot placement map (`bdlQubitSiteSlot_injective`) and global open-box validity `ValidDescriptorField (bdlLocalDescriptor k)` (`bdlLocalDescriptor_validDescriptorField_proof`).

## References

* Part I, Section 2.3 (`subsec:step2-mapping-cone`), Proposition 2.6 (`prop:mapping-cone-invariants`)
* Part I, Section 5.4 (`subsec:safe-decoded-observables`), Definition 5.6 (`def:safe-decoded-observables`)
* Part I, Section 6.1 (`subsec:dsuper-banach`), Equation (60) (`eq:open-cubic-grid`)
-/

noncomputable section

open scoped Classical BigOperators

/-! ## 1. Coordinate Bounds & Open-Box Snapping (Part I, Section 5.4 (`subsec:safe-decoded-observables`), Definition 5.6 (`def:safe-decoded-observables`) and Section 6.1 (`subsec:dsuper-banach`), Equation (60) (`eq:open-cubic-grid`)) -/

/-- Recursive coordinate bound `bdlCoordBound n` after `n` composite `(bdlStepZ ∘ bdlStepX)` steps. -/
def bdlCoordBound : ℕ → ℝ
  | 0 => 2
  | n + 1 => (bdlLambda : ℝ) * ((bdlLambda : ℝ) * (bdlCoordBound n + 1000) + 1000)

/-- Non-negativity of `bdlCoordBound n` for all $n \in \mathbb{N}$. -/
lemma bdlCoordBound_nonneg (n : ℕ) : 0 ≤ bdlCoordBound n := by
  induction n with
  | zero => dsimp [bdlCoordBound]; norm_num
  | succ n ih => dsimp [bdlCoordBound]; positivity

/-- Coordinate bound invariant `|pos axis| ≤ M` across all qubits and checks of `B`. -/
def HasBounded3DCoords (B : BundledCSSCode3D) (M : ℝ) : Prop :=
  (∀ q axis, |B.code.posQ q axis| ≤ M) ∧
  (∀ mZ axis, |B.code.posZ mZ axis| ≤ M) ∧
  (∀ mX axis, |B.code.posX mX axis| ≤ M)

/-- Convexity of $[-M, M]^3$ under linear subdivision `subdividePoint3D`. -/
lemma abs_subdividePoint3D_le (p q : Point3D) (L j : ℕ) (M : ℝ) (_ : 0 ≤ M)
    (hj : j ≤ L) (hp : ∀ axis, |p axis| ≤ M) (hq : ∀ axis, |q axis| ≤ M) (axis : Fin 3) :
    |subdividePoint3D p q L j axis| ≤ M := by
  dsimp [subdividePoint3D]
  by_cases hL : L = 0
  · subst hL; simp [hp axis]
  · have hL_pos : (0 : ℝ) < (L : ℝ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hL)
    have ht0 : 0 ≤ (j : ℝ) / (L : ℝ) := div_nonneg (Nat.cast_nonneg j) (le_of_lt hL_pos)
    have ht1 : (j : ℝ) / (L : ℝ) ≤ 1 := (div_le_one hL_pos).mpr (Nat.cast_le.mpr hj)
    have h_ident : p axis + ((j : ℝ) / (L : ℝ)) * (q axis - p axis) =
        (1 - (j : ℝ) / (L : ℝ)) * p axis + ((j : ℝ) / (L : ℝ)) * q axis := by ring
    rw [h_ident]
    have h_1mt : 0 ≤ 1 - (j : ℝ) / (L : ℝ) := by linarith
    have h1 := abs_add_le ((1 - (j : ℝ) / (L : ℝ)) * p axis) (((j : ℝ) / (L : ℝ)) * q axis)
    rw [abs_mul, abs_mul, abs_of_nonneg h_1mt, abs_of_nonneg ht0] at h1
    have hp_ax := hp axis
    have hq_ax := hq axis
    calc |(1 - (j : ℝ) / (L : ℝ)) * p axis + ((j : ℝ) / (L : ℝ)) * q axis|
      _ ≤ (1 - (j : ℝ) / (L : ℝ)) * |p axis| + (j : ℝ) / (L : ℝ) * |q axis| := h1
      _ ≤ (1 - (j : ℝ) / (L : ℝ)) * M + (j : ℝ) / (L : ℝ) * M := by nlinarith
      _ = M := by ring

/-- Expresses `triGridPos3D` as a nested convex combination of `subdividePoint3D`. -/
lemma triGridPos3D_eq_subdividePoint3D (pX pQ pZ : Point3D) (m u v : ℕ)
    (hu : 0 < u) (hvu : v ≤ u) :
    triGridPos3D pX pQ pZ m u v =
      subdividePoint3D pX (subdividePoint3D pQ pZ u v) m u := by
  ext axis
  dsimp [triGridPos3D, subdividePoint3D]
  have h_sub : ((u - v : ℕ) : ℝ) = (u : ℝ) - (v : ℝ) := Nat.cast_sub hvu
  rw [h_sub]
  have hu_ne : (u : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (ne_of_gt hu)
  by_cases hm : m = 0
  · subst hm; simp
  · have hm_ne : (m : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hm
    field_simp [hu_ne, hm_ne]
    ring

lemma abs_triGridPos3D_le (pX pQ pZ : Point3D) (m u v : ℕ) (B : ℝ)
    (hB : 0 ≤ B) (hu : 0 < u) (hvu : v ≤ u) (hum : u ≤ m)
    (hpX : ∀ axis, |pX axis| ≤ B) (hpQ : ∀ axis, |pQ axis| ≤ B)
    (hpZ : ∀ axis, |pZ axis| ≤ B) (axis : Fin 3) :
    |triGridPos3D pX pQ pZ m u v axis| ≤ B := by
  rw [triGridPos3D_eq_subdividePoint3D pX pQ pZ m u v hu hvu]
  exact abs_subdividePoint3D_le pX (subdividePoint3D pQ pZ u v) m u B hB hum hpX
    (fun ax => abs_subdividePoint3D_le pQ pZ u v B hB hvu hpQ hpZ ax) axis

/-- `bdlStepX` maps a code with coordinates in $[-M, M]^3$ to one in $[-\Lambda(M + 1000), \Lambda(M + 1000)]^3$. -/
lemma bdlStepX_preserves_bounded_coords (B : BundledCSSCode3D) (M : ℝ) (hM : 0 ≤ M)
    (h : HasBounded3DCoords B M) :
    HasBounded3DCoords (bdlStepX B) ((bdlLambda : ℝ) * (M + 1000)) := by
  have h_lll := WeldedHierarchy.bdlLLLPerturbation_abs_le B
  have h_lam_nonneg : (0 : ℝ) ≤ (bdlLambda : ℝ) := by dsimp [bdlLambda]; positivity
  have hM'_nonneg : 0 ≤ (bdlLambda : ℝ) * (M + 1000) := by positivity
  let pcode := bdlPerturbStep B.code bdlLambda (bdlLLLPerturbation B).1 (bdlLLLPerturbation B).2.1 (bdlLLLPerturbation B).2.2
  have hpQ : ∀ q axis, |pcode.posQ q axis| ≤ (bdlLambda : ℝ) * (M + 1000) := by
    intro q axis; dsimp [pcode, bdlPerturbStep]
    have h1 := abs_add_le ((bdlLambda : ℝ) * B.code.posQ q axis) ((bdlLLLPerturbation B).1 q axis)
    rw [abs_mul, abs_of_nonneg h_lam_nonneg] at h1
    have hq := h.1 q axis; have hc := h_lll.1 q axis; nlinarith
  have hpZ : ∀ mZ axis, |pcode.posZ mZ axis| ≤ (bdlLambda : ℝ) * (M + 1000) := by
    intro mZ axis; dsimp [pcode, bdlPerturbStep]
    have h1 := abs_add_le ((bdlLambda : ℝ) * B.code.posZ mZ axis) ((bdlLLLPerturbation B).2.1 mZ axis)
    rw [abs_mul, abs_of_nonneg h_lam_nonneg] at h1
    have hmZ := h.2.1 mZ axis; have hc := h_lll.2.1 mZ axis; nlinarith
  have hpX : ∀ mX axis, |pcode.posX mX axis| ≤ (bdlLambda : ℝ) * (M + 1000) := by
    intro mX axis; dsimp [pcode, bdlPerturbStep]
    have h1 := abs_add_le ((bdlLambda : ℝ) * B.code.posX mX axis) ((bdlLLLPerturbation B).2.2 mX axis)
    rw [abs_mul, abs_of_nonneg h_lam_nonneg] at h1
    have hmX := h.2.2 mX axis; have hc := h_lll.2.2 mX axis; nlinarith
  have h_bxPos : ∀ (v : BoundaryX0 pcode bdlSubdivPred) axis,
      |boundaryX0Pos pcode bdlSubdivPred v axis| ≤ (bdlLambda : ℝ) * (M + 1000) := by
    intro v axis; rcases v with q | ⟨⟨eZ, j⟩ | z⟩
    · exact hpQ q axis
    · exact abs_subdividePoint3D_le _ _ (bdlSubdivPred + 1) (j.val + 1) _ hM'_nonneg
        (by omega) (hpQ eZ.val.1) (hpZ eZ.val.2) axis
    · exact hpZ z axis
  have h_xqPos : ∀ (v0 : Xq0 pcode bdlSubdivPred) axis,
      |xq0Pos pcode bdlSubdivPred v0 axis| ≤ (bdlLambda : ℝ) * (M + 1000) :=
    fun v0 axis => h_bxPos (projXq0ToBoundaryX0 pcode bdlSubdivPred v0) axis
  have h_svPos : ∀ (sv : ShellVertex pcode bdlSubdivPred) axis,
      |shellVertexPos pcode bdlSubdivPred sv axis| ≤ (bdlLambda : ℝ) * (M + 1000) := by
    intro ⟨⟨⟨⟨x, v⟩, _⟩, r⟩, h_in⟩ axis
    rcases v with q | ⟨⟨eZ, j⟩ | z⟩
    · dsimp [shellVertexPos]
      exact abs_subdividePoint3D_le _ _ (bdlSubdivPred + 1) (r.val + 1) _ hM'_nonneg
        (Nat.succ_le_of_lt r.isLt) (hpX x) (hpQ q) axis
    · dsimp [shellVertexPos]; dsimp [InShellR] at h_in
      exact abs_triGridPos3D_le _ _ _ (bdlSubdivPred + 1) (r.val + 1) (j.val + 1) _ hM'_nonneg
        (Nat.succ_pos r.val) (by omega) (Nat.succ_le_of_lt r.isLt)
        (hpX x) (hpQ eZ.val.1) (hpZ eZ.val.2) axis
    · dsimp [shellVertexPos]
      exact abs_subdividePoint3D_le _ _ (bdlSubdivPred + 1) (r.val + 1) _ hM'_nonneg
        (Nat.succ_le_of_lt r.isLt) (hpX x) (hpZ z) axis
  refine ⟨?_, ?_, ?_⟩
  · intro q axis; dsimp [bdlStepX, bdlReplaceStepX, bdlCylinderStepX, bdlStepXPosQ]
    rcases q with ⟨⟨sv, _⟩ | ⟨⟨seg, _⟩ | ⟨xv, _⟩⟩⟩ | ⟨v0, _⟩
    · exact h_svPos sv axis
    · exact h_svPos (shellSegEndVertex pcode bdlSubdivPred seg) axis
    · exact h_bxPos xv.val.2 axis
    · exact h_xqPos v0 axis
  · intro mZ axis; dsimp [bdlStepX, bdlReplaceStepX, bdlCylinderStepX, bdlStepXPosZ]
    rcases mZ with ⟨⟨seg, _⟩ | ⟨s, k, _⟩⟩ | ⟨⟨⟨eZ, k, _⟩ | ⟨eZ, _⟩⟩ | ⟨z, _⟩⟩
    · exact h_svPos (shellSegEndVertex pcode bdlSubdivPred seg) axis
    · exact h_bxPos (bxEnd pcode bdlSubdivPred s.val.2 k) axis
    · exact h_xqPos (armEnd pcode bdlSubdivPred eZ k) axis
    · exact hpZ eZ.val.2 axis
    · exact hpZ z axis
  · intro mX axis; dsimp [bdlStepX, bdlReplaceStepX, bdlCylinderStepX, bdlStepXPosX]
    rcases mX with ⟨x, _⟩ | ⟨sv, _⟩
    · exact hpX x axis
    · exact h_svPos sv axis

lemma dualBundled_preserves_bounded_coords (B : BundledCSSCode3D) (M : ℝ)
    (h : HasBounded3DCoords B M) : HasBounded3DCoords (dualBundled B) M :=
  ⟨h.1, h.2.2, h.2.1⟩

lemma bdlStepZX_preserves_bounded_coords (B : BundledCSSCode3D) (M : ℝ) (hM : 0 ≤ M)
    (h : HasBounded3DCoords B M) :
    HasBounded3DCoords ((bdlStepZ ∘ bdlStepX) B)
      ((bdlLambda : ℝ) * ((bdlLambda : ℝ) * (M + 1000) + 1000)) := by
  have h1 := bdlStepX_preserves_bounded_coords B M hM h
  have hM1 : 0 ≤ (bdlLambda : ℝ) * (M + 1000) := by positivity
  exact dualBundled_preserves_bounded_coords _ _
    (bdlStepX_preserves_bounded_coords _ ((bdlLambda : ℝ) * (M + 1000)) hM1
      (dualBundled_preserves_bounded_coords _ _ h1))

lemma hasBounded3DCoords_bdlIterated (k : ℕ) :
    ∀ (B : BundledCSSCode3D) (n : ℕ),
      HasBounded3DCoords B (bdlCoordBound n) →
      HasBounded3DCoords ((bdlStepZ ∘ bdlStepX)^[k] B) (bdlCoordBound (n + k)) := by
  induction k with
  | zero => intro B n h; simpa using h
  | succ k ih =>
    intro B n h
    have h_step : HasBounded3DCoords ((bdlStepZ ∘ bdlStepX) B) (bdlCoordBound (n + 1)) := by
      dsimp [bdlCoordBound]
      exact bdlStepZX_preserves_bounded_coords B (bdlCoordBound n) (bdlCoordBound_nonneg n) h
    have h_ih := ih ((bdlStepZ ∘ bdlStepX) B) (n + 1) h_step
    rwa [show n + 1 + k = n + (k + 1) by omega] at h_ih

lemma hasBounded3DCoords_surfaceSeed : HasBounded3DCoords bdlSurfaceSeedBundled (bdlCoordBound 0) := by
  refine ⟨?_, ?_, ?_⟩
  · intro q axis; fin_cases q <;> fin_cases axis <;>
      dsimp [bdlSurfaceSeedBundled, bdlSurfaceSeedCode, surfacePosQ, bdlCoordBound] <;> norm_num
  · intro mZ axis; fin_cases mZ <;> fin_cases axis <;>
      dsimp [bdlSurfaceSeedBundled, bdlSurfaceSeedCode, surfacePosZ, bdlCoordBound] <;> norm_num
  · intro mX axis; fin_cases mX <;> fin_cases axis <;>
      dsimp [bdlSurfaceSeedBundled, bdlSurfaceSeedCode, surfacePosX, bdlCoordBound] <;> norm_num

/-- All physical qubits and checks of `bdlWeldedBundled k` have 3D coordinates in
    `[-bdlCoordBound (k + 1), bdlCoordBound (k + 1)]^3`. -/
theorem hasBounded3DCoords_bdlWeldedBundled (k : ℕ) :
    HasBounded3DCoords (bdlWeldedBundled k) (bdlCoordBound (k + 1)) := by
  have h := hasBounded3DCoords_bdlIterated (k + 1) bdlSurfaceSeedBundled 0 hasBounded3DCoords_surfaceSeed
  rwa [Nat.zero_add] at h

lemma bdlCoordBound_succ_add_2000_le (n : ℕ) :
    bdlCoordBound (n + 1) + 2000 ≤ ((bBDL : ℝ) ^ 2) ^ (n + 2) / 2 := by
  induction n with
  | zero =>
    dsimp [bdlCoordBound, bBDL, bdlLambda]; norm_num
  | succ n ih =>
    change (bdlLambda : ℝ) * ((bdlLambda : ℝ) * (bdlCoordBound (n + 1) + 1000) + 1000) + 2000 ≤
      ((bBDL : ℝ) ^ 2) ^ (n + 2 + 1) / 2
    rw [pow_succ']
    dsimp [bBDL, bdlLambda] at ih ⊢
    norm_num at ih ⊢; linarith

lemma bdlCoordBound_add_1000_le_half_L (k : ℕ) :
    bdlCoordBound (k + 1) + 1000 ≤ (bdlBoxSide k : ℝ) / 2 := by
  have h1 := bdlCoordBound_succ_add_2000_le k
  have h_nat : bdlBoxSide k = (bBDL ^ 2) ^ (k + 2) := by
    dsimp [bdlBoxSide, bdlHierarchySteps]
    rw [← Nat.pow_mul, show 2 * (k + 2) = 2 * k + 4 by omega]
  have h_L : (bdlBoxSide k : ℝ) = ((bBDL : ℝ) ^ 2) ^ (k + 2) := by exact_mod_cast h_nat
  linarith

/-- Interior coordinate bounds and floor inequalities for `snapPointToOpenBox L p`. -/
lemma snapPointToOpenBox_bounds {L : ℕ} [NeZero L] {M : ℝ} (hL : M + 1000 ≤ (L : ℝ) / 2)
    {p : Point3D} (hp : ∀ μ, |p μ| ≤ M) (μ : Fin 3) :
    (1000 ≤ ((snapPointToOpenBox L p μ).val : ℤ) ∧ ((snapPointToOpenBox L p μ).val : ℤ) ≤ (L : ℤ) - 1000) ∧
    (((snapPointToOpenBox L p μ).val : ℝ) ≤ p μ + (L : ℝ) / 2 ∧
     p μ + (L : ℝ) / 2 < ((snapPointToOpenBox L p μ).val : ℝ) + 1) := by
  have h_abs := abs_le.mp (hp μ)
  have h_lo : (1000 : ℝ) ≤ p μ + (L : ℝ) / 2 := by linarith
  have h_hi : p μ + (L : ℝ) / 2 ≤ (L : ℝ) - 1000 := by linarith
  let m := ⌊p μ + (L : ℝ) / 2⌋
  have hm_lo : (1000 : ℤ) ≤ m := Int.le_floor.mpr (by exact_mod_cast h_lo)
  have hm_hi : m ≤ (L : ℤ) - 1000 := by
    have := Int.floor_le (p μ + (L : ℝ) / 2)
    exact_mod_cast (by push_cast; linarith : (m : ℝ) ≤ ((L : ℤ) - 1000 : ℤ))
  have hm_lt : m.toNat < L := by omega
  have hv_val : (snapPointToOpenBox L p μ).val = m.toNat := by
    dsimp [snapPointToOpenBox]; rw [dif_pos hm_lt]
  have hv_int : ((snapPointToOpenBox L p μ).val : ℤ) = m := by rw [hv_val]; omega
  refine ⟨⟨by omega, by omega⟩, ⟨?_, ?_⟩⟩
  · have h_eq : (((snapPointToOpenBox L p μ).val : ℤ) : ℝ) = (m : ℝ) := by exact_mod_cast hv_int
    exact_mod_cast h_eq.trans_le (Int.floor_le (p μ + (L : ℝ) / 2))
  · have h_eq : (((snapPointToOpenBox L p μ).val : ℤ) : ℝ) + 1 = (m : ℝ) + 1 := by
      exact_mod_cast congr_arg (· + 1) hv_int
    exact_mod_cast (Int.lt_floor_add_one (p μ + (L : ℝ) / 2)).trans_le h_eq.symm.le

/-- Every offset `nb : LocalNeighborhoodIdx r_0_BDL` around a snapped point with $|p_\mu| \le M$
    satisfies `InOpenBox (snapPointToOpenBox L p) (neighborhoodOffset r_0_BDL nb)`. -/
lemma snapPointToOpenBox_inOpenBox_neighborhoodOffset {L : ℕ} [NeZero L] {M : ℝ}
    (hL : M + 1000 ≤ (L : ℝ) / 2) {p : Point3D} (hp : ∀ μ, |p μ| ≤ M)
    (nb : LocalNeighborhoodIdx r0BDL) :
    InOpenBox (snapPointToOpenBox L p) (neighborhoodOffset r0BDL nb) := by
  intro μ
  have hb := (snapPointToOpenBox_bounds hL hp μ).1
  have hnb := (nb μ).isLt
  dsimp [neighborhoodOffset, r0BDL] at hnb ⊢
  omega

/-! ## 2. Unit-Cube Fiber Cardinality Bounds & Intra-Site Slot Bijection -/

private lemma snapPointToOpenBox_mem_ball3D {L : ℕ} [NeZero L] {M : ℝ} (hL : M + 1000 ≤ (L : ℝ) / 2)
    {p : Point3D} {v : Box3D L} (hp : ∀ μ, |p μ| ≤ M) (hv : snapPointToOpenBox L p = v) :
    p ∈ ball3D (fun μ => ((v μ).val : ℝ) - (L : ℝ) / 2 + 1 / 2) 1 := by
  subst hv; dsimp [ball3D, distSq3D]
  have h0 := (snapPointToOpenBox_bounds hL hp 0).2
  have h1 := (snapPointToOpenBox_bounds hL hp 1).2
  have h2 := (snapPointToOpenBox_bounds hL hp 2).2
  have hsq0 : (p 0 - (((snapPointToOpenBox L p 0).val : ℝ) - (L : ℝ) / 2 + 1 / 2)) ^ 2 ≤ (1 / 2 : ℝ) ^ 2 := by nlinarith
  have hsq1 : (p 1 - (((snapPointToOpenBox L p 1).val : ℝ) - (L : ℝ) / 2 + 1 / 2)) ^ 2 ≤ (1 / 2 : ℝ) ^ 2 := by nlinarith
  have hsq2 : (p 2 - (((snapPointToOpenBox L p 2).val : ℝ) - (L : ℝ) / 2 + 1 / 2)) ^ 2 ≤ (1 / 2 : ℝ) ^ 2 := by nlinarith
  nlinarith

private lemma card_filter_snapPointToOpenBox_le {L : ℕ} [NeZero L] {M : ℝ} (hL : M + 1000 ≤ (L : ℝ) / 2)
    {α : Type*} [Fintype α] (pos : α → Point3D) (hpos : ∀ a μ, |pos a μ| ≤ M) (v : Box3D L)
    [DecidablePred (fun a : α => snapPointToOpenBox L (pos a) = v)] :
    (Finset.univ.filter (fun a : α => snapPointToOpenBox L (pos a) = v)).card ≤
      (Finset.univ.filter (fun a : α =>
        pos a ∈ ball3D (fun μ => ((v μ).val : ℝ) - (L : ℝ) / 2 + 1 / 2) 1)).card :=
  Finset.card_le_card (fun a ha => Finset.mem_filter.mpr
    ⟨Finset.mem_univ a, snapPointToOpenBox_mem_ball3D hL (hpos a) (Finset.mem_filter.mp ha).2⟩)

/-- **Unit-Cube Fiber Cardinality Bound**: Every open-box site $v \in \mathrm{Box3D}(\mathrm{bdlBoxSide}\ k)$
    has `(bdlQubitFiber k v).card ≤ q_code_BDL`, `(bdlCheckXFiber k v).card ≤ m_max_BDL`,
    and `(bdlCheckZFiber k v).card ≤ m_max_BDL`. -/
theorem bdlFiber_card_bounds (k : ℕ) (v : Box3D (bdlBoxSide k)) :
    (bdlQubitFiber k v).card ≤ qCodeBDL ∧
    (bdlCheckXFiber k v).card ≤ mMaxBDL ∧
    (bdlCheckZFiber k v).card ≤ mMaxBDL := by
  have hL := bdlCoordBound_add_1000_le_half_L k
  have hb := hasBounded3DCoords_bdlWeldedBundled k
  let x0 : Point3D := fun μ => ((v μ).val : ℝ) - (bdlBoxSide k : ℝ) / 2 + 1 / 2
  have hd := WeldedHierarchy.bdl_random_lll_unit_ball_density k x0
  have hdQ : (Finset.univ.filter (fun q : BDLWeldedQubit k =>
      (bdlWeldedCode k).posQ q ∈ ball3D x0 1)).card ≤ qCodeBDL := by
    have h1 := hd.1; dsimp [bdlDensityT, qCodeBDL] at h1 ⊢; exact_mod_cast h1
  have hdZ : (Finset.univ.filter (fun mZ : BDLWeldedCheckZ k =>
      (bdlWeldedCode k).posZ mZ ∈ ball3D x0 1)).card ≤ mMaxBDL := by
    have h1 := hd.2.1; dsimp [bdlDensityT, mMaxBDL] at h1 ⊢; exact_mod_cast h1
  have hdX : (Finset.univ.filter (fun mX : BDLWeldedCheckX k =>
      (bdlWeldedCode k).posX mX ∈ ball3D x0 1)).card ≤ mMaxBDL := by
    have h1 := hd.2.2; dsimp [bdlDensityT, mMaxBDL] at h1 ⊢; exact_mod_cast h1
  exact ⟨(card_filter_snapPointToOpenBox_le hL (bdlWeldedCode k).posQ hb.1 v).trans hdQ,
         (card_filter_snapPointToOpenBox_le hL (bdlWeldedCode k).posX hb.2.2 v).trans hdX,
         (card_filter_snapPointToOpenBox_le hL (bdlWeldedCode k).posZ hb.2.1 v).trans hdZ⟩

private lemma fiber_localRank_lt_card {X V : Type*} [Fintype X] [DecidableEq V]
    (f : X → V) (idx : X → ℕ) (x : X) :
    ((Finset.univ.filter (fun x' : X => f x' = f x)).filter (fun x' => idx x' < idx x)).card <
      (Finset.univ.filter (fun x' : X => f x' = f x)).card := by
  apply Finset.card_lt_card
  rw [Finset.ssubset_iff_subset_ne]
  refine ⟨Finset.filter_subset _ _, fun h_eq => ?_⟩
  have hx : x ∈ Finset.univ.filter (fun x' : X => f x' = f x) := by simp
  rw [← h_eq, Finset.mem_filter] at hx
  exact Nat.lt_irrefl _ hx.2

private lemma fiber_localRank_injective {X V : Type*} [Fintype X] [DecidableEq V]
    (f : X → V) (idx : X → ℕ) (h_inj : Function.Injective idx) :
    Function.Injective (fun x : X =>
      (f x, ((Finset.univ.filter (fun x' : X => f x' = f x)).filter
        (fun x' => idx x' < idx x)).card)) := by
  intro x₁ x₂ h
  have hf : f x₁ = f x₂ := (Prod.ext_iff.mp h).1
  have hr := (Prod.ext_iff.mp h).2
  have h_lt : ∀ a b : X, f a = f b → idx a < idx b →
      ((Finset.univ.filter (fun x' : X => f x' = f a)).filter (fun x' => idx x' < idx a)).card <
      ((Finset.univ.filter (fun x' : X => f x' = f b)).filter (fun x' => idx x' < idx b)).card := by
    intro a b hab hlt; rw [hab]; apply Finset.card_lt_card; rw [Finset.ssubset_iff_subset_ne]
    refine ⟨fun y hy => ?_, fun h_eq => ?_⟩
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hy ⊢
      exact ⟨hy.1, Nat.lt_trans hy.2 hlt⟩
    · have ha : a ∈ (Finset.univ.filter (fun x' : X => f x' = f b)).filter (fun x' => idx x' < idx b) :=
        Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, hab⟩, hlt⟩
      rw [← h_eq, Finset.mem_filter] at ha; exact Nat.lt_irrefl _ ha.2
  rcases lt_trichotomy (idx x₁) (idx x₂) with h1 | heq | h2
  · exact False.elim (ne_of_lt (h_lt x₁ x₂ hf h1) hr)
  · exact h_inj heq
  · exact False.elim (ne_of_gt (h_lt x₂ x₁ hf.symm h2) hr)

private lemma fiber_localRank_surjective {X V : Type*} [Fintype X] [DecidableEq X] [DecidableEq V]
    (f : X → V) (idx : X → ℕ) (h_inj : Function.Injective idx)
    (v : V) (c : ℕ) (hc : c < (Finset.univ.filter (fun x' : X => f x' = v)).card) :
    ∃ x : X, f x = v ∧
      ((Finset.univ.filter (fun x' : X => f x' = f x)).filter
        (fun x' => idx x' < idx x)).card = c := by
  let S := Finset.univ.filter (fun x' : X => f x' = v)
  let g : S → Fin S.card := fun x =>
    ⟨((Finset.univ.filter (fun x' : X => f x' = f x.1)).filter (fun x' => idx x' < idx x.1)).card, by
      have hx : f x.1 = v := (Finset.mem_filter.mp x.2).2
      simpa [S, hx] using fiber_localRank_lt_card f idx x.1⟩
  have hg_inj : Function.Injective g := fun x₁ x₂ h =>
    Subtype.ext (fiber_localRank_injective f idx h_inj
      (Prod.ext ((Finset.mem_filter.mp x₁.2).2.trans (Finset.mem_filter.mp x₂.2).2.symm)
        (congr_arg Fin.val h)))
  obtain ⟨x, hx⟩ := ((Fintype.bijective_iff_injective_and_card g).mpr
    ⟨hg_inj, by simp [Fintype.card_coe, Fintype.card_fin]⟩).2 ⟨c, hc⟩
  exact ⟨x.1, (Finset.mem_filter.mp x.2).2, congr_arg Fin.val hx⟩

lemma bdlQubitLocalRank_lt_card (k : ℕ) (q : BDLWeldedQubit k) :
    bdlQubitLocalRank k q < (bdlQubitFiber k (bdlGridVertexQ k q)).card :=
  fiber_localRank_lt_card (bdlGridVertexQ k) (bdlCellIndexQ k) q

lemma bdlQubitLocalRank_lt_q_code (k : ℕ) (q : BDLWeldedQubit k) :
    bdlQubitLocalRank k q < qCodeBDL :=
  (bdlQubitLocalRank_lt_card k q).trans_le (bdlFiber_card_bounds k (bdlGridVertexQ k q)).1

lemma bdlQubitSiteSlot_eq (k : ℕ) (q : BDLWeldedQubit k) :
    bdlQubitSiteSlot k q =
      (bdlGridVertexQ k q, ⟨bdlQubitLocalRank k q, bdlQubitLocalRank_lt_q_code k q⟩) := by
  have h : bdlQubitLocalRankOf (bdlGridVertexQ k) (bdlCellIndexQ k) q < qCodeBDL :=
    bdlQubitLocalRank_lt_q_code k q
  dsimp [bdlQubitSiteSlot, bdlQubitSiteSlotOf]
  rw [dif_pos h]
  rfl

/-- `bdlQubitSiteSlot k` injects `BDLWeldedQubit k` into `BoxSlot3D (bdlBoxSide k) q_code_BDL`. -/
theorem bdlQubitSiteSlot_injective (k : ℕ) :
    Function.Injective (bdlQubitSiteSlot k) := by
  intro q₁ q₂ h
  rw [bdlQubitSiteSlot_eq k q₁, bdlQubitSiteSlot_eq k q₂] at h
  have h_injQ : Function.Injective (bdlCellIndexQ k) :=
    Fin.val_injective.comp (Fintype.equivFin _).injective
  exact fiber_localRank_injective (bdlGridVertexQ k) (bdlCellIndexQ k) h_injQ
    (Prod.ext (Prod.ext_iff.mp h).1 (congr_arg Fin.val (Prod.ext_iff.mp h).2))

lemma numXChecks_val_eq_card_fiber (k : ℕ) (v : Box3D (bdlBoxSide k)) :
    (bdlLocalDescriptor k v).numXChecks.val = (bdlCheckXFiber k v).card := by
  have h : (bdlCheckXFiberOf (bdlGridVertexX k) v).card ≤ mMaxBDL :=
    (bdlFiber_card_bounds k v).2.1
  dsimp [bdlLocalDescriptor, bdlLocalDescriptorOfPlacement]
  rw [dif_pos h]
  rfl

lemma numZChecks_val_eq_card_fiber (k : ℕ) (v : Box3D (bdlBoxSide k)) :
    (bdlLocalDescriptor k v).numZChecks.val = (bdlCheckZFiber k v).card := by
  have h : (bdlCheckZFiberOf (bdlGridVertexZ k) v).card ≤ mMaxBDL :=
    (bdlFiber_card_bounds k v).2.2
  dsimp [bdlLocalDescriptor, bdlLocalDescriptorOfPlacement]
  rw [dif_pos h]
  rfl

/-! ## 3. Interaction Range $\le 8 \implies \ell_\infty$ Grid Offset $\le r_0 = 9$ & Symplectic Commutativity -/

private lemma snapPointToOpenBox_nb_of_distSq_le {L : ℕ} [NeZero L] {M : ℝ}
    (hL : M + 1000 ≤ (L : ℝ) / 2) {p₁ p₂ : Point3D}
    (hp₁ : ∀ μ, |p₁ μ| ≤ M) (hp₂ : ∀ μ, |p₂ μ| ≤ M) (h_dist : distSq3D p₂ p₁ ≤ 8 ^ 2) :
    ∃ nb : LocalNeighborhoodIdx r0BDL,
      InOpenBox (snapPointToOpenBox L p₁) (neighborhoodOffset r0BDL nb) ∧
      shiftOpenBox (snapPointToOpenBox L p₁) (neighborhoodOffset r0BDL nb) =
        snapPointToOpenBox L p₂ := by
  have h_diff : ∀ μ : Fin 3,
      -9 ≤ ((snapPointToOpenBox L p₂ μ).val : ℤ) - ((snapPointToOpenBox L p₁ μ).val : ℤ) ∧
      ((snapPointToOpenBox L p₂ μ).val : ℤ) - ((snapPointToOpenBox L p₁ μ).val : ℤ) ≤ 9 := fun μ => by
    have h_sq : (p₂ μ - p₁ μ) ^ 2 ≤ 8 ^ 2 := by
      dsimp [distSq3D] at h_dist
      have := sq_nonneg (p₂ 0 - p₁ 0); have := sq_nonneg (p₂ 1 - p₁ 1); have := sq_nonneg (p₂ 2 - p₁ 2)
      fin_cases μ <;> (dsimp; linarith)
    have h_ab := abs_le_of_sq_le_sq' h_sq (by norm_num)
    have hb₁ := (snapPointToOpenBox_bounds hL hp₁ μ).2
    have hb₂ := (snapPointToOpenBox_bounds hL hp₂ μ).2
    have h_z1 : (-9 : ℤ) < ((snapPointToOpenBox L p₂ μ).val : ℤ) - ((snapPointToOpenBox L p₁ μ).val : ℤ) := by
      exact_mod_cast (by linarith : (-9 : ℝ) < ((snapPointToOpenBox L p₂ μ).val : ℝ) - ((snapPointToOpenBox L p₁ μ).val : ℝ))
    have h_z2 : ((snapPointToOpenBox L p₂ μ).val : ℤ) - ((snapPointToOpenBox L p₁ μ).val : ℤ) < 9 := by
      exact_mod_cast (by linarith : ((snapPointToOpenBox L p₂ μ).val : ℝ) - ((snapPointToOpenBox L p₁ μ).val : ℝ) < 9)
    omega
  let nb : LocalNeighborhoodIdx r0BDL := fun μ =>
    ⟨(snapPointToOpenBox L p₂ μ).val + r0BDL - (snapPointToOpenBox L p₁ μ).val,
     by have := h_diff μ; dsimp [r0BDL] at *; omega⟩
  have h_in : InOpenBox (snapPointToOpenBox L p₁) (neighborhoodOffset r0BDL nb) :=
    snapPointToOpenBox_inOpenBox_neighborhoodOffset hL hp₁ nb
  refine ⟨nb, h_in, funext fun μ => ?_⟩
  dsimp [shiftOpenBox, shiftOpenBoxD]
  rw [dif_pos (h_in μ)]
  apply Fin.ext
  dsimp [neighborhoodOffset, nb, r0BDL]
  have := h_diff μ
  omega

lemma bdlGridVertex_nb_of_checkX (k : ℕ) (mX : BDLWeldedCheckX k) (q : BDLWeldedQubit k)
    (h_chk : (bdlWeldedCode k).checkX mX q ≠ 0) :
    ∃ nb : LocalNeighborhoodIdx r0BDL,
      InOpenBox (bdlGridVertexX k mX) (neighborhoodOffset r0BDL nb) ∧
      shiftOpenBox (bdlGridVertexX k mX) (neighborhoodOffset r0BDL nb) = bdlGridVertexQ k q := by
  have hL := bdlCoordBound_add_1000_le_half_L k
  have hb := hasBounded3DCoords_bdlWeldedBundled k
  have h_r := (WeldedHierarchy.bdl_random_interaction_range8 k).2 mX q h_chk
  exact snapPointToOpenBox_nb_of_distSq_le hL (hb.2.2 mX) (hb.1 q) h_r

lemma bdlGridVertex_nb_of_checkZ (k : ℕ) (mZ : BDLWeldedCheckZ k) (q : BDLWeldedQubit k)
    (h_chk : (bdlWeldedCode k).checkZ mZ q ≠ 0) :
    ∃ nb : LocalNeighborhoodIdx r0BDL,
      InOpenBox (bdlGridVertexZ k mZ) (neighborhoodOffset r0BDL nb) ∧
      shiftOpenBox (bdlGridVertexZ k mZ) (neighborhoodOffset r0BDL nb) = bdlGridVertexQ k q := by
  have hL := bdlCoordBound_add_1000_le_half_L k
  have hb := hasBounded3DCoords_bdlWeldedBundled k
  have h_r := (WeldedHierarchy.bdl_random_interaction_range8 k).1 mZ q h_chk
  exact snapPointToOpenBox_nb_of_distSq_le hL (hb.2.1 mZ) (hb.1 q) h_r

lemma descriptorCheckXChain_bdlQubitSiteSlot_eq (k : ℕ)
    (mX : BDLWeldedCheckX k) (idxX : Fin mMaxBDL)
    (h_rank : bdlCheckXLocalRank k mX = idxX.val) (q : BDLWeldedQubit k) :
    descriptorCheckXChain (bdlLocalDescriptor k) (bdlGridVertexX k mX) idxX (bdlQubitSiteSlot k q) =
      (bdlWeldedCode k).checkX mX q := by
  have h_injX : Function.Injective (bdlCellIndexX k) :=
    Fin.val_injective.comp (Fintype.equivFin _).injective
  have h_lt : idxX.val < (bdlLocalDescriptor k (bdlGridVertexX k mX)).numXChecks.val := by
    rw [numXChecks_val_eq_card_fiber, ← h_rank]
    exact fiber_localRank_lt_card (bdlGridVertexX k) (bdlCellIndexX k) mX
  have h_iff : (idxX.val < (bdlLocalDescriptor k (bdlGridVertexX k mX)).numXChecks.val ∧
      ∃ nb : LocalNeighborhoodIdx r0BDL,
        InOpenBox (bdlGridVertexX k mX) (neighborhoodOffset r0BDL nb) ∧
        shiftOpenBox (bdlGridVertexX k mX) (neighborhoodOffset r0BDL nb) = (bdlQubitSiteSlot k q).1 ∧
        (bdlLocalDescriptor k (bdlGridVertexX k mX)).xCheckMask idxX nb (bdlQubitSiteSlot k q).2 = true) ↔
      (bdlWeldedCode k).checkX mX q ≠ 0 := by
    refine ⟨fun ⟨_, nb, _, h_sh, h_mask⟩ => ?_, fun h_chk => ?_⟩
    · dsimp [bdlLocalDescriptor, bdlLocalDescriptorOfPlacement] at h_mask
      rw [Bool.and_eq_true] at h_mask
      rcases decide_eq_true_iff.mp h_mask.2 with ⟨mX', q', hv', hr', hq', h_chk⟩
      have hm : mX' = mX :=
        fiber_localRank_injective (bdlGridVertexX k) (bdlCellIndexX k) h_injX
          (Prod.ext hv' (hr'.trans h_rank.symm))
      change bdlQubitSiteSlot k q' = _ at hq'
      have hq : q' = q := bdlQubitSiteSlot_injective k (by rw [hq', h_sh])
      subst hm hq; exact h_chk
    · obtain ⟨nb, h_in, h_sh⟩ := bdlGridVertex_nb_of_checkX k mX q h_chk
      have h_fst : (bdlQubitSiteSlot k q).1 = bdlGridVertexQ k q := rfl
      refine ⟨h_lt, nb, h_in, h_sh.trans h_fst.symm, ?_⟩
      dsimp [bdlLocalDescriptor, bdlLocalDescriptorOfPlacement]
      rw [Bool.and_eq_true]
      exact ⟨decide_eq_true h_in,
        decide_eq_true_iff.mpr ⟨mX, q, rfl, h_rank, Prod.ext (h_fst.trans h_sh.symm) rfl, h_chk⟩⟩
  change (if idxX.val < (bdlLocalDescriptor k (bdlGridVertexX k mX)).numXChecks.val ∧
      ∃ nb : LocalNeighborhoodIdx r0BDL,
        InOpenBox (bdlGridVertexX k mX) (neighborhoodOffset r0BDL nb) ∧
        shiftOpenBox (bdlGridVertexX k mX) (neighborhoodOffset r0BDL nb) = (bdlQubitSiteSlot k q).1 ∧
        (bdlLocalDescriptor k (bdlGridVertexX k mX)).xCheckMask idxX nb (bdlQubitSiteSlot k q).2 = true
    then (1 : ZMod 2) else 0) = (bdlWeldedCode k).checkX mX q
  by_cases h_nz : (bdlWeldedCode k).checkX mX q ≠ 0
  · rw [if_pos (h_iff.mpr h_nz)]
    exact (zmod2_ne_zero_iff_eq_one _ h_nz).symm
  · push_neg at h_nz
    rw [if_neg (fun h => h_iff.mp h h_nz), h_nz]

lemma descriptorCheckZChain_bdlQubitSiteSlot_eq (k : ℕ)
    (mZ : BDLWeldedCheckZ k) (idxZ : Fin mMaxBDL)
    (h_rank : bdlCheckZLocalRank k mZ = idxZ.val) (q : BDLWeldedQubit k) :
    descriptorCheckZChain (bdlLocalDescriptor k) (bdlGridVertexZ k mZ) idxZ (bdlQubitSiteSlot k q) =
      (bdlWeldedCode k).checkZ mZ q := by
  have h_injZ : Function.Injective (bdlCellIndexZ k) :=
    Fin.val_injective.comp (Fintype.equivFin _).injective
  have h_lt : idxZ.val < (bdlLocalDescriptor k (bdlGridVertexZ k mZ)).numZChecks.val := by
    rw [numZChecks_val_eq_card_fiber, ← h_rank]
    exact fiber_localRank_lt_card (bdlGridVertexZ k) (bdlCellIndexZ k) mZ
  have h_iff : (idxZ.val < (bdlLocalDescriptor k (bdlGridVertexZ k mZ)).numZChecks.val ∧
      ∃ nb : LocalNeighborhoodIdx r0BDL,
        InOpenBox (bdlGridVertexZ k mZ) (neighborhoodOffset r0BDL nb) ∧
        shiftOpenBox (bdlGridVertexZ k mZ) (neighborhoodOffset r0BDL nb) = (bdlQubitSiteSlot k q).1 ∧
        (bdlLocalDescriptor k (bdlGridVertexZ k mZ)).zCheckMask idxZ nb (bdlQubitSiteSlot k q).2 = true) ↔
      (bdlWeldedCode k).checkZ mZ q ≠ 0 := by
    refine ⟨fun ⟨_, nb, _, h_sh, h_mask⟩ => ?_, fun h_chk => ?_⟩
    · dsimp [bdlLocalDescriptor, bdlLocalDescriptorOfPlacement] at h_mask
      rw [Bool.and_eq_true] at h_mask
      rcases decide_eq_true_iff.mp h_mask.2 with ⟨mZ', q', hv', hr', hq', h_chk⟩
      have hm : mZ' = mZ :=
        fiber_localRank_injective (bdlGridVertexZ k) (bdlCellIndexZ k) h_injZ
          (Prod.ext hv' (hr'.trans h_rank.symm))
      change bdlQubitSiteSlot k q' = _ at hq'
      have hq : q' = q := bdlQubitSiteSlot_injective k (by rw [hq', h_sh])
      subst hm hq; exact h_chk
    · obtain ⟨nb, h_in, h_sh⟩ := bdlGridVertex_nb_of_checkZ k mZ q h_chk
      have h_fst : (bdlQubitSiteSlot k q).1 = bdlGridVertexQ k q := rfl
      refine ⟨h_lt, nb, h_in, h_sh.trans h_fst.symm, ?_⟩
      dsimp [bdlLocalDescriptor, bdlLocalDescriptorOfPlacement]
      rw [Bool.and_eq_true]
      exact ⟨decide_eq_true h_in,
        decide_eq_true_iff.mpr ⟨mZ, q, rfl, h_rank, Prod.ext (h_fst.trans h_sh.symm) rfl, h_chk⟩⟩
  change (if idxZ.val < (bdlLocalDescriptor k (bdlGridVertexZ k mZ)).numZChecks.val ∧
      ∃ nb : LocalNeighborhoodIdx r0BDL,
        InOpenBox (bdlGridVertexZ k mZ) (neighborhoodOffset r0BDL nb) ∧
        shiftOpenBox (bdlGridVertexZ k mZ) (neighborhoodOffset r0BDL nb) = (bdlQubitSiteSlot k q).1 ∧
        (bdlLocalDescriptor k (bdlGridVertexZ k mZ)).zCheckMask idxZ nb (bdlQubitSiteSlot k q).2 = true
    then (1 : ZMod 2) else 0) = (bdlWeldedCode k).checkZ mZ q
  by_cases h_nz : (bdlWeldedCode k).checkZ mZ q ≠ 0
  · rw [if_pos (h_iff.mpr h_nz)]
    exact (zmod2_ne_zero_iff_eq_one _ h_nz).symm
  · push_neg at h_nz
    rw [if_neg (fun h => h_iff.mp h h_nz), h_nz]

private lemma descriptorCheckXChain_eq_zero_of_not_mem_image (k : ℕ)
    (vX : Box3D (bdlBoxSide k)) (idxX : Fin mMaxBDL)
    (p : BoxSlot3D (bdlBoxSide k) qCodeBDL)
    (hp : p ∉ Finset.univ.image (bdlQubitSiteSlot k)) :
    descriptorCheckXChain (bdlLocalDescriptor k) vX idxX p = 0 := by
  rcases p with ⟨w, s⟩
  dsimp [descriptorCheckXChain]
  rw [if_neg]
  rintro ⟨_, nb, _, h_sh, h_mask⟩
  dsimp [bdlLocalDescriptor, bdlLocalDescriptorOfPlacement] at h_mask
  rw [Bool.and_eq_true] at h_mask
  rcases decide_eq_true_iff.mp h_mask.2 with ⟨_, q, _, _, hq, _⟩
  apply hp
  rw [Finset.mem_image]
  exact ⟨q, Finset.mem_univ q, by simpa [h_sh, bdlQubitSiteSlot] using hq⟩

/-- **Global Open-Box Validity of the Multi-Site BDL Descriptor Field (`ValidDescriptorField (bdlLocalDescriptor k)`)**:
    Proves that `bdlLocalDescriptor k` satisfies all three global validity properties on `Box3D (bdlBoxSide k)`:
    1. All active $X$- and $Z$-check masks fit inside the open box (`InOpenBox`);
    2. All active check masks touch only active qubit slots (`activeSlot s = true`);
    3. Every active $X$-check chain and active $Z$-check chain have even symplectic overlap (`= 0` in `ZMod 2`). -/
theorem bdlLocalDescriptor_validDescriptorField_proof (k : ℕ) :
    ValidDescriptorField (bdlLocalDescriptor k) := by
  refine ⟨?_, ?_, ?_⟩
  · intro v idx nb s _ h_mask
    dsimp [bdlLocalDescriptor, bdlLocalDescriptorOfPlacement] at h_mask
    rw [Bool.and_eq_true] at h_mask
    have h_in : InOpenBox v (neighborhoodOffset r0BDL nb) := of_decide_eq_true h_mask.1
    rcases decide_eq_true_iff.mp h_mask.2 with ⟨_, q, _, _, hq, _⟩
    change bdlQubitSiteSlot k q = _ at hq
    rw [bdlQubitSiteSlot_eq k q] at hq
    have hv_eq : bdlGridVertexQ k q = shiftOpenBox v (neighborhoodOffset r0BDL nb) :=
      (Prod.ext_iff.mp hq).1
    have hs_eq : s.val = bdlQubitLocalRank k q :=
      (congr_arg Fin.val (Prod.ext_iff.mp hq).2).symm
    refine ⟨h_in, ?_⟩
    dsimp [bdlLocalDescriptor, bdlLocalDescriptorOfPlacement]
    rw [decide_eq_true_iff, hs_eq, ← hv_eq]
    exact bdlQubitLocalRank_lt_card k q
  · intro v idx nb s _ h_mask
    dsimp [bdlLocalDescriptor, bdlLocalDescriptorOfPlacement] at h_mask
    rw [Bool.and_eq_true] at h_mask
    have h_in : InOpenBox v (neighborhoodOffset r0BDL nb) := of_decide_eq_true h_mask.1
    rcases decide_eq_true_iff.mp h_mask.2 with ⟨_, q, _, _, hq, _⟩
    change bdlQubitSiteSlot k q = _ at hq
    rw [bdlQubitSiteSlot_eq k q] at hq
    have hv_eq : bdlGridVertexQ k q = shiftOpenBox v (neighborhoodOffset r0BDL nb) :=
      (Prod.ext_iff.mp hq).1
    have hs_eq : s.val = bdlQubitLocalRank k q :=
      (congr_arg Fin.val (Prod.ext_iff.mp hq).2).symm
    refine ⟨h_in, ?_⟩
    dsimp [bdlLocalDescriptor, bdlLocalDescriptorOfPlacement]
    rw [decide_eq_true_iff, hs_eq, ← hv_eq]
    exact bdlQubitLocalRank_lt_card k q
  · intro vX vZ idxX idxZ
    by_cases hX : idxX.val < (bdlLocalDescriptor k vX).numXChecks.val
    · by_cases hZ : idxZ.val < (bdlLocalDescriptor k vZ).numZChecks.val
      · rw [numXChecks_val_eq_card_fiber] at hX
        rw [numZChecks_val_eq_card_fiber] at hZ
        have h_injX : Function.Injective (bdlCellIndexX k) :=
          Fin.val_injective.comp (Fintype.equivFin _).injective
        have h_injZ : Function.Injective (bdlCellIndexZ k) :=
          Fin.val_injective.comp (Fintype.equivFin _).injective
        obtain ⟨mX, hmX_v, hmX_r⟩ :=
          fiber_localRank_surjective (bdlGridVertexX k) (bdlCellIndexX k) h_injX vX idxX.val hX
        obtain ⟨mZ, hmZ_v, hmZ_r⟩ :=
          fiber_localRank_surjective (bdlGridVertexZ k) (bdlCellIndexZ k) h_injZ vZ idxZ.val hZ
        subst hmX_v hmZ_v
        refine (Finset.sum_subset (Finset.subset_univ (Finset.univ.image (bdlQubitSiteSlot k))) ?_).symm.trans ?_
        · intro p _ hp
          rw [descriptorCheckXChain_eq_zero_of_not_mem_image k _ idxX p hp, zero_mul]
        · rw [Finset.sum_image (fun q₁ _ q₂ _ h => bdlQubitSiteSlot_injective k h)]
          simp_rw [descriptorCheckXChain_bdlQubitSiteSlot_eq k mX idxX hmX_r,
            descriptorCheckZChain_bdlQubitSiteSlot_eq k mZ idxZ hmZ_r]
          exact (bdlWeldedCode k).commutativity mX mZ
      · refine Finset.sum_eq_zero (fun ⟨w, s⟩ _ => ?_)
        dsimp [descriptorCheckZChain]
        rw [if_neg (fun h => hZ h.1), mul_zero]
    · refine Finset.sum_eq_zero (fun ⟨w, s⟩ _ => ?_)
      dsimp [descriptorCheckXChain]
      rw [if_neg (fun h => hX h.1), zero_mul]

end
