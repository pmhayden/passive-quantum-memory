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

import Proofs.ConeAcyclicityRCA.RescaledRCASynthesis
import Defs.BDLSubstitutionCode

/-!
# Syndrome Decoders, Classical Free-Energy Barriers, and Welded Cell-Count Growth

Defines abstract CSS syndrome decoders (`Decoder`), single-qubit jump failure sets (`decoderFailureSet`), and classical equilibrium free-energy barriers (`HasEquilibriumFreeEnergyBarrier`, `IsThermallyStable`). Bounds the total cell count `bundledCellCount` across iterated primal and dual three-layer welded steps (`bundledCellCount_iterated_le`, `numQubits_bdlRandomCode_le_stepFactor_pow`).

## References

* Part I, Section 2.3 (`subsec:step2-mapping-cone`), Proposition 2.6 (`prop:mapping-cone-invariants`)
* Part I, Section 5.2 (`subsec:cluster-decoder`), Definition 5.2 (`def:multiscale-cluster-decoder`)
* Part I, Section 5.3 (`subsec:walsh-fourier-peierls`), Theorem 5.5 (`thm:walsh-fourier-peierls`)
-/

noncomputable section

open scoped Classical
open BigOperators

namespace WeldedHierarchy

/-! ## 1. Equilibrium Free-Energy Thermal Stability Definitions -/

/-- Number of physical qubits `N = |Q|`, derived directly from the finite type `Q`. -/
def numQubits {Q M_Z M_X : Type}
    [Fintype Q] [DecidableEq Q] [Fintype M_Z] [DecidableEq M_Z] [Fintype M_X] [DecidableEq M_X]
    (_ : CSSCode3D Q M_Z M_X) : ℝ :=
  (Fintype.card Q : ℝ)

/-- Derived Hamming weight `|g|` of a 1-chain `g : Q → ZMod 2`. -/
def hammingWeight {Q : Type} [Fintype Q] [DecidableEq Q] (g : Q → ZMod 2) : ℝ :=
  ((Finset.univ.filter (fun q : Q => g q ≠ 0)).card : ℝ)

/-- Derived syndrome weight (excitation energy penalty) `|s|` of a syndrome `s : M_X → ZMod 2`:
    the number of violated X-check generators. -/
def syndromeWeight {M_X : Type} [Fintype M_X] [DecidableEq M_X] (s : M_X → ZMod 2) : ℝ :=
  ((Finset.univ.filter (fun m : M_X => s m ≠ 0)).card : ℝ)

/-- Derived elementary jump operators: single-qubit Pauli errors `{e_q | q ∈ Q}`. -/
def elementaryJumps {Q : Type} [DecidableEq Q] : Set (Q → ZMod 2) :=
  {E : (Q → ZMod 2) | ∃ q : Q, E = singleQubit q}

/-- A syndrome decoder maps each syndrome `s : M_X → ZMod 2` to a recovery 1-chain
    `decode s : Q → ZMod 2` that reproduces the syndrome for all realizable error syndromes
    `s = syndrome code e`. -/
structure Decoder {Q M_Z M_X : Type}
    [Fintype Q] [DecidableEq Q] [Fintype M_Z] [DecidableEq M_Z] [Fintype M_X] [DecidableEq M_X]
    (code : CSSCode3D Q M_Z M_X) where
  decode : (M_X → ZMod 2) → (Q → ZMod 2)
  h_correct : ∀ e : (Q → ZMod 2), syndrome code (decode (syndrome code e)) = syndrome code e

/-- The decoder failure set: realizable syndromes `s = syndrome code e_err` where a single-qubit
    error `E ∈ elementaryJumps` causes the decoder recovery to change by a non-trivial logical
    operator (`decode s + E - decode (s + ∂₁ E) ∉ im(∂₂)`). -/
def decoderFailureSet {Q M_Z M_X : Type}
    [Fintype Q] [DecidableEq Q] [Fintype M_Z] [DecidableEq M_Z] [Fintype M_X] [DecidableEq M_X]
    (code : CSSCode3D Q M_Z M_X) (dec : Decoder code) : Set (M_X → ZMod 2) :=
  {s : (M_X → ZMod 2) | (∃ e_err : (Q → ZMod 2), syndrome code e_err = s) ∧
    ∃ E ∈ elementaryJumps (Q := Q),
      ∀ c2 : (M_Z → ZMod 2),
        checkGen code c2 ≠ dec.decode s + E - dec.decode (s + syndrome code E)}

/-- Equilibrium free-energy barrier `ΔF_target` at inverse temperature `β`. -/
def HasEquilibriumFreeEnergyBarrier {Q M_Z M_X : Type}
    [Fintype Q] [DecidableEq Q] [Fintype M_Z] [DecidableEq M_Z] [Fintype M_X] [DecidableEq M_X]
    (code : CSSCode3D Q M_Z M_X) (β ΔF_target : ℝ) : Prop :=
  ∃ dec : Decoder code,
    ∀ (S_fail : Finset (M_X → ZMod 2)),
      (↑S_fail : Set (M_X → ZMod 2)) ⊆ decoderFailureSet code dec →
      (∑ s ∈ S_fail, Real.exp (-β * syndromeWeight s)) ≤
        (∑ s ∈ Finset.univ.image (syndrome code), Real.exp (-β * syndromeWeight s)) * Real.exp (-ΔF_target)

/-- A family of 3D CSS codes `codes k` is thermally stable via an equilibrium free-energy barrier
    if there exist constants `β_c > 0`, `η > 0`, `c_F > 0` such that for all `β > β_c` and all `k`,
    `codes k` has an equilibrium free-energy barrier `ΔF ≥ c_F (β - β_c) (numQubits (codes k)) ^ η`. -/
def IsThermallyStable
    {Q M_Z M_X : ℕ → Type}
    [∀ k, Fintype (Q k)] [∀ k, DecidableEq (Q k)]
    [∀ k, Fintype (M_Z k)] [∀ k, DecidableEq (M_Z k)]
    [∀ k, Fintype (M_X k)] [∀ k, DecidableEq (M_X k)]
    (codes : ∀ k : ℕ, CSSCode3D (Q k) (M_Z k) (M_X k))
    (β_c η c_F : ℝ) : Prop :=
  β_c > 0 ∧ η > 0 ∧ c_F > 0 ∧
  ∀ (β : ℝ), β > β_c →
    ∀ (k : ℕ),
      let ΔF_target := c_F * (β - β_c) * ((numQubits (codes k)) ^ η)
      HasEquilibriumFreeEnergyBarrier (codes k) β ΔF_target

/-! ## 2. Active Incidence Cardinality Bounds & Cell-Count Growth -/

/-- Total cell count `|Q| + |M_Z| + |M_X|` of a bundled 3D CSS code. -/
def bundledCellCount (B : BundledCSSCode3D) : ℕ :=
  Fintype.card B.Q + Fintype.card B.M_Z + Fintype.card B.M_X

/-- Single-step symbolic cell-count multiplier across `bdlRandomStepX` (`M = bdlSubdivPred`). -/
abbrev bdlSingleStepFactor : ℕ := _root_.bdlSingleStepFactor

/-- Symbolic upper bound factor on `numQubits (bdlRandomCode k)` per level `k + 1`. -/
def bdlRandomStepFactor : ℕ := 9 * bdlSingleStepFactor ^ 2

/-- Verifies that the subdivision parameter `bdlSubdivM = bdlSubdivPred + 1` is at least `2`. -/
lemma bdlSubdivM_ge_two : 2 ≤ bdlSubdivM := by
  dsimp [bdlSubdivM, bdlSubdivFactor, bdlAlphaNat]
  have h := bdlLambda_pos
  omega

/-- Verifies that `bdlSingleStepFactor` is at least `2`. -/
lemma bdlSingleStepFactor_ge_two : 2 ≤ bdlSingleStepFactor := by
  dsimp [bdlSingleStepFactor, _root_.bdlSingleStepFactor]
  have h := bdlSubdivM_ge_two
  nlinarith

/-- Verifies that `bdlRandomStepFactor` is at least `2`. -/
lemma bdlRandomStepFactor_ge_two : 2 ≤ bdlRandomStepFactor := by
  dsimp [bdlRandomStepFactor]
  have h := bdlSingleStepFactor_ge_two
  nlinarith

/-- Real-cast inequality `1 < (bdlRandomStepFactor : ℝ)`. -/
lemma bdlRandomStepFactor_gt_one_real : (1 : ℝ) < (bdlRandomStepFactor : ℝ) := by
  have h : 2 ≤ bdlRandomStepFactor := bdlRandomStepFactor_ge_two
  exact_mod_cast Nat.lt_of_lt_of_le (by norm_num : 1 < 2) h

/-- Under `HasBoundedCheckDegree B 8 8 4 4`, the number of active Z-pair incidences `ActiveZ B.code`
    is at most `4 * Fintype.card B.Q`. -/
lemma card_activeZ_le_four_mul_card_Q (B : BundledCSSCode3D)
    (hdeg : HasBoundedCheckDegree B 8 8 4 4) :
    Fintype.card (ActiveZ B.code) ≤ 4 * Fintype.card B.Q := by
  let S : Finset (B.Q × B.M_Z) :=
    Finset.univ.biUnion (fun q : B.Q =>
      (Finset.univ.filter (fun z : B.M_Z => B.code.checkZ z q ≠ 0)).image (fun z => (q, z)))
  have h_maps : Set.MapsTo (fun eZ : ActiveZ B.code => eZ.val)
      (↑(Finset.univ : Finset (ActiveZ B.code)) : Set (ActiveZ B.code)) (↑S : Set (B.Q × B.M_Z)) := by
    intro eZ _
    rw [Finset.mem_coe, Finset.mem_biUnion]
    refine ⟨eZ.val.1, Finset.mem_univ _, ?_⟩
    rw [Finset.mem_image]
    exact ⟨eZ.val.2, Finset.mem_filter.mpr ⟨Finset.mem_univ _, eZ.property⟩, rfl⟩
  have h_inj : Set.InjOn (fun eZ : ActiveZ B.code => eZ.val)
      (↑(Finset.univ : Finset (ActiveZ B.code)) : Set (ActiveZ B.code)) :=
    fun _ _ _ _ h => Subtype.ext h
  have h_card : Fintype.card (ActiveZ B.code) ≤ S.card :=
    Finset.card_le_card_of_injOn _ h_maps h_inj
  have h_S : S.card ≤ 4 * Fintype.card B.Q := by
    calc S.card
      _ ≤ ∑ q : B.Q, ((Finset.univ.filter (fun z : B.M_Z => B.code.checkZ z q ≠ 0)).image (fun z => (q, z))).card :=
          Finset.card_biUnion_le
      _ ≤ ∑ _q : B.Q, 4 := by
          apply Finset.sum_le_sum
          intro q _
          exact Finset.card_image_le.trans (hdeg.2.2.2 q)
      _ = 4 * Fintype.card B.Q := by
          rw [Finset.sum_const, Finset.card_univ, smul_eq_mul, mul_comm]
  exact h_card.trans h_S

/-- Under `HasBoundedCheckDegree B 8 8 4 4`, the number of active X-pair incidences `ActiveX B.code`
    is at most `4 * Fintype.card B.Q`. -/
lemma card_activeX_le_four_mul_card_Q (B : BundledCSSCode3D)
    (hdeg : HasBoundedCheckDegree B 8 8 4 4) :
    Fintype.card (ActiveX B.code) ≤ 4 * Fintype.card B.Q := by
  let S : Finset (B.Q × B.M_X) :=
    Finset.univ.biUnion (fun q : B.Q =>
      (Finset.univ.filter (fun x : B.M_X => B.code.checkX x q ≠ 0)).image (fun x => (q, x)))
  have h_maps : Set.MapsTo (fun eX : ActiveX B.code => eX.val)
      (↑(Finset.univ : Finset (ActiveX B.code)) : Set (ActiveX B.code)) (↑S : Set (B.Q × B.M_X)) := by
    intro eX _
    rw [Finset.mem_coe, Finset.mem_biUnion]
    refine ⟨eX.val.1, Finset.mem_univ _, ?_⟩
    rw [Finset.mem_image]
    exact ⟨eX.val.2, Finset.mem_filter.mpr ⟨Finset.mem_univ _, eX.property⟩, rfl⟩
  have h_inj : Set.InjOn (fun eX : ActiveX B.code => eX.val)
      (↑(Finset.univ : Finset (ActiveX B.code)) : Set (ActiveX B.code)) :=
    fun _ _ _ _ h => Subtype.ext h
  have h_card : Fintype.card (ActiveX B.code) ≤ S.card :=
    Finset.card_le_card_of_injOn _ h_maps h_inj
  have h_S : S.card ≤ 4 * Fintype.card B.Q := by
    calc S.card
      _ ≤ ∑ q : B.Q, ((Finset.univ.filter (fun x : B.M_X => B.code.checkX x q ≠ 0)).image (fun x => (q, x))).card :=
          Finset.card_biUnion_le
      _ ≤ ∑ _q : B.Q, 4 := by
          apply Finset.sum_le_sum
          intro q _
          exact Finset.card_image_le.trans (hdeg.2.2.1 q)
      _ = 4 * Fintype.card B.Q := by
          rw [Finset.sum_const, Finset.card_univ, smul_eq_mul, mul_comm]
  exact h_card.trans h_S

/-- Under `HasBoundedSimplexDegreeD B 32`, the number of active 2-simplices `ActiveSimplex2 B.code`
    is at most `32 * Fintype.card B.M_X`. -/
lemma card_activeSimplex2_le_28_mul_card_MX (B : BundledCSSCode3D)
    (hsimp : HasBoundedSimplexDegreeD B 32) :
    Fintype.card (ActiveSimplex2 B.code) ≤ 32 * Fintype.card B.M_X := by
  let S : Finset (ActiveSimplex2 B.code) :=
    Finset.univ.biUnion (fun x : B.M_X =>
      Finset.univ.filter (fun s : ActiveSimplex2 B.code => s.val.1 = x))
  have h_univ : (Finset.univ : Finset (ActiveSimplex2 B.code)) ⊆ S := by
    intro s _
    rw [Finset.mem_biUnion]
    exact ⟨s.val.1, Finset.mem_univ _, Finset.mem_filter.mpr ⟨Finset.mem_univ _, rfl⟩⟩
  calc Fintype.card (ActiveSimplex2 B.code)
    _ ≤ S.card := Finset.card_le_card h_univ
    _ ≤ ∑ x : B.M_X, (Finset.univ.filter (fun s : ActiveSimplex2 B.code => s.val.1 = x)).card :=
        Finset.card_biUnion_le
    _ ≤ ∑ _x : B.M_X, 32 := Finset.sum_le_sum (fun x _ => hsimp.1 x)
    _ = 32 * Fintype.card B.M_X := by
        rw [Finset.sum_const, Finset.card_univ, smul_eq_mul, mul_comm]

/-- Bounds the number of active Z-links `|ActiveZLink B.code|` by `32 * |M_X|`. -/
lemma card_activeZLink_le_28_mul_card_MX (B : BundledCSSCode3D)
    (hsimp : HasBoundedSimplexDegreeD B 32) :
    Fintype.card (ActiveZLink B.code) ≤ 32 * Fintype.card B.M_X := by
  let f : ActiveZLink B.code → ActiveSimplex2 B.code :=
    fun p => ⟨(p.val.1, p.val.2.val.1, p.val.2.val.2), ⟨p.property, p.val.2.property⟩⟩
  have hf : Function.Injective f := by
    intro p1 p2 h
    apply Subtype.ext
    apply Prod.ext
    · exact congr_arg (fun s : ActiveSimplex2 B.code => s.val.1) h
    · apply Subtype.ext
      exact Prod.ext
        (congr_arg (fun s : ActiveSimplex2 B.code => s.val.2.1) h)
        (congr_arg (fun s : ActiveSimplex2 B.code => s.val.2.2) h)
  exact (Fintype.card_le_of_injective f hf).trans (card_activeSimplex2_le_28_mul_card_MX B hsimp)

/-- Injective encoding of `BoundaryX0Link pcode M` into a disjoint sum of coarse incidence types. -/
noncomputable def boundaryX0LinkToSum {Q M_Z M_X : Type}
    [Fintype Q] [DecidableEq Q] [Fintype M_Z] [DecidableEq M_Z] [Fintype M_X] [DecidableEq M_X]
    (pcode : CSSCode3D Q M_Z M_X) (M : ℕ) :
    BoundaryX0Link pcode M →
      ActiveX pcode ⊕ (ActiveZLink pcode × Fin M) ⊕ ActiveSimplex2 pcode
  | ⟨(x, Sum.inl q), h⟩ => Sum.inl ⟨(q, x), h⟩
  | ⟨(x, Sum.inr (Sum.inl (eZ, j))), h⟩ => Sum.inr (Sum.inl (⟨(x, eZ), h⟩, j))
  | ⟨(x, Sum.inr (Sum.inr z)), h⟩ =>
      Sum.inr (Sum.inr ⟨(x, Classical.choose h, z), Classical.choose_spec h⟩)

/-- Proves that `boundaryX0LinkToSum pcode M` is injective. -/
lemma boundaryX0LinkToSum_injective {Q M_Z M_X : Type}
    [Fintype Q] [DecidableEq Q] [Fintype M_Z] [DecidableEq M_Z] [Fintype M_X] [DecidableEq M_X]
    (pcode : CSSCode3D Q M_Z M_X) (M : ℕ) :
    Function.Injective (boundaryX0LinkToSum pcode M) := by
  intro p1 p2 h
  rcases p1 with ⟨⟨x1, q1 | ⟨⟨eZ1, j1⟩ | z1⟩⟩, h1⟩ <;>
    rcases p2 with ⟨⟨x2, q2 | ⟨⟨eZ2, j2⟩ | z2⟩⟩, h2⟩ <;>
    dsimp [boundaryX0LinkToSum] at h
  · injection h with h_eq
    have hx : x1 = x2 := congr_arg (fun u : ActiveX pcode => u.val.2) h_eq
    have hq : q1 = q2 := congr_arg (fun u : ActiveX pcode => u.val.1) h_eq
    subst hx hq; rfl
  · nomatch h
  · nomatch h
  · nomatch h
  · injection h with h_inr
    injection h_inr with h_prod
    have hx : x1 = x2 := congr_arg (fun u : ActiveZLink pcode × Fin M => u.1.val.1) h_prod
    have heZ : eZ1 = eZ2 := congr_arg (fun u : ActiveZLink pcode × Fin M => u.1.val.2) h_prod
    have hj : j1 = j2 := congr_arg Prod.snd h_prod
    subst hx heZ hj; rfl
  · nomatch h
  · nomatch h
  · nomatch h
  · injection h with h_inr
    injection h_inr with h_simp
    have hx : x1 = x2 := congr_arg (fun u : ActiveSimplex2 pcode => u.val.1) h_simp
    have hz : z1 = z2 := congr_arg (fun u : ActiveSimplex2 pcode => u.val.2.2) h_simp
    subst hx hz; rfl

/-- Bounds `|BoundaryX0Link B.code M|` by `4 * |Q| + 32 * (M + 1) * |M_X|`. -/
lemma card_boundaryX0Link_le (B : BundledCSSCode3D) (M : ℕ)
    (hdeg : HasBoundedCheckDegree B 8 8 4 4)
    (hsimp : HasBoundedSimplexDegreeD B 32) :
    Fintype.card (BoundaryX0Link B.code M) ≤
      4 * Fintype.card B.Q + 32 * (M + 1) * Fintype.card B.M_X := by
  have h_inj := Fintype.card_le_of_injective (boundaryX0LinkToSum B.code M)
    (boundaryX0LinkToSum_injective B.code M)
  simp only [Fintype.card_sum, Fintype.card_prod, Fintype.card_fin] at h_inj
  have hX := card_activeX_le_four_mul_card_Q B hdeg
  have hZLink := card_activeZLink_le_28_mul_card_MX B hsimp
  have hSimp := card_activeSimplex2_le_28_mul_card_MX B hsimp
  nlinarith

/-- Bounds `|ShellVertex pcode M|` by `(M + 1) * |BoundaryX0Link pcode M|`. -/
lemma card_shellVertex_le (B : BundledCSSCode3D) (M : ℕ) :
    Fintype.card (ShellVertex B.code M) ≤ Fintype.card (BoundaryX0Link B.code M) * (M + 1) := by
  calc Fintype.card (ShellVertex B.code M)
    _ ≤ Fintype.card (BoundaryX0Link B.code M × Fin (M + 1)) := Fintype.card_subtype_le _
    _ = Fintype.card (BoundaryX0Link B.code M) * (M + 1) := by
        simp [Fintype.card_prod, Fintype.card_fin]

/-- Bounds `|RadialVertex pcode M|` by `|ShellVertex pcode M|`. -/
lemma card_radialVertex_le (B : BundledCSSCode3D) (M : ℕ) :
    Fintype.card (RadialVertex B.code M) ≤ Fintype.card (ShellVertex B.code M) :=
  Fintype.card_subtype_le _

/-- Bounds `|ShellSegment pcode M|` by `(M + 1) * (M + 1) * |ActiveZLink pcode|`. -/
lemma card_shellSegment_le (B : BundledCSSCode3D) (M : ℕ) :
    Fintype.card (ShellSegment B.code M) ≤ Fintype.card (ActiveZLink B.code) * (M + 1) * (M + 1) := by
  calc Fintype.card (ShellSegment B.code M)
    _ ≤ Fintype.card (ActiveZLink B.code × Fin (M + 1) × Fin (M + 1)) := Fintype.card_subtype_le _
    _ = Fintype.card (ActiveZLink B.code) * (M + 1) * (M + 1) := by
        simp [Fintype.card_prod, Fintype.card_fin, mul_assoc]

/-- Bounds the total cell count of `bdlRandomStepX B` by `bdlSingleStepFactor * bundledCellCount B`. -/
lemma bundledCellCount_bdlRandomStepX_le (B : BundledCSSCode3D)
    (hdeg : HasBoundedCheckDegree B 8 8 4 4)
    (hsimp : HasBoundedSimplexDegreeD B 32) :
    bundledCellCount (bdlRandomStepX B) ≤ bdlSingleStepFactor * bundledCellCount B := by
  let c := bdlLLLPerturbation B
  let pcode := bdlPerturbStep B.code bdlLambda c.1 c.2.1 c.2.2
  let M := bdlSubdivPred
  let B' : BundledCSSCode3D := { Q := B.Q, M_Z := B.M_Z, M_X := B.M_X, code := pcode }
  have hdeg' : HasBoundedCheckDegree B' 8 8 4 4 := hdeg
  have hsimp' : HasBoundedSimplexDegreeD B' 32 := hsimp
  have h_actZ : Fintype.card (ActiveZ pcode) ≤ 4 * Fintype.card B.Q :=
    card_activeZ_le_four_mul_card_Q B' hdeg'
  have h_actZLink : Fintype.card (ActiveZLink pcode) ≤ 32 * Fintype.card B.M_X :=
    card_activeZLink_le_28_mul_card_MX B' hsimp'
  have h_bxLink : Fintype.card (BoundaryX0Link pcode M) ≤
      4 * Fintype.card B.Q + 32 * (M + 1) * Fintype.card B.M_X :=
    card_boundaryX0Link_le B' M hdeg' hsimp'
  have h_sv : Fintype.card (ShellVertex pcode M) ≤ Fintype.card (BoundaryX0Link pcode M) * (M + 1) :=
    card_shellVertex_le B' M
  have h_rv : Fintype.card (RadialVertex pcode M) ≤ Fintype.card (ShellVertex pcode M) :=
    card_radialVertex_le B' M
  have h_seg : Fintype.card (ShellSegment pcode M) ≤ Fintype.card (ActiveZLink pcode) * (M + 1) * (M + 1) :=
    card_shellSegment_le B' M
  have h_sv_exp : Fintype.card (ShellVertex pcode M) ≤
      (4 * Fintype.card B.Q + 32 * (M + 1) * Fintype.card B.M_X) * (M + 1) :=
    h_sv.trans (Nat.mul_le_mul_right (M + 1) h_bxLink)
  have h_seg_exp : Fintype.card (ShellSegment pcode M) ≤
      32 * Fintype.card B.M_X * (M + 1) * (M + 1) :=
    h_seg.trans (Nat.mul_le_mul_right (M + 1) (Nat.mul_le_mul_right (M + 1) h_actZLink))
  have h_actZ_M : Fintype.card (ActiveZ pcode) * M ≤ 4 * Fintype.card B.Q * (M + 1) :=
    (Nat.mul_le_mul_left _ (Nat.le_succ M)).trans (Nat.mul_le_mul_right (M + 1) h_actZ)
  have h_actZ_M1 : Fintype.card (ActiveZ pcode) * (M + 1) ≤ 4 * Fintype.card B.Q * (M + 1) :=
    Nat.mul_le_mul_right (M + 1) h_actZ
  have h_actZLink_M1 : Fintype.card (ActiveZLink pcode) * (M + 1) ≤ 32 * Fintype.card B.M_X * (M + 1) :=
    Nat.mul_le_mul_right (M + 1) h_actZLink
  have h_Q : Fintype.card (bdlRandomStepX B).Q =
      Fintype.card (RadialVertex pcode M) * 3 +
      Fintype.card (ShellSegment pcode M) * 3 +
      Fintype.card (BoundaryX0Link pcode M) * 2 +
      (Fintype.card B.Q + Fintype.card (ActiveZ pcode) * M + Fintype.card (ActiveZ pcode)) * 3 := by
    change Fintype.card (((RadialVertex pcode M × Fin 3) ⊕ ((ShellSegment pcode M × Fin 3) ⊕ (BoundaryX0Link pcode M × Fin 2))) ⊕ ((B.Q ⊕ ((ActiveZ pcode × Fin M) ⊕ ActiveZ pcode)) × Fin 3)) = _
    simp only [Fintype.card_sum, Fintype.card_prod, Fintype.card_fin]
    ring
  have h_MZ : Fintype.card (bdlRandomStepX B).M_Z =
      Fintype.card (ShellSegment pcode M) * 3 +
      Fintype.card (ActiveZLink pcode) * (M + 1) * 2 +
      (Fintype.card (ActiveZ pcode) * (M + 1) * 3 + Fintype.card (ActiveZ pcode) * 2) +
      Fintype.card B.M_Z * 3 := by
    change Fintype.card (((ShellSegment pcode M × Fin 3) ⊕ (ActiveZLink pcode × Fin (M + 1) × Fin 2)) ⊕ (((ActiveZ pcode × Fin (M + 1) × Fin 3) ⊕ (ActiveZ pcode × Fin 2)) ⊕ (B.M_Z × Fin 3))) = _
    simp only [Fintype.card_sum, Fintype.card_prod, Fintype.card_fin]
    ring
  have h_MX : Fintype.card (bdlRandomStepX B).M_X =
      Fintype.card B.M_X * 3 + Fintype.card (ShellVertex pcode M) * 3 := by
    change Fintype.card ((B.M_X × Fin 3) ⊕ (ShellVertex pcode M × Fin 3)) = _
    simp only [Fintype.card_sum, Fintype.card_prod, Fintype.card_fin]
  have hM_eq : M + 1 = bdlSubdivM := bdlSubdivM_eq_succ
  have hM_ge : 2 ≤ M + 1 := by rw [hM_eq]; exact bdlSubdivM_ge_two
  have hM_sq : M + 1 ≤ (M + 1) ^ 2 := by nlinarith
  have h1_sq : 1 ≤ (M + 1) ^ 2 := by nlinarith
  have hQ_m2 : Fintype.card B.Q * (M + 1) ≤ Fintype.card B.Q * (M + 1) ^ 2 :=
    Nat.mul_le_mul_left _ hM_sq
  have hQ_1 : Fintype.card B.Q ≤ Fintype.card B.Q * (M + 1) ^ 2 := by
    simpa using Nat.mul_le_mul_left (Fintype.card B.Q) h1_sq
  have hMZ_1 : Fintype.card B.M_Z ≤ Fintype.card B.M_Z * (M + 1) ^ 2 := by
    simpa using Nat.mul_le_mul_left (Fintype.card B.M_Z) h1_sq
  have hMX_m2 : Fintype.card B.M_X * (M + 1) ≤ Fintype.card B.M_X * (M + 1) ^ 2 :=
    Nat.mul_le_mul_left _ hM_sq
  have hMX_1 : Fintype.card B.M_X ≤ Fintype.card B.M_X * (M + 1) ^ 2 := by
    simpa using Nat.mul_le_mul_left (Fintype.card B.M_X) h1_sq
  have h_sv_exp2 : Fintype.card (ShellVertex pcode M) ≤
      4 * (Fintype.card B.Q * (M + 1)) + 32 * (Fintype.card B.M_X * (M + 1) ^ 2) := by
    calc Fintype.card (ShellVertex pcode M)
        ≤ (4 * Fintype.card B.Q + 32 * (M + 1) * Fintype.card B.M_X) * (M + 1) := h_sv_exp
      _ = 4 * (Fintype.card B.Q * (M + 1)) + 32 * (Fintype.card B.M_X * (M + 1) ^ 2) := by ring
  have h_seg_exp2 : Fintype.card (ShellSegment pcode M) ≤
      32 * (Fintype.card B.M_X * (M + 1) ^ 2) := by
    calc Fintype.card (ShellSegment pcode M)
        ≤ 32 * Fintype.card B.M_X * (M + 1) * (M + 1) := h_seg_exp
      _ = 32 * (Fintype.card B.M_X * (M + 1) ^ 2) := by ring
  dsimp [bundledCellCount, bdlSingleStepFactor, _root_.bdlSingleStepFactor]
  rw [← hM_eq, h_Q, h_MZ, h_MX]
  linarith

/-- Evaluates `bundledCellCount` on the surface seed code to `9`. -/
lemma bundledCellCount_surfaceSeed : bundledCellCount bdlSurfaceSeedBundled = 9 := by
  dsimp [bundledCellCount, bdlSurfaceSeedBundled]
  simp

/-- Proves that `dualBundled` preserves `bundledCellCount`. -/
lemma bundledCellCount_dualBundled (B : BundledCSSCode3D) :
    bundledCellCount (dualBundled B) = bundledCellCount B := by
  dsimp [bundledCellCount, dualBundled]
  omega

/-- Bounds the total cell count after a combined `bdlRandomStepZ (bdlRandomStepX B)` step. -/
lemma bundledCellCount_bdlRandomStepZX_le (B : BundledCSSCode3D)
    (hov : HasBoundedCheckDegreeOverlap B) :
    bundledCellCount ((bdlRandomStepZ ∘ bdlRandomStepX) B) ≤
      bdlSingleStepFactor ^ 2 * bundledCellCount B := by
  have hdeg1 : HasBoundedCheckDegree B 8 8 4 4 := hov.1
  have hsimp1 : HasBoundedSimplexDegreeD B 32 :=
    hasBoundedSimplexDegreeD_32_of_hasBoundedCheckDegreeOverlap B hov
  have h_step1 := bundledCellCount_bdlRandomStepX_le B hdeg1 hsimp1
  have hov_X := bdlRandomStepX_preserves_bounded_check_degree_overlap B hov
  have hov_dualX := dualBundled_preserves_bounded_check_degree_overlap (bdlRandomStepX B) hov_X
  have hdeg2 : HasBoundedCheckDegree (dualBundled (bdlRandomStepX B)) 8 8 4 4 := hov_dualX.1
  have hsimp2 : HasBoundedSimplexDegreeD (dualBundled (bdlRandomStepX B)) 32 :=
    hasBoundedSimplexDegreeD_32_of_hasBoundedCheckDegreeOverlap (dualBundled (bdlRandomStepX B)) hov_dualX
  have h_step2 := bundledCellCount_bdlRandomStepX_le (dualBundled (bdlRandomStepX B)) hdeg2 hsimp2
  dsimp [Function.comp, bdlRandomStepZ, bdlStepZ]
  rw [bundledCellCount_dualBundled]
  rw [bundledCellCount_dualBundled] at h_step2
  nlinarith

/-- Exponential upper bound on `bundledCellCount` after `n` iterated BDL thickening rounds. -/
lemma bundledCellCount_iterated_le : ∀ (n : ℕ),
    bundledCellCount ((bdlRandomStepZ ∘ bdlRandomStepX)^[n] bdlSurfaceSeedBundled) ≤
      9 * (bdlSingleStepFactor ^ 2) ^ n
  | 0 => by simp [bundledCellCount_surfaceSeed]
  | n + 1 => by
      rw [Function.iterate_succ_apply']
      have hov := hasBoundedCheckDegreeOverlap_bdlIterated n
      have h_step := bundledCellCount_bdlRandomStepZX_le
        ((bdlRandomStepZ ∘ bdlRandomStepX)^[n] bdlSurfaceSeedBundled) hov
      have h_ih := bundledCellCount_iterated_le n
      calc bundledCellCount ((bdlRandomStepZ ∘ bdlRandomStepX)
            ((bdlRandomStepZ ∘ bdlRandomStepX)^[n] bdlSurfaceSeedBundled))
        _ ≤ bdlSingleStepFactor ^ 2 *
            bundledCellCount ((bdlRandomStepZ ∘ bdlRandomStepX)^[n] bdlSurfaceSeedBundled) := h_step
        _ ≤ bdlSingleStepFactor ^ 2 * (9 * (bdlSingleStepFactor ^ 2) ^ n) :=
            Nat.mul_le_mul_left _ h_ih
        _ = 9 * (bdlSingleStepFactor ^ 2) ^ (n + 1) := by ring

/-- Bounds `numQubits (bdlRandomCode k)` by `bdlRandomStepFactor ^ (k + 1)`. -/
lemma numQubits_bdlRandomCode_le_stepFactor_pow (k : ℕ) :
    numQubits (bdlRandomCode k) ≤ (bdlRandomStepFactor : ℝ) ^ (k + 1) := by
  have h_q_le : Fintype.card (bdlRandomBundled k).Q ≤ bundledCellCount (bdlRandomBundled k) := by
    dsimp [bundledCellCount]; omega
  have h_cell := bundledCellCount_iterated_le (k + 1)
  have h_9_pow : 9 * (bdlSingleStepFactor ^ 2) ^ (k + 1) ≤ bdlRandomStepFactor ^ (k + 1) := by
    dsimp [bdlRandomStepFactor]
    rw [mul_pow]
    have h9 : 9 ≤ 9 ^ (k + 1) := by
      calc 9 = 9 ^ 1 := (pow_one 9).symm
        _ ≤ 9 ^ (k + 1) := Nat.pow_le_pow_right (by norm_num) (Nat.succ_pos k)
    exact Nat.mul_le_mul_right _ h9
  have h_nat : Fintype.card (bdlRandomBundled k).Q ≤ bdlRandomStepFactor ^ (k + 1) :=
    h_q_le.trans (h_cell.trans h_9_pow)
  dsimp [numQubits, bdlRandomCode, bdlWeldedCode]
  exact_mod_cast h_nat

/-- Proves that `dualCode` preserves `numQubits`. -/
lemma numQubits_dualCode_eq {Q M_Z M_X : Type}
    [Fintype Q] [DecidableEq Q] [Fintype M_Z] [DecidableEq M_Z] [Fintype M_X] [DecidableEq M_X]
    (code : CSSCode3D Q M_Z M_X) :
    numQubits (dualCode code) = numQubits code := rfl

end WeldedHierarchy
