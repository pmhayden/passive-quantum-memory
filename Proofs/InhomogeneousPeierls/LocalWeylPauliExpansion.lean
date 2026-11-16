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

import Proofs.InhomogeneousPeierls.StaticCSSFrustrationFree
import Proofs.F2TQOToOperatorTQO

/-!
# Local Weyl-Pauli Operator Expansion and Hilbert-Space Trace Identities

Proves that every continuous linear operator supported on a finite lattice region admits an exact expansion in the local Weyl-Pauli Z/X basis (`exists_weylPauli_expansion_of_isSupportedOn`). Develops cyclicity, positivity, and anticommutation vanishing lemmas for `complexTrace` and `hilbertTrace` (`sandwich_eq_zero_of_anticomm`, `one_le_hilbertTrace_of_isStarProjection_ne_zero`).

## References

* Part I, Section 3.1 (`subsec:rca-trinity`), Proposition 3.3 (`prop:trinity-equivalence`)
* Part I, Section 5.4 (`subsec:safe-decoded-observables`), Proposition 5.7 (`prop:safe-subspace-immunity`)
-/

noncomputable section

open scoped Classical BigOperators InnerProduct ComplexConjugate
open ContinuousLinearMap

set_option linter.constructorNameAsVariable false
set_option maxRecDepth 200000

/-! ## 1. Finite-Region Weyl–Pauli Fourier Expansion on `UniformSite3D L (CodeSlotConfig q_code)` -/

private lemma pauliPhase_zero_right {Q : Type*} [Fintype Q] (a : Q → ZMod 2) :
    pauliPhase a 0 = 1 := by
  simp [pauliPhase]

private lemma sum_pauliPhase_eq {ι : Type} [Fintype ι] [DecidableEq ι] (z : ι → ZMod 2) :
    (∑ a : ι → ZMod 2, pauliPhase a z) =
      if z = 0 then (Fintype.card (ι → ZMod 2) : ℂ) else 0 := by
  split_ifs with hz
  · subst hz
    simp [pauliPhase_zero_right]
  · have h_ex : ∃ q₀ : ι, z q₀ ≠ 0 := by
      by_contra! h_all
      exact hz (funext h_all)
    rcases h_ex with ⟨q₀, hzq₀⟩
    have hzq₀_one : z q₀ = 1 := zmod2_ne_zero_iff_eq_one _ hzq₀
    let e₀ : ι → ZMod 2 := fun q => if q = q₀ then 1 else 0
    have he₀_phase : pauliPhase e₀ z = -1 := by
      dsimp [pauliPhase, e₀]
      have h_sum : (∑ q : ι, (if q = q₀ then (1 : ZMod 2) else 0) * z q) = z q₀ := by
        simp
      rw [h_sum, hzq₀_one]
      have h10 : (1 : ZMod 2) ≠ 0 := by decide
      rw [if_neg h10]
    have h_shift :
        (∑ a : ι → ZMod 2, pauliPhase a z) =
          -(∑ a : ι → ZMod 2, pauliPhase a z) := by
      conv_lhs => rw [← Equiv.sum_comp (Equiv.addRight e₀) (fun a => pauliPhase a z)]
      rw [← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl (fun a _ => ?_)
      change pauliPhase (a + e₀) z = -pauliPhase a z
      rw [pauliPhase_add_left, he₀_phase, mul_neg_one]
    have h_two : (2 : ℂ) * (∑ a : ι → ZMod 2, pauliPhase a z) = 0 := by
      linear_combination h_shift
    exact (mul_eq_zero.mp h_two).resolve_left two_ne_zero

private abbrev SubSlot3D (L q_code : ℕ) (A : Finset (Box3D L)) : Type :=
  ↥A × Fin q_code

private def extSlotChain {L q_code : ℕ} (A : Finset (Box3D L))
    (a : SubSlot3D L q_code A → ZMod 2) : BoxSlot3D L q_code → ZMod 2 :=
  fun p => if hp : p.1 ∈ A then a (⟨p.1, hp⟩, p.2) else 0

private lemma boxSlotChainSupportedIn_extSlotChain {L q_code : ℕ} (A : Finset (Box3D L))
    (a : SubSlot3D L q_code A → ZMod 2) :
    BoxSlotChainSupportedIn (extSlotChain A a) A := by
  intro p hp_ne
  dsimp [extSlotChain] at hp_ne
  split_ifs at hp_ne with hpA
  · exact hpA
  · exact absurd rfl hp_ne

private def localSlotConfigToSub {L q_code : ℕ} (A : Finset (Box3D L))
    (α : LocalConfig (UniformSite3D L (CodeSlotConfig q_code)) A) :
    SubSlot3D L q_code A → ZMod 2 :=
  fun p => boolToZMod2 (α p.1 p.2)

private lemma localSlotConfigToSub_injective {L q_code : ℕ} (A : Finset (Box3D L)) :
    Function.Injective (localSlotConfigToSub (L := L) (q_code := q_code) A) := by
  intro α β h
  funext x s
  have hxs := congr_fun h (x, s)
  dsimp [localSlotConfigToSub] at hxs
  revert hxs
  cases α x s <;> cases β x s <;> decide

private lemma pauliPhase_extSlotChain {L q_code : ℕ} (A : Finset (Box3D L))
    (a : SubSlot3D L q_code A → ZMod 2)
    (ψ : ManyBodyConfig (UniformSite3D L (CodeSlotConfig q_code))) :
    pauliPhase (extSlotChain A a) (codeConfigBits ψ) =
      pauliPhase a (localSlotConfigToSub A (restrictConfig A ψ)) := by
  dsimp [pauliPhase]
  have h_sum :
      (∑ p : BoxSlot3D L q_code, extSlotChain A a p * codeConfigBits ψ p) =
        ∑ p : SubSlot3D L q_code A,
          a p * localSlotConfigToSub A (restrictConfig A ψ) p := by
    rw [Fintype.sum_prod_type, Fintype.sum_prod_type]
    rw [← Finset.sum_subset (Finset.subset_univ A)]
    · rw [← Finset.sum_attach A]
      refine Finset.sum_congr rfl (fun vA _ => Finset.sum_congr rfl (fun s _ => ?_))
      simp [extSlotChain, codeConfigBits, localSlotConfigToSub, restrictConfig, vA.2]
    · intro v _ hv_not
      refine Finset.sum_eq_zero (fun s _ => ?_)
      dsimp [extSlotChain]
      rw [dif_neg hv_not, zero_mul]
  rw [h_sum]

private def localDiffSlotChain {L q_code : ℕ} (A : Finset (Box3D L))
    (α β : LocalConfig (UniformSite3D L (CodeSlotConfig q_code)) A) :
    BoxSlot3D L q_code → ZMod 2 :=
  extSlotChain A (localSlotConfigToSub A α + localSlotConfigToSub A β)

private lemma boxSlotChainSupportedIn_localDiffSlotChain {L q_code : ℕ} (A : Finset (Box3D L))
    (α β : LocalConfig (UniformSite3D L (CodeSlotConfig q_code)) A) :
    BoxSlotChainSupportedIn (localDiffSlotChain A α β) A :=
  boxSlotChainSupportedIn_extSlotChain A _

private lemma flipCodeConfig_localDiffSlotChain {L q_code : ℕ} (A : Finset (Box3D L))
    (α β : LocalConfig (UniformSite3D L (CodeSlotConfig q_code)) A)
    (ψ : ManyBodyConfig (UniformSite3D L (CodeSlotConfig q_code)))
    (hβ : restrictConfig A ψ = β) :
    flipCodeConfig (localDiffSlotChain A α β) ψ = spliceConfig A α ψ := by
  funext v s
  dsimp [flipCodeConfig, spliceConfig, localDiffSlotChain, extSlotChain]
  by_cases hvA : v ∈ A
  · rw [dif_pos hvA, dif_pos hvA]
    dsimp [localSlotConfigToSub]
    have hβ_eq : β ⟨v, hvA⟩ s = ψ v s := by
      rw [← hβ]
      rfl
    rw [hβ_eq]
    cases ψ v s <;> cases α ⟨v, hvA⟩ s <;> rfl
  · rw [dif_neg hvA, dif_neg hvA]
    dsimp [zmod2ToBool]
    cases ψ v s <;> rfl

/-- Any operator `O_A` supported on `A : Finset (Box3D L)` expands as a finite linear combination
    of Weyl–Pauli operators `weylPauliZ a * weylPauliX b` with `a, b` supported on `A`. -/
theorem exists_weylPauli_expansion_of_isSupportedOn {L q_code : ℕ}
    (A : Finset (Box3D L))
    {O_A : ManyBodyHilbertSpace (UniformSite3D L (CodeSlotConfig q_code)) →L[ℂ]
      ManyBodyHilbertSpace (UniformSite3D L (CodeSlotConfig q_code))}
    (hO : IsSupportedOn (UniformSite3D L (CodeSlotConfig q_code)) A O_A) :
    ∃ (ι : Type) (_ : Fintype ι) (w : ι → ℂ)
      (a_fam b_fam : ι → BoxSlot3D L q_code → ZMod 2),
      (∀ i : ι, BoxSlotChainSupportedIn (a_fam i) A) ∧
      (∀ i : ι, BoxSlotChainSupportedIn (b_fam i) A) ∧
      O_A = ∑ i : ι, w i • (weylPauliZ (a_fam i) * weylPauliX (b_fam i)) := by
  rcases hO with ⟨O_loc, rfl⟩
  let SubQ := SubSlot3D L q_code A
  let Loc := LocalConfig (UniformSite3D L (CodeSlotConfig q_code)) A
  let ι := (Loc × Loc) × (SubQ → ZMod 2)
  let N : ℂ := (Fintype.card (SubQ → ZMod 2) : ℂ)
  have hN_ne : N ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  refine ⟨ι, inferInstance,
    fun i => (O_loc (deltaLp i.1.1)).ofLp i.1.2 *
      N⁻¹ * pauliPhase i.2 (localSlotConfigToSub A i.1.2),
    fun i => extSlotChain A i.2,
    fun i => localDiffSlotChain A i.1.1 i.1.2,
    fun i => boxSlotChainSupportedIn_extSlotChain A i.2,
    fun i => boxSlotChainSupportedIn_localDiffSlotChain A i.1.1 i.1.2,
    ?_⟩
  ext φ ψ
  rw [ContinuousLinearMap.sum_apply, ofLp_sum]
  change (O_loc (WithLp.toLp 2 fun α => φ.ofLp (spliceConfig A α ψ))).ofLp (restrictConfig A ψ) = _
  rw [clm_apply_ofLp_eq_sum O_loc]
  conv_rhs => rw [Fintype.sum_prod_type, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl (fun α _ => ?_)
  have h_inner_sum :
      ∀ β : Loc,
        (∑ a : SubQ → ZMod 2,
          ((((O_loc (deltaLp α)).ofLp β *
            N⁻¹ * pauliPhase a (localSlotConfigToSub A β)) •
            (weylPauliZ (extSlotChain A a) *
              weylPauliX (localDiffSlotChain A α β))) φ).ofLp ψ) =
        if β = restrictConfig A ψ then
          φ.ofLp (spliceConfig A α ψ) * (O_loc (deltaLp α)).ofLp β
        else 0 := by
    intro β
    have h_term :
        ∀ a : SubQ → ZMod 2,
          ((((O_loc (deltaLp α)).ofLp β *
            N⁻¹ * pauliPhase a (localSlotConfigToSub A β)) •
            (weylPauliZ (extSlotChain A a) *
              weylPauliX (localDiffSlotChain A α β))) φ).ofLp ψ =
          ((O_loc (deltaLp α)).ofLp β *
            N⁻¹ * φ.ofLp (flipCodeConfig (localDiffSlotChain A α β) ψ)) *
            pauliPhase a (localSlotConfigToSub A (restrictConfig A ψ) +
              localSlotConfigToSub A β) := by
      intro a
      change ((O_loc (deltaLp α)).ofLp β *
          N⁻¹ * pauliPhase a (localSlotConfigToSub A β)) *
          (pauliPhase (extSlotChain A a) (codeConfigBits ψ) *
            φ.ofLp (flipCodeConfig (localDiffSlotChain A α β) ψ)) = _
      rw [pauliPhase_extSlotChain A a ψ, pauliPhase_add_right]
      ring
    simp_rw [h_term, ← Finset.mul_sum, sum_pauliPhase_eq]
    have h_zero_iff :
        localSlotConfigToSub A (restrictConfig A ψ) +
          localSlotConfigToSub A β = 0 ↔
        β = restrictConfig A ψ := by
      constructor
      · intro h_add0
        have h_eq :
            localSlotConfigToSub A β =
              localSlotConfigToSub A (restrictConfig A ψ) := by
          funext qA
          have hq := congr_fun h_add0 qA
          (try dsimp at hq)
          calc localSlotConfigToSub A β qA
            _ = (localSlotConfigToSub A (restrictConfig A ψ) qA +
                  localSlotConfigToSub A (restrictConfig A ψ) qA) +
                localSlotConfigToSub A β qA := by
              rw [zmod2_add_self, zero_add]
            _ = localSlotConfigToSub A (restrictConfig A ψ) qA +
                (localSlotConfigToSub A (restrictConfig A ψ) qA +
                  localSlotConfigToSub A β qA) := by
              abel
            _ = localSlotConfigToSub A (restrictConfig A ψ) qA := by
              rw [hq, add_zero]
        exact localSlotConfigToSub_injective A h_eq
      · intro h_eq
        subst h_eq
        funext qA
        exact zmod2_add_self _
    by_cases hβ : β = restrictConfig A ψ
    · rw [if_pos (h_zero_iff.mpr hβ), if_pos hβ]
      subst hβ
      rw [flipCodeConfig_localDiffSlotChain A α (restrictConfig A ψ) ψ rfl]
      change ((O_loc (deltaLp α)).ofLp (restrictConfig A ψ) *
        N⁻¹ * φ.ofLp (spliceConfig A α ψ)) * N = _
      calc ((O_loc (deltaLp α)).ofLp (restrictConfig A ψ) *
            N⁻¹ * φ.ofLp (spliceConfig A α ψ)) * N
        _ = (N⁻¹ * N) * φ.ofLp (spliceConfig A α ψ) *
            (O_loc (deltaLp α)).ofLp (restrictConfig A ψ) := by ring
        _ = φ.ofLp (spliceConfig A α ψ) *
            (O_loc (deltaLp α)).ofLp (restrictConfig A ψ) := by
          rw [inv_mul_cancel₀ hN_ne, one_mul]
    · rw [if_neg (mt h_zero_iff.mp hβ), if_neg hβ, mul_zero]
  dsimp only
  rw [Finset.sum_congr rfl (fun β _ => h_inner_sum β),
    Finset.sum_ite_eq', if_pos (Finset.mem_univ (restrictConfig A ψ))]

/-! ## 2. Trace Helpers and Single-Pauli Operator TQO Step -/

lemma inner_basisVecGlobal_left {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    (σ : ManyBodyConfig Site) (v : ManyBodyHilbertSpace Site) :
    inner ℂ (basisVecGlobal Site σ) v = v.ofLp σ := by
  simp [basisVecGlobal, PiLp.inner_apply, apply_ite conj, mul_comm]

lemma basisVecGlobal_eq_deltaLp {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    (σ : ManyBodyConfig Site) :
    basisVecGlobal Site σ = deltaLp σ := by
  ext τ
  simp [basisVecGlobal, deltaLp, eq_comm]

lemma one_le_hilbertTrace_of_isStarProjection_ne_zero {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    {Q : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site}
    (hQ : IsStarProjection Q) (hQ_ne : Q ≠ 0) :
    (1 : ℝ) ≤ hilbertTrace Q := by
  have h_ex : ∃ ω : ManyBodyConfig Site,
      Q (opEigenbasis Q hQ.isSelfAdjoint ω) ≠ 0 := by
    by_contra! h_all
    apply hQ_ne
    have h_id := onb_sum_ketBra_eq_one (opEigenbasis Q hQ.isSelfAdjoint)
      (opEigenbasis_orthonormal Q hQ.isSelfAdjoint)
      (opEigenbasis_parseval Q hQ.isSelfAdjoint)
    ext ψ : 1
    calc Q ψ
      _ = (Q * 1) ψ := by rw [mul_one]
      _ = (Q * ∑ ω : ManyBodyConfig Site, rankOneKetBra (opEigenbasis Q hQ.isSelfAdjoint ω)) ψ := by
        rw [h_id]
      _ = ∑ ω : ManyBodyConfig Site,
            Q (rankOneKetBra (opEigenbasis Q hQ.isSelfAdjoint ω) ψ) := by
        simp [Finset.mul_sum, ContinuousLinearMap.sum_apply]
      _ = 0 := by
        refine Finset.sum_eq_zero (fun ω _ => ?_)
        rw [rankOneKetBra_apply, map_smul, h_all ω, smul_zero]
  rcases h_ex with ⟨ω₀, hω₀⟩
  rw [hilbertTrace_eq_sum_opEigenbasis Q hQ.isSelfAdjoint Q]
  have h_nonneg : ∀ ω, 0 ≤ RCLike.re (inner ℂ (opEigenbasis Q hQ.isSelfAdjoint ω)
      (Q (opEigenbasis Q hQ.isSelfAdjoint ω))) :=
    fun ω => hQ.re_inner_nonneg _
  have hω₀_one : RCLike.re (inner ℂ (opEigenbasis Q hQ.isSelfAdjoint ω₀)
      (Q (opEigenbasis Q hQ.isSelfAdjoint ω₀))) = 1 := by
    let v₀ := opEigenbasis Q hQ.isSelfAdjoint ω₀
    have h_eig : Q v₀ = (opEigenvalues Q hQ.isSelfAdjoint ω₀ : ℂ) • v₀ :=
      opEigenbasis_apply_H Q hQ.isSelfAdjoint ω₀
    let lam := opEigenvalues Q hQ.isSelfAdjoint ω₀
    have h_lam_ne : (lam : ℂ) ≠ 0 := by
      intro h0
      apply hω₀
      change Q v₀ = 0
      rw [h_eig, h0, zero_smul]
    have h_v_ne : v₀ ≠ 0 := by
      intro h0
      apply hω₀
      change Q v₀ = 0
      rw [h0, map_zero]
    have h_idem : Q (Q v₀) = Q v₀ := isStarProjection_apply_self hQ v₀
    rw [h_eig, map_smul, h_eig, smul_smul] at h_idem
    have h_sq : (lam : ℂ) * (lam : ℂ) = (lam : ℂ) := by
      have h_sub : ((lam : ℂ) * (lam : ℂ) - (lam : ℂ)) • v₀ = 0 := by
        rw [sub_smul, h_idem, sub_self]
      exact sub_eq_zero.mp ((smul_eq_zero.mp h_sub).resolve_right h_v_ne)
    have h_lam_one : (lam : ℂ) = 1 :=
      mul_right_cancel₀ h_lam_ne (h_sq.trans (one_mul _).symm)
    have h_Qv : Q v₀ = v₀ := by rw [h_eig, h_lam_one, one_smul]
    have h_inner : inner ℂ v₀ v₀ = 1 := by
      have h_onb := opEigenbasis_orthonormal Q hQ.isSelfAdjoint ω₀ ω₀
      simpa using h_onb
    change RCLike.re (inner ℂ v₀ (Q v₀)) = 1
    rw [h_Qv, h_inner]
    rfl
  calc (1 : ℝ)
    _ = RCLike.re (inner ℂ (opEigenbasis Q hQ.isSelfAdjoint ω₀)
          (Q (opEigenbasis Q hQ.isSelfAdjoint ω₀))) := hω₀_one.symm
    _ ≤ ∑ ω, RCLike.re (inner ℂ (opEigenbasis Q hQ.isSelfAdjoint ω)
          (Q (opEigenbasis Q hQ.isSelfAdjoint ω))) :=
      Finset.single_le_sum (fun ω _ => h_nonneg ω) (Finset.mem_univ ω₀)

def complexTrace {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    (M : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site) : ℂ :=
  ∑ σ : ManyBodyConfig Site, (M (basisVecGlobal Site σ)).ofLp σ

lemma complexTrace_neg {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    (M : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site) :
    complexTrace (-M) = -complexTrace M := by
  unfold complexTrace
  rw [← Finset.sum_neg_distrib]
  rfl

lemma complexTrace_smul {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    (c : ℂ) (M : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site) :
    complexTrace (c • M) = c * complexTrace M := by
  unfold complexTrace
  rw [Finset.mul_sum]
  rfl

lemma complexTrace_sum {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    {ι : Type*} (s : Finset ι)
    (f : ι → (ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site)) :
    complexTrace (∑ i ∈ s, f i) = ∑ i ∈ s, complexTrace (f i) := by
  unfold complexTrace
  have h_term : ∀ σ : ManyBodyConfig Site,
      ((∑ i ∈ s, f i) (basisVecGlobal Site σ)).ofLp σ =
        ∑ i ∈ s, (f i (basisVecGlobal Site σ)).ofLp σ := by
    intro σ
    rw [ContinuousLinearMap.sum_apply, ofLp_sum]
  simp_rw [h_term]
  exact Finset.sum_comm

lemma complexTrace_mul_comm {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    (A B : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site) :
    complexTrace (A * B) = complexTrace (B * A) := by
  unfold complexTrace
  have h_expand : ∀ (C D_op : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site)
      (ψ : ManyBodyConfig Site),
      ((C * D_op) (basisVecGlobal Site ψ)).ofLp ψ =
        ∑ τ : ManyBodyConfig Site,
          (D_op (basisVecGlobal Site ψ)).ofLp τ * (C (basisVecGlobal Site τ)).ofLp ψ := by
    intro C D_op ψ
    change (C (D_op (basisVecGlobal Site ψ))).ofLp ψ = _
    rw [clm_apply_ofLp_eq_sum C (D_op (basisVecGlobal Site ψ)) ψ]
    refine Finset.sum_congr rfl (fun τ _ => ?_)
    rw [basisVecGlobal_eq_deltaLp τ]
  simp_rw [h_expand A B, h_expand B A]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun τ _ => Finset.sum_congr rfl (fun ψ _ => ?_))
  rw [mul_comm]

lemma re_complexTrace {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    (M : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site) :
    (complexTrace M).re = hilbertTrace M := by
  unfold complexTrace hilbertTrace
  rw [Complex.re_sum]
  refine Finset.sum_congr rfl (fun σ _ => ?_)
  rw [inner_basisVecGlobal_left]
  rfl

lemma complexTrace_of_isStarProjection {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    {Q : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site}
    (hQ : IsStarProjection Q) :
    complexTrace Q = (hilbertTrace Q : ℂ) := by
  apply Complex.ext
  · rw [re_complexTrace, Complex.ofReal_re]
  · rw [Complex.ofReal_im]
    unfold complexTrace
    rw [Complex.im_sum]
    refine Finset.sum_eq_zero (fun σ _ => ?_)
    rw [← inner_basisVecGlobal_left σ (Q (basisVecGlobal Site σ))]
    have h_conj : (starRingEnd ℂ) (inner ℂ (basisVecGlobal Site σ) (Q (basisVecGlobal Site σ))) =
        inner ℂ (basisVecGlobal Site σ) (Q (basisVecGlobal Site σ)) := by
      have hQ_adj : adjoint Q = Q := hQ.isSelfAdjoint.star_eq
      rw [inner_conj_symm, ← ContinuousLinearMap.adjoint_inner_left, hQ_adj]
    have h_im := congrArg Complex.im h_conj
    simp only [Complex.conj_im] at h_im
    linarith

lemma sandwich_eq_zero_of_anticomm {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E]
    {P U W : E →L[ℂ] E} (hPU : P * U = P) (hUP : U * P = P)
    (h_anti : U * W * U = -W) :
    P * W * P = 0 := by
  have h_eq : P * W * P = -(P * W * P) := by
    calc P * W * P
      _ = (P * U) * W * (U * P) := by rw [hPU, hUP]
      _ = P * (U * W * U) * P := by simp only [mul_assoc]
      _ = -(P * W * P) := by rw [h_anti, mul_neg, neg_mul]
  have h_two : (2 : ℂ) • (P * W * P) = 0 := by
    calc (2 : ℂ) • (P * W * P)
      _ = P * W * P + P * W * P := two_smul ℂ (P * W * P)
      _ = P * W * P + -(P * W * P) := congrArg (P * W * P + ·) h_eq
      _ = 0 := add_neg_cancel (P * W * P)
  have h2_ne : (2 : ℂ) ≠ 0 := by norm_num
  exact (smul_eq_zero.mp h_two).resolve_left h2_ne

lemma complexTrace_mul_eq_zero_of_anticomm {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    {Q U W : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site}
    (hU_sq : U * U = 1) (hUQ : Commute U Q) (h_anti : U * W * U = -W) :
    complexTrace (W * Q) = 0 := by
  have h_tr : complexTrace (W * Q) = -complexTrace (W * Q) := by
    calc complexTrace (W * Q)
      _ = complexTrace (W * Q * (U * U)) := by rw [hU_sq, mul_one]
      _ = complexTrace (U * (W * Q * U)) := by
        rw [← mul_assoc (W * Q) U U, complexTrace_mul_comm (W * Q * U) U]
      _ = complexTrace ((U * W * U) * Q) := by
        have h_assoc : U * (W * Q * U) = (U * W * U) * Q := by
          calc U * (W * Q * U)
            _ = U * W * (Q * U) := by simp only [mul_assoc]
            _ = U * W * (U * Q) := by rw [hUQ.symm.eq]
            _ = (U * W * U) * Q := by simp only [mul_assoc]
        rw [h_assoc]
      _ = -complexTrace (W * Q) := by
        rw [h_anti, neg_mul W Q, complexTrace_neg]
  linear_combination (1 / 2 : ℂ) * h_tr

def localUnitOp {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    (A : Finset (BoxD D L)) (α β : LocalConfig Site A) :
    LocalHilbertSpace Site A →L[ℂ] LocalHilbertSpace Site A :=
  LinearMap.toContinuousLinearMap
    { toFun := fun φ_A => WithLp.toLp 2 (fun β' => if β' = β then φ_A.ofLp α else 0)
      map_add' := fun φ₁ φ₂ => by
        ext β'
        change (if β' = β then φ₁.ofLp α + φ₂.ofLp α else 0) =
          (if β' = β then φ₁.ofLp α else 0) + (if β' = β then φ₂.ofLp α else 0)
        split_ifs <;> ring
      map_smul' := fun c φ => by
        ext β'
        change (if β' = β then c * φ.ofLp α else 0) =
          c * (if β' = β then φ.ofLp α else 0)
        split_ifs <;> ring }

lemma sum_partialTraceEntry_eq_complexTrace {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    (A : Finset (BoxD D L))
    (ρ : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site)
    (α β : LocalConfig Site A) :
    (∑ γ : LocalConfig Site (Finset.univ \ A), partialTraceEntry Site A ρ γ α β) =
      complexTrace (cylinderOp Site A (localUnitOp A α β) * ρ) := by
  unfold complexTrace
  rw [← (configEquiv (Site := Site) A).sum_comp]
  rw [Fintype.sum_prod_type, Finset.sum_comm]
  refine Finset.sum_congr rfl (fun γ _ => ?_)
  have h_term : ∀ β' : LocalConfig Site A,
      ((cylinderOp Site A (localUnitOp A α β) * ρ)
        (basisVecGlobal Site (combineConfig A β' γ))).ofLp (combineConfig A β' γ) =
      if β' = β then partialTraceEntry Site A ρ γ α β else 0 := by
    intro β'
    change (cylinderOp Site A (localUnitOp A α β)
      (ρ (basisVecGlobal Site (combineConfig A β' γ)))).ofLp (combineConfig A β' γ) = _
    rw [cylinderOp_apply_combineConfig]
    change (if β' = β then (sliceLp A γ (ρ (basisVecGlobal Site (combineConfig A β' γ)))).ofLp α else 0) = _
    by_cases hβ : β' = β
    · subst hβ
      rw [if_pos rfl, if_pos rfl]
      rfl
    · rw [if_neg hβ, if_neg hβ]
  dsimp only [configEquiv, Equiv.coe_fn_mk]
  rw [Finset.sum_congr rfl (fun β' _ => h_term β'),
    Finset.sum_ite_eq', if_pos (Finset.mem_univ β)]

lemma hilbertTrace_adjoint_mul_self_eq_zero_iff {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    (M : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site) :
    hilbertTrace (M† * M) = 0 ↔ M = 0 := by
  constructor
  · intro h_tr
    unfold hilbertTrace at h_tr
    have h_term : ∀ ψ : ManyBodyConfig Site,
        RCLike.re (inner ℂ (basisVecGlobal Site ψ) ((M† * M) (basisVecGlobal Site ψ))) =
          ‖M (basisVecGlobal Site ψ)‖ ^ 2 := by
      intro ψ
      rw [ContinuousLinearMap.mul_apply, ContinuousLinearMap.adjoint_inner_right,
        inner_self_eq_norm_sq]
    simp_rw [h_term] at h_tr
    have h_all := (Finset.sum_eq_zero_iff_of_nonneg (fun ψ _ => sq_nonneg _)).mp h_tr
    ext φ σ
    rw [clm_apply_ofLp_eq_sum M φ σ]
    refine Finset.sum_eq_zero (fun ψ _ => ?_)
    have hψ : M (deltaLp ψ) = 0 := by
      rw [← basisVecGlobal_eq_deltaLp ψ]
      exact norm_eq_zero.mp (sq_eq_zero_iff.mp (h_all ψ (Finset.mem_univ ψ)))
    rw [hψ]
    exact mul_zero _
  · intro h0
    rw [h0, mul_zero]
    unfold hilbertTrace
    simp

lemma hilbertTrace_adjoint_mul_self_mul_proj {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    (O Q : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site)
    (hQ : IsStarProjection Q) :
    hilbertTrace (O† * O * Q) = hilbertTrace ((O * Q)† * (O * Q)) := by
  have hQ_sa : Q† = Q := hQ.isSelfAdjoint.star_eq
  have hQ_id : Q * Q = Q := hQ.isIdempotentElem.eq
  have h_lhs : O† * O * Q = (O† * O * Q†) * Q := by
    rw [hQ_sa, mul_assoc (O† * O) Q Q, hQ_id]
  have h_rhs : Q * (O† * O * Q†) = (O * Q)† * (O * Q) := by
    have h_adj : (O * Q)† = Q† * O† := star_mul O Q
    rw [h_adj, hQ_sa]
    simp only [mul_assoc]
  rw [h_lhs, ← re_complexTrace, complexTrace_mul_comm (O† * O * Q†) Q, re_complexTrace, h_rhs]

lemma clm_sum_smul {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    {ι : Type*} (s : Finset ι) (f : ι → ℂ) (A : E →L[ℂ] E) :
    (∑ i ∈ s, f i) • A = ∑ i ∈ s, f i • A := by
  ext φ
  simp [ContinuousLinearMap.sum_apply, Finset.sum_smul]

lemma clm_sandwich_smul {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (P X : E →L[ℂ] E) (w c : ℂ) (h : P * X * P = c • P) :
    P * (w • X) * P = (w * c) • P := by
  have h1 : P * (w • X) * P = w • (P * X * P) := by
    ext φ
    simp
  rw [h1, h, smul_smul]

lemma conjugation_neg_of_weylPauliZ_anticomm {L q_code : ℕ}
    (u a b : BoxSlot3D L q_code → ZMod 2)
    (h_anti : (∑ p : BoxSlot3D L q_code, u p * b p) = 1) :
    weylPauliZ u * (weylPauliZ a * weylPauliX b) * weylPauliZ u =
      -(weylPauliZ a * weylPauliX b) := by
  have h1 : weylPauliZ u * weylPauliZ a = weylPauliZ a * weylPauliZ u :=
    (weylPauliZ_comm u a).eq
  have h2 : weylPauliX b * weylPauliZ u = -(weylPauliZ u * weylPauliX b) :=
    weylPauliX_anticomm_weylPauliZ_of_symplectic_one u b h_anti
  calc weylPauliZ u * (weylPauliZ a * weylPauliX b) * weylPauliZ u
    _ = (weylPauliZ u * weylPauliZ a) * (weylPauliX b * weylPauliZ u) := by
      simp only [mul_assoc]
    _ = (weylPauliZ a * weylPauliZ u) * (-(weylPauliZ u * weylPauliX b)) := by
      rw [h1, h2]
    _ = -(weylPauliZ a * (weylPauliZ u * weylPauliZ u) * weylPauliX b) := by
      rw [mul_neg (weylPauliZ a * weylPauliZ u) (weylPauliZ u * weylPauliX b)]
      simp only [mul_assoc]
    _ = -(weylPauliZ a * weylPauliX b) := by
      rw [weylPauliZ_sq_eq_one, mul_one]

lemma conjugation_neg_of_weylPauliX_anticomm {L q_code : ℕ}
    (u a b : BoxSlot3D L q_code → ZMod 2)
    (h_anti : (∑ p : BoxSlot3D L q_code, a p * u p) = 1) :
    weylPauliX u * (weylPauliZ a * weylPauliX b) * weylPauliX u =
      -(weylPauliZ a * weylPauliX b) := by
  have h1 : weylPauliX u * weylPauliZ a = -(weylPauliZ a * weylPauliX u) :=
    weylPauliX_anticomm_weylPauliZ_of_symplectic_one a u h_anti
  have h2 : weylPauliX b * weylPauliX u = weylPauliX u * weylPauliX b :=
    (weylPauliX_comm b u).eq
  calc weylPauliX u * (weylPauliZ a * weylPauliX b) * weylPauliX u
    _ = (weylPauliX u * weylPauliZ a) * (weylPauliX b * weylPauliX u) := by
      simp only [mul_assoc]
    _ = (-(weylPauliZ a * weylPauliX u)) * (weylPauliX u * weylPauliX b) := by
      rw [h1, h2]
    _ = -(weylPauliZ a * (weylPauliX u * weylPauliX u) * weylPauliX b) := by
      rw [neg_mul (weylPauliZ a * weylPauliX u) (weylPauliX u * weylPauliX b)]
      simp only [mul_assoc]
    _ = -(weylPauliZ a * weylPauliX b) := by
      rw [weylPauliX_sq_eq_one, mul_one]
