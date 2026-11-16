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

import Proofs.KMSSafeSubspaceODE.KMSDissipativeGeneratorAndGronwall
import Proofs.KMSSafeSubspaceODE.KMSFourthRootAndPinchedGibbs
import Mathlib.Analysis.Normed.Field.Basic

open scoped Classical InnerProduct ComplexConjugate BigOperators
open ContinuousLinearMap

noncomputable section

/-!
# GKLS Semigroup Unitality, Star-Preservation, Stationarity, and Complete Positivity

Establishes abstract superoperator exponential identities (`superop_exp_hasSum`, `superop_exp_real_functional_invariant`, `superop_exp_unital_of_zero`, `superop_exp_isStarPreserving`) and proves Kraus Euler-step complete positivity (`isCompletelyPositiveMap_opDaviesThermalSemigroup`) for `opDaviesThermalSemigroup`.

## References

* Part I, Section 5.5 (`subsec:unperturbed-kms-lifetime`), Theorem 5.8(ii) (`thm:unperturbed-kms-lifetime`)
-/

private lemma clm_smul_mul_gkls {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (a : ℂ) (A B : E →L[ℂ] E) : (a • A) * B = a • (A * B) := by ext φ; simp

private lemma clm_mul_smul_gkls {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (A B : E →L[ℂ] E) (a : ℂ) : A * (a • B) = a • (A * B) := by ext φ; simp

set_option linter.style.haveILetI false

lemma superop_exp_hasSum {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [CompleteSpace E] (A : (E →L[ℂ] E) →L[ℂ] (E →L[ℂ] E)) (X : E →L[ℂ] E) :
    HasSum (fun n : ℕ => (((n.factorial : ℂ)⁻¹) • (A ^ n)) X) ((NormedSpace.exp A) X) := by
  letI : NormedRing ((E →L[ℂ] E) →L[ℂ] (E →L[ℂ] E)) := ContinuousLinearMap.toNormedRing
  letI : NormedAlgebra ℂ ((E →L[ℂ] E) →L[ℂ] (E →L[ℂ] E)) := ContinuousLinearMap.toNormedAlgebra
  have h_ser := NormedSpace.expSeries_hasSum_exp (𝕂 := ℂ) A
  simp_rw [NormedSpace.expSeries_apply_eq] at h_ser
  let evX : ((E →L[ℂ] E) →L[ℂ] (E →L[ℂ] E)) →L[ℂ] (E →L[ℂ] E) :=
    ContinuousLinearMap.apply ℂ (E →L[ℂ] E) X
  exact h_ser.map evX evX.continuous

lemma superop_exp_real_functional_invariant {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] [CompleteSpace E]
    (φ : (E →L[ℂ] E) →+ ℝ) (hφ_cont : Continuous φ)
    (hφ_real : ∀ (r : ℝ) (M : E →L[ℂ] E), φ ((r : ℂ) • M) = r * φ M)
    (L : (E →L[ℂ] E) →L[ℂ] (E →L[ℂ] E)) (hL : ∀ Y : E →L[ℂ] E, φ (L Y) = 0)
    (t : ℝ) (X : E →L[ℂ] E) :
    φ ((NormedSpace.exp ((t : ℂ) • L)) X) = φ X := by
  letI : NormedRing ((E →L[ℂ] E) →L[ℂ] (E →L[ℂ] E)) := ContinuousLinearMap.toNormedRing
  have h_hs := (superop_exp_hasSum ((t : ℂ) • L) X).map φ hφ_cont
  change HasSum (fun n : ℕ => φ ((((n.factorial : ℂ)⁻¹) • (((t : ℂ) • L) ^ n)) X))
    (φ ((NormedSpace.exp ((t : ℂ) • L)) X)) at h_hs
  have h_terms : ∀ n : ℕ,
      φ ((((n.factorial : ℂ)⁻¹) • (((t : ℂ) • L) ^ n)) X) = if n = 0 then φ X else 0 := by
    intro n; cases n with
    | zero =>
      rw [if_pos rfl, pow_zero, Nat.factorial_zero, Nat.cast_one, inv_one, one_smul]
      rfl
    | succ k =>
      rw [if_neg (Nat.succ_ne_zero k)]
      change φ (((((k + 1).factorial : ℂ)⁻¹) • (((t : ℂ) • L) ^ (k + 1))) X) = 0
      rw [ContinuousLinearMap.smul_apply, pow_succ', ContinuousLinearMap.mul_apply,
        ContinuousLinearMap.smul_apply, smul_smul]
      have h_real : (((k + 1).factorial : ℂ)⁻¹ * (t : ℂ)) =
          ((((k + 1).factorial : ℝ)⁻¹ * t : ℝ) : ℂ) := by push_cast; rfl
      rw [h_real, hφ_real, hL _, mul_zero]
  simp_rw [h_terms] at h_hs
  exact h_hs.unique (hasSum_ite_eq 0 (φ X))

lemma superop_exp_unital_of_zero {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] [CompleteSpace E]
    (L : (E →L[ℂ] E) →L[ℂ] (E →L[ℂ] E)) (hL_one : L 1 = 0) (t : ℝ) :
    (NormedSpace.exp ((t : ℂ) • L)) 1 = 1 := by
  letI : NormedRing ((E →L[ℂ] E) →L[ℂ] (E →L[ℂ] E)) := ContinuousLinearMap.toNormedRing
  have h_hs := superop_exp_hasSum ((t : ℂ) • L) 1
  have h_pow : ∀ n : ℕ, (((n.factorial : ℂ)⁻¹) • (((t : ℂ) • L) ^ n)) 1 =
      if n = 0 then 1 else 0 := by
    intro n; cases n with
    | zero =>
      rw [if_pos rfl, pow_zero, Nat.factorial_zero, Nat.cast_one, inv_one, one_smul]
      rfl
    | succ k =>
      rw [if_neg (Nat.succ_ne_zero k), pow_succ, ContinuousLinearMap.smul_apply]
      change ((k + 1).factorial : ℂ)⁻¹ • ((((t : ℂ) • L) ^ k) (((t : ℂ) • L) 1)) = 0
      rw [ContinuousLinearMap.smul_apply, hL_one, smul_zero, map_zero, smul_zero]
  simp_rw [h_pow] at h_hs
  exact h_hs.unique (hasSum_ite_eq 0 1)

lemma superop_exp_isStarPreserving {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] [CompleteSpace E]
    (L : (E →L[ℂ] E) →L[ℂ] (E →L[ℂ] E)) (hL_star : IsStarPreservingMap L) (t : ℝ) :
    IsStarPreservingMap (NormedSpace.exp ((t : ℂ) • L)) := by
  letI : NormedRing ((E →L[ℂ] E) →L[ℂ] (E →L[ℂ] E)) := ContinuousLinearMap.toNormedRing
  intro Y
  have h_pow_star : ∀ n : ℕ,
      star (((((n.factorial : ℂ)⁻¹) • (((t : ℂ) • L) ^ n)) Y)) =
        (((n.factorial : ℂ)⁻¹) • (((t : ℂ) • L) ^ n)) (star Y) := by
    intro n
    have h_iter : ∀ k : ℕ, star (((((t : ℂ) • L) ^ k) Y)) = (((t : ℂ) • L) ^ k) (star Y) := by
      intro k; induction k with
      | zero => rfl
      | succ k ih =>
        rw [pow_succ', ContinuousLinearMap.mul_apply, ContinuousLinearMap.smul_apply,
          star_smul, RCLike.star_def, Complex.conj_ofReal]
        have h_ly : star (L ((((t : ℂ) • L) ^ k) Y)) = L (star ((((t : ℂ) • L) ^ k) Y)) :=
          hL_star _
        rw [h_ly, ih]; rfl
    rw [ContinuousLinearMap.smul_apply, star_smul, h_iter n]
    have h_inv_conj : star ((n.factorial : ℂ)⁻¹) = ((n.factorial : ℂ)⁻¹) := by
      rw [star_inv₀, RCLike.star_def, Complex.conj_natCast]
    rw [h_inv_conj]; rfl
  have h1 := superop_exp_hasSum ((t : ℂ) • L) Y
  have h2 := superop_exp_hasSum ((t : ℂ) • L) (star Y)
  let starAddHom : (E →L[ℂ] E) →+ (E →L[ℂ] E) :=
    { toFun := star, map_zero' := star_zero _, map_add' := fun a b => star_add a b }
  have h_cont_star : Continuous (star : (E →L[ℂ] E) → (E →L[ℂ] E)) :=
    (ContinuousLinearMap.adjoint : (E →L[ℂ] E) ≃ₗᵢ⋆[ℂ] (E →L[ℂ] E)).continuous
  have h1_star := h1.map starAddHom h_cont_star
  change HasSum (fun n : ℕ => star (((((n.factorial : ℂ)⁻¹) • (((t : ℂ) • L) ^ n)) Y)))
    (star ((NormedSpace.exp ((t : ℂ) • L)) Y)) at h1_star
  simp_rw [h_pow_star] at h1_star
  exact h1_star.unique h2

private lemma isCompletelyPositiveMap_clmSandwichOp_adjoint {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] [CompleteSpace E] (W : E →L[ℂ] E) :
    IsCompletelyPositiveMap (clmSandwichOp (W†) W) := by
  intro n M hM
  let π := fun i : Fin n => ancillaBlockProj (E := E) n i
  let W_n : PiLp 2 (fun _ : Fin n => E) →L[ℂ] PiLp 2 (fun _ : Fin n => E) :=
    ∑ j : Fin n, (ContinuousLinearMap.adjoint (π j)).comp (W.comp (π j))
  have hWn_adj : W_n† = ∑ i : Fin n, (ContinuousLinearMap.adjoint (π i)).comp ((W†).comp (π i)) := by
    change ContinuousLinearMap.adjoint W_n = _
    dsimp only [W_n]; rw [map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [ContinuousLinearMap.adjoint_comp, ContinuousLinearMap.adjoint_adjoint,
      ContinuousLinearMap.comp_assoc]
  have h_eq : ancillaLiftMap n (clmSandwichOp (W†) W) M = W_n† * M * W_n := by
    apply ContinuousLinearMap.ext; intro Ψ
    rw [hWn_adj]; dsimp only [ancillaLiftMap, W_n, π]
    rw [ContinuousLinearMap.mul_apply, ContinuousLinearMap.mul_apply,
      ContinuousLinearMap.sum_apply, ContinuousLinearMap.sum_apply]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [ContinuousLinearMap.sum_apply, ContinuousLinearMap.sum_apply,
      ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply,
      map_sum M, map_sum (ancillaBlockProj (E := E) n i), map_sum (W†),
      map_sum (ContinuousLinearMap.adjoint (ancillaBlockProj (E := E) n i))]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [ContinuousLinearMap.comp_apply, clmSandwichOp_apply,
      ContinuousLinearMap.mul_apply]
  rw [h_eq]
  refine ⟨?_, ?_⟩
  · rw [isSelfAdjoint_iff]
    change star (star W_n * M * W_n) = star W_n * M * W_n
    rw [star_mul, star_mul, star_star, hM.1.star_eq, mul_assoc]
  · intro Ψ
    change 0 ≤ RCLike.re (inner ℂ Ψ ((W_n†) (M (W_n Ψ))))
    rw [ContinuousLinearMap.adjoint_inner_right]
    exact hM.2 (W_n Ψ)

private lemma ancillaBlockProj_comp_adjoint {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] [CompleteSpace E] (n : ℕ) (i k : Fin n) :
    (ancillaBlockProj (E := E) n i).comp (ContinuousLinearMap.adjoint (ancillaBlockProj (E := E) n k)) =
      if i = k then 1 else 0 := by
  apply ContinuousLinearMap.ext; intro x
  have h_adj_apply : (ContinuousLinearMap.adjoint (ancillaBlockProj (E := E) n k)) x =
      WithLp.toLp 2 (fun m : Fin n => if m = k then x else 0) := by
    apply ext_inner_right ℂ; intro Ψ
    rw [ContinuousLinearMap.adjoint_inner_left, PiLp.inner_apply]
    have h_proj : ancillaBlockProj (E := E) n k Ψ = Ψ.ofLp k := rfl
    rw [h_proj, Finset.sum_eq_single k]
    · simp
    · intro m _ hne; simp [hne]
    · intro h_not; exact False.elim (h_not (Finset.mem_univ k))
  change ancillaBlockProj (E := E) n i ((ContinuousLinearMap.adjoint (ancillaBlockProj (E := E) n k)) x) =
    (if i = k then (1 : E →L[ℂ] E) else 0) x
  rw [h_adj_apply]
  change (WithLp.toLp 2 (fun m : Fin n => if m = k then x else 0)).ofLp i = _
  split_ifs with hik <;> simp [hik]

private lemma sum_ancillaBlockProj_adjoint_comp_eq_one {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] [CompleteSpace E] (n : ℕ) :
    (∑ i : Fin n, ((ancillaBlockProj (E := E) n i)†).comp (ancillaBlockProj (E := E) n i)) = 1 := by
  apply ContinuousLinearMap.ext; intro Ψ
  apply ext_inner_left ℂ; intro Φ
  rw [ContinuousLinearMap.sum_apply, inner_sum, ContinuousLinearMap.one_apply, PiLp.inner_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.adjoint_inner_right]; rfl

private lemma isCompletelyPositiveMap_closure_props {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] [CompleteSpace E] :
    IsCompletelyPositiveMap (1 : (E →L[ℂ] E) →L[ℂ] (E →L[ℂ] E)) ∧
    IsCompletelyPositiveMap (0 : (E →L[ℂ] E) →L[ℂ] (E →L[ℂ] E)) ∧
    (∀ Φ₁ Φ₂ : (E →L[ℂ] E) →L[ℂ] (E →L[ℂ] E),
      IsCompletelyPositiveMap Φ₁ → IsCompletelyPositiveMap Φ₂ →
      IsCompletelyPositiveMap (Φ₁ + Φ₂)) ∧
    (∀ (r : ℝ) (Φ : (E →L[ℂ] E) →L[ℂ] (E →L[ℂ] E)),
      0 ≤ r → IsCompletelyPositiveMap Φ → IsCompletelyPositiveMap ((r : ℂ) • Φ)) ∧
    (∀ Φ₁ Φ₂ : (E →L[ℂ] E) →L[ℂ] (E →L[ℂ] E),
      IsCompletelyPositiveMap Φ₁ → IsCompletelyPositiveMap Φ₂ →
      IsCompletelyPositiveMap (Φ₁.comp Φ₂)) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro n M hM
    have h_id : ancillaLiftMap n (1 : (E →L[ℂ] E) →L[ℂ] (E →L[ℂ] E)) M = M := by
      apply ContinuousLinearMap.ext; intro Ψ
      have h_part : ∀ v : PiLp 2 (fun _ : Fin n => E),
          (∑ i : Fin n, ((ancillaBlockProj (E := E) n i)†) (ancillaBlockProj (E := E) n i v)) = v := by
        intro v
        have hv := ContinuousLinearMap.ext_iff.mp (sum_ancillaBlockProj_adjoint_comp_eq_one (E := E) n) v
        simpa only [ContinuousLinearMap.sum_apply, ContinuousLinearMap.comp_apply,
          ContinuousLinearMap.one_apply] using hv
      dsimp only [ancillaLiftMap]
      simp only [ContinuousLinearMap.sum_apply, ContinuousLinearMap.comp_apply,
        ContinuousLinearMap.one_apply]
      have h_inner_sum : ∀ i : Fin n,
          (∑ j : Fin n, ((ancillaBlockProj (E := E) n i)†)
            ((ancillaBlockProj (E := E) n i)
              (M (((ancillaBlockProj (E := E) n j)†) ((ancillaBlockProj (E := E) n j) Ψ))))) =
          ((ancillaBlockProj (E := E) n i)†) ((ancillaBlockProj (E := E) n i) (M Ψ)) := by
        intro i
        rw [← map_sum ((ancillaBlockProj (E := E) n i)†),
          ← map_sum (ancillaBlockProj (E := E) n i), ← map_sum M, h_part Ψ]
      simp_rw [h_inner_sum]
      exact h_part (M Ψ)
    rwa [h_id]
  · intro n M _
    have h0 : ancillaLiftMap n (0 : (E →L[ℂ] E) →L[ℂ] (E →L[ℂ] E)) M = 0 := by
      dsimp only [ancillaLiftMap]
      simp only [ContinuousLinearMap.zero_apply, zero_comp, comp_zero, Finset.sum_const_zero]
    rw [h0]; exact ⟨IsSelfAdjoint.zero _, fun _ => by simp⟩
  · intro Φ₁ Φ₂ h₁ h₂ n M hM
    have h_add : ancillaLiftMap n (Φ₁ + Φ₂) M = ancillaLiftMap n Φ₁ M + ancillaLiftMap n Φ₂ M := by
      dsimp [ancillaLiftMap]
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [ContinuousLinearMap.add_apply, add_comp, comp_add]
    rw [h_add]
    exact ⟨(h₁ n M hM).1.add (h₂ n M hM).1, fun Ψ => by
      rw [ContinuousLinearMap.add_apply, inner_add_right, map_add]
      exact add_nonneg ((h₁ n M hM).2 Ψ) ((h₂ n M hM).2 Ψ)⟩
  · intro r Φ hr hΦ n M hM
    have h_smul : ancillaLiftMap n ((r : ℂ) • Φ) M = (r : ℂ) • ancillaLiftMap n Φ M := by
      dsimp [ancillaLiftMap]
      rw [Finset.smul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Finset.smul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [ContinuousLinearMap.smul_apply, smul_comp, comp_smul]
    rw [h_smul]
    exact ⟨isSelfAdjoint_real_smul r (hΦ n M hM).1, fun Ψ => by
      rw [ContinuousLinearMap.smul_apply, inner_smul_right, re_ofReal_mul]
      exact mul_nonneg hr ((hΦ n M hM).2 Ψ)⟩
  · intro Φ₁ Φ₂ h₁ h₂ n M hM
    have h_orth : ∀ (m p : Fin n) (y : E),
        ancillaBlockProj (E := E) n m (((ancillaBlockProj (E := E) n p)†) y) =
          if m = p then y else 0 := by
      intro m p y
      have h := ContinuousLinearMap.ext_iff.mp (ancillaBlockProj_comp_adjoint (E := E) n m p) y
      rw [ContinuousLinearMap.comp_apply] at h
      change ancillaBlockProj (E := E) n m (((ancillaBlockProj (E := E) n p)†) y) =
        (if m = p then (1 : E →L[ℂ] E) else 0) y at h
      rw [h]
      split_ifs <;> simp
    have h_comp : ancillaLiftMap n (Φ₁.comp Φ₂) M = ancillaLiftMap n Φ₁ (ancillaLiftMap n Φ₂ M) := by
      dsimp [ancillaLiftMap]
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
      congr 2; congr 1
      have h_in : (ancillaBlockProj (E := E) n i).comp
          ((∑ k : Fin n, ∑ l : Fin n,
            ((ancillaBlockProj n k)†).comp
              ((Φ₂ ((ancillaBlockProj n k).comp (M.comp ((ancillaBlockProj n l)†)))).comp
                (ancillaBlockProj n l))).comp
            ((ancillaBlockProj n j)†)) =
          Φ₂ ((ancillaBlockProj n i).comp (M.comp ((ancillaBlockProj n j)†))) := by
        apply ContinuousLinearMap.ext; intro x
        rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply,
          ContinuousLinearMap.sum_apply, map_sum]
        rw [Finset.sum_eq_single i]
        · rw [ContinuousLinearMap.sum_apply, map_sum, Finset.sum_eq_single j]
          · rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply,
              h_orth, if_pos rfl, h_orth, if_pos rfl]
          · intro l _ hlj
            rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply,
              h_orth, if_pos rfl, h_orth, if_neg hlj, map_zero]
          · intro h_not; exact False.elim (h_not (Finset.mem_univ j))
        · intro k _ hki
          rw [ContinuousLinearMap.sum_apply, map_sum]
          refine Finset.sum_eq_zero fun l _ => ?_
          rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply,
            h_orth, if_neg hki.symm]
        · intro h_not; exact False.elim (h_not (Finset.mem_univ i))
      rw [h_in]
    rw [h_comp]
    exact h₁ n _ (h₂ n M hM)

private lemma isCompletelyPositiveMap_finset_sum {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] [CompleteSpace E] {α : Type*} (s : Finset α)
    (Φ : α → ((E →L[ℂ] E) →L[ℂ] (E →L[ℂ] E)))
    (hΦ : ∀ a ∈ s, IsCompletelyPositiveMap (Φ a)) :
    IsCompletelyPositiveMap (∑ a ∈ s, Φ a) := by
  classical
  have hc := isCompletelyPositiveMap_closure_props (E := E)
  induction s using Finset.induction_on with
  | empty => simpa using hc.2.1
  | @insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact hc.2.2.1 _ _ (hΦ a (Finset.mem_insert_self a s))
      (ih fun b hb => hΦ b (Finset.mem_insert_of_mem hb))

private lemma isCompletelyPositiveMap_of_tendsto {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] [CompleteSpace E]
    (T : ℕ → ((E →L[ℂ] E) →L[ℂ] (E →L[ℂ] E)))
    (Φ : (E →L[ℂ] E) →L[ℂ] (E →L[ℂ] E))
    (hT : ∀ m : ℕ, IsCompletelyPositiveMap (T m))
    (h_lim : Filter.Tendsto T Filter.atTop (nhds Φ)) :
    IsCompletelyPositiveMap Φ := by
  intro n M hM
  have h_cont_lift : Continuous (fun Ψ' : (E →L[ℂ] E) →L[ℂ] (E →L[ℂ] E) => ancillaLiftMap n Ψ' M) := by
    unfold ancillaLiftMap
    refine continuous_finset_sum _ fun i _ => continuous_finset_sum _ fun j _ => ?_
    let X_ij := (ancillaBlockProj (E := E) n i).comp (M.comp ((ancillaBlockProj (E := E) n j)†))
    let sand_ij : (E →L[ℂ] E) →L[ℂ] (PiLp 2 (fun _ : Fin n => E) →L[ℂ] PiLp 2 (fun _ : Fin n => E)) :=
      ((ContinuousLinearMap.compL ℂ _ _ _ ((ancillaBlockProj (E := E) n i)†)).comp
        ((ContinuousLinearMap.compL ℂ _ _ _).flip (ancillaBlockProj (E := E) n j)))
    have h_fn : (fun Ψ' : (E →L[ℂ] E) →L[ℂ] (E →L[ℂ] E) =>
        ((ancillaBlockProj (E := E) n i)†).comp ((Ψ' X_ij).comp (ancillaBlockProj (E := E) n j))) =
        sand_ij ∘ (ContinuousLinearMap.apply ℂ (E →L[ℂ] E) X_ij) := by
      ext Ψ'; rfl
    rw [h_fn]
    exact sand_ij.continuous.comp (ContinuousLinearMap.apply ℂ (E →L[ℂ] E) X_ij).continuous
  have h_tend : Filter.Tendsto (fun m => ancillaLiftMap n (T m) M)
      Filter.atTop (nhds (ancillaLiftMap n Φ M)) :=
    h_cont_lift.continuousAt.tendsto.comp h_lim
  refine ⟨?_, ?_⟩
  · rw [isSelfAdjoint_iff]
    have h_cont_star : Continuous
        (star : (PiLp 2 (fun _ : Fin n => E) →L[ℂ] PiLp 2 (fun _ : Fin n => E)) →
          (PiLp 2 (fun _ : Fin n => E) →L[ℂ] PiLp 2 (fun _ : Fin n => E))) :=
      (ContinuousLinearMap.adjoint :
        (PiLp 2 (fun _ : Fin n => E) →L[ℂ] PiLp 2 (fun _ : Fin n => E)) ≃ₗᵢ⋆[ℂ]
          (PiLp 2 (fun _ : Fin n => E) →L[ℂ] PiLp 2 (fun _ : Fin n => E))).continuous
    have h_star_tend : Filter.Tendsto (fun m => star (ancillaLiftMap n (T m) M))
        Filter.atTop (nhds (star (ancillaLiftMap n Φ M))) :=
      h_cont_star.continuousAt.tendsto.comp h_tend
    have h_eq_m : (fun m => star (ancillaLiftMap n (T m) M)) =
        (fun m => ancillaLiftMap n (T m) M) := by
      funext m; exact (hT m n M hM).1.star_eq
    rw [h_eq_m] at h_star_tend
    exact tendsto_nhds_unique h_star_tend h_tend
  · intro Ψ
    have h_re_tend : Filter.Tendsto
        (fun m => RCLike.re (inner ℂ Ψ (ancillaLiftMap n (T m) M Ψ)))
        Filter.atTop (nhds (RCLike.re (inner ℂ Ψ (ancillaLiftMap n Φ M Ψ)))) := by
      have h_cont_eval : Continuous
          (fun K : PiLp 2 (fun _ : Fin n => E) →L[ℂ] PiLp 2 (fun _ : Fin n => E) =>
            RCLike.re (inner ℂ Ψ (K Ψ))) :=
        RCLike.continuous_re.comp
          (continuous_const.inner (ContinuousLinearMap.apply ℂ _ Ψ).continuous)
      exact h_cont_eval.continuousAt.tendsto.comp h_tend
    exact ge_of_tendsto' h_re_tend fun m => (hT m n M hM).2 Ψ

private lemma superop_exp_norm_and_taylor2 {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] [CompleteSpace E]
    (Z : (E →L[ℂ] E) →L[ℂ] (E →L[ℂ] E)) :
    ‖NormedSpace.exp Z‖ ≤ Real.exp ‖Z‖ ∧
    ‖NormedSpace.exp Z - (1 + Z)‖ ≤ ‖Z‖ ^ 2 * Real.exp ‖Z‖ := by
  letI : NormedRing ((E →L[ℂ] E) →L[ℂ] (E →L[ℂ] E)) := ContinuousLinearMap.toNormedRing
  letI : NormedAlgebra ℂ ((E →L[ℂ] E) →L[ℂ] (E →L[ℂ] E)) := ContinuousLinearMap.toNormedAlgebra
  have h_pow_norm : ∀ n : ℕ, ‖Z ^ n‖ ≤ ‖Z‖ ^ n := by
    intro n; induction n with
    | zero => rw [pow_zero, pow_zero]; exact ContinuousLinearMap.norm_id_le
    | succ k ih =>
      rw [pow_succ, pow_succ]
      exact (norm_mul_le (Z ^ k) Z).trans (mul_le_mul_of_nonneg_right ih (norm_nonneg Z))
  have h_ser : HasSum (fun n : ℕ => ((n.factorial : ℂ)⁻¹) • (Z ^ n)) (NormedSpace.exp Z) := by
    have h0 := NormedSpace.expSeries_hasSum_exp (𝕂 := ℂ) Z
    simp_rw [NormedSpace.expSeries_apply_eq] at h0
    exact h0
  have h_real : HasSum (fun n : ℕ => ‖Z‖ ^ n / (n.factorial : ℝ)) (Real.exp ‖Z‖) := by
    rw [Real.exp_eq_exp_ℝ]
    exact NormedSpace.expSeries_div_hasSum_exp ‖Z‖
  have h_term_le : ∀ n : ℕ, ‖((n.factorial : ℂ)⁻¹) • (Z ^ n)‖ ≤ ‖Z‖ ^ n / (n.factorial : ℝ) := by
    intro n
    rw [norm_smul, norm_inv, Complex.norm_natCast, div_eq_inv_mul]
    exact mul_le_mul_of_nonneg_left (h_pow_norm n) (by positivity)
  have h_summable_norm : Summable (fun n : ℕ => ‖((n.factorial : ℂ)⁻¹) • (Z ^ n)‖) :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) h_term_le h_real.summable
  refine ⟨?_, ?_⟩
  · rw [← h_ser.tsum_eq]
    exact (norm_tsum_le_tsum_norm h_summable_norm).trans
      (hasSum_le h_term_le h_summable_norm.hasSum h_real)
  · have h_shift := (hasSum_nat_add_iff' 2).mpr h_ser
    have h_range2 : (∑ i ∈ Finset.range 2, ((i.factorial : ℂ)⁻¹) • (Z ^ i)) = 1 + Z := by
      rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_zero, zero_add]; simp
    rw [h_range2] at h_shift
    have h_shift_le : ∀ n : ℕ,
        ‖(((n + 2).factorial : ℂ)⁻¹) • (Z ^ (n + 2))‖ ≤
          ‖Z‖ ^ 2 * (‖Z‖ ^ n / (n.factorial : ℝ)) := by
      intro n
      rw [norm_smul, norm_inv, Complex.norm_natCast]
      have h_fac : (n.factorial : ℝ) ≤ ((n + 2).factorial : ℝ) := by
        exact_mod_cast Nat.factorial_le (by omega)
      have h_inv_le : (((n + 2).factorial : ℝ))⁻¹ ≤ ((n.factorial : ℝ))⁻¹ :=
        inv_anti₀ (Nat.cast_pos.mpr (Nat.factorial_pos n)) h_fac
      calc (((n + 2).factorial : ℝ))⁻¹ * ‖Z ^ (n + 2)‖
        _ ≤ ((n.factorial : ℝ))⁻¹ * ‖Z‖ ^ (n + 2) :=
          mul_le_mul h_inv_le (h_pow_norm (n + 2)) (norm_nonneg _) (by positivity)
        _ = ‖Z‖ ^ 2 * (‖Z‖ ^ n / (n.factorial : ℝ)) := by rw [pow_add, div_eq_inv_mul]; ring
    have h_real2 := h_real.mul_left (‖Z‖ ^ 2)
    have h_sum2 : Summable (fun n : ℕ => ‖(((n + 2).factorial : ℂ)⁻¹) • (Z ^ (n + 2))‖) :=
      Summable.of_nonneg_of_le (fun _ => norm_nonneg _) h_shift_le h_real2.summable
    rw [← h_shift.tsum_eq]
    exact (norm_tsum_le_tsum_norm h_sum2).trans (hasSum_le h_shift_le h_sum2.hasSum h_real2)

private lemma normedRing_pow_sub_pow_norm_le {𝔸 : Type*} [NormedRing 𝔸]
    (h1_le : ‖(1 : 𝔸)‖ ≤ 1) (U V : 𝔸) {M : ℝ} (hM : 1 ≤ M)
    (hU : ‖U‖ ≤ M) (hV : ‖V‖ ≤ M) (k : ℕ) :
    ‖U ^ k - V ^ k‖ ≤ (k : ℝ) * M ^ k * ‖U - V‖ := by
  have hM0 : 0 ≤ M := by linarith
  have hU_pow : ∀ j : ℕ, ‖U ^ j‖ ≤ M ^ j := by
    intro j; induction j with
    | zero => simpa using h1_le
    | succ j ih =>
      rw [pow_succ, pow_succ]
      exact (norm_mul_le _ _).trans (mul_le_mul ih hU (norm_nonneg _) (pow_nonneg hM0 j))
  induction k with
  | zero => simp
  | succ k ih =>
    have h_id : U ^ (k + 1) - V ^ (k + 1) = U ^ k * (U - V) + (U ^ k - V ^ k) * V := by
      rw [pow_succ, pow_succ, mul_sub, sub_mul]; abel
    rw [h_id]
    have h1 : ‖U ^ k * (U - V)‖ ≤ M ^ (k + 1) * ‖U - V‖ := by
      have hMk : M ^ k ≤ M ^ (k + 1) := by
        rw [pow_succ]; exact le_mul_of_one_le_right (pow_nonneg hM0 k) hM
      exact (norm_mul_le _ _).trans
        (mul_le_mul_of_nonneg_right ((hU_pow k).trans hMk) (norm_nonneg _))
    have h2 : ‖(U ^ k - V ^ k) * V‖ ≤ (k : ℝ) * M ^ (k + 1) * ‖U - V‖ := by
      calc ‖(U ^ k - V ^ k) * V‖
        _ ≤ ‖U ^ k - V ^ k‖ * ‖V‖ := norm_mul_le _ _
        _ ≤ ((k : ℝ) * M ^ k * ‖U - V‖) * M :=
          mul_le_mul ih hV (norm_nonneg _) (by positivity)
        _ = (k : ℝ) * M ^ (k + 1) * ‖U - V‖ := by rw [pow_succ]; ring
    calc ‖U ^ k * (U - V) + (U ^ k - V ^ k) * V‖
      _ ≤ ‖U ^ k * (U - V)‖ + ‖(U ^ k - V ^ k) * V‖ := norm_add_le _ _
      _ ≤ M ^ (k + 1) * ‖U - V‖ + (k : ℝ) * M ^ (k + 1) * ‖U - V‖ := add_le_add h1 h2
      _ = ((k + 1 : ℕ) : ℝ) * M ^ (k + 1) * ‖U - V‖ := by push_cast; ring

private lemma normedAlgebra_euler_quadratic_tendsto_exp {𝔸 : Type*} [NormedRing 𝔸]
    [NormedAlgebra ℂ 𝔸] [CompleteSpace 𝔸] (h1_le : ‖(1 : 𝔸)‖ ≤ 1) (A R : 𝔸)
    (h_norm_exp : ∀ Z : 𝔸, ‖NormedSpace.exp Z‖ ≤ Real.exp ‖Z‖ ∧
      ‖NormedSpace.exp Z - (1 + Z)‖ ≤ ‖Z‖ ^ 2 * Real.exp ‖Z‖) :
    Filter.Tendsto
      (fun m : ℕ =>
        (1 + (((m + 1 : ℕ) : ℂ)⁻¹) • A +
          (((((m + 1 : ℕ) : ℝ) ^ 2)⁻¹ : ℝ) : ℂ) • R) ^ (m + 1))
      Filter.atTop (nhds (NormedSpace.exp A)) := by
  letI : NormedAlgebra ℚ 𝔸 := NormedAlgebra.restrictScalars ℚ ℂ 𝔸
  let K_const : ℝ := Real.exp (‖A‖ + ‖R‖) * (‖R‖ + ‖A‖ ^ 2 * Real.exp ‖A‖)
  have h_bound : ∀ m : ℕ,
      ‖(1 + (((m + 1 : ℕ) : ℂ)⁻¹) • A +
          (((((m + 1 : ℕ) : ℝ) ^ 2)⁻¹ : ℝ) : ℂ) • R) ^ (m + 1) - NormedSpace.exp A‖ ≤
        K_const / ((m + 1 : ℕ) : ℝ) := by
    intro m
    set k : ℕ := m + 1
    have hk_pos : 0 < k := Nat.succ_pos m
    have hk_r_pos : (0 : ℝ) < (k : ℝ) := Nat.cast_pos.mpr hk_pos
    have hk_r_ge1 : (1 : ℝ) ≤ (k : ℝ) := Nat.one_le_cast.mpr hk_pos
    have hk_c_ne : (k : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (ne_of_gt hk_pos)
    let Z : 𝔸 := ((k : ℂ)⁻¹) • A
    let U : 𝔸 := 1 + Z + ((((k : ℝ) ^ 2)⁻¹ : ℝ) : ℂ) • R
    let V : 𝔸 := NormedSpace.exp Z
    have hV_pow : V ^ k = NormedSpace.exp A := by
      dsimp [V, Z]
      rw [← NormedSpace.exp_nsmul k (((k : ℂ)⁻¹) • A), ← Nat.cast_smul_eq_nsmul ℂ,
        smul_smul, mul_inv_cancel₀ hk_c_ne, one_smul]
    have hZ_norm : ‖Z‖ = ‖A‖ / (k : ℝ) := by
      dsimp [Z]; rw [norm_smul, norm_inv, Complex.norm_natCast, div_eq_inv_mul, mul_comm]
    have hZ_le_A : ‖Z‖ ≤ ‖A‖ := by rw [hZ_norm]; exact div_le_self (norm_nonneg A) hk_r_ge1
    set M := Real.exp ((‖A‖ + ‖R‖) / (k : ℝ))
    have hM_ge1 : 1 ≤ M := Real.one_le_exp (div_nonneg (by positivity) (le_of_lt hk_r_pos))
    have hM_pow : M ^ k = Real.exp (‖A‖ + ‖R‖) := by
      dsimp [M]; rw [← Real.exp_nat_mul, mul_div_cancel₀ _ (ne_of_gt hk_r_pos)]
    have hU_norm : ‖U‖ ≤ M := by
      have hR_term : ‖((((k : ℝ) ^ 2)⁻¹ : ℝ) : ℂ) • R‖ ≤ ‖R‖ / (k : ℝ) := by
        rw [norm_smul, Complex.norm_real, Real.norm_of_nonneg (by positivity), div_eq_mul_inv]
        have hk2 : ((k : ℝ) ^ 2)⁻¹ ≤ (k : ℝ)⁻¹ := by
          rw [inv_le_inv₀ (sq_pos_of_pos hk_r_pos) hk_r_pos]; nlinarith
        exact (mul_comm _ _).trans_le (mul_le_mul_of_nonneg_left hk2 (norm_nonneg R))
      have h1Z : ‖(1 : 𝔸) + Z‖ ≤ 1 + ‖Z‖ := (norm_add_le 1 Z).trans (by linarith)
      calc ‖U‖
        _ ≤ ‖(1 : 𝔸) + Z‖ + ‖((((k : ℝ) ^ 2)⁻¹ : ℝ) : ℂ) • R‖ := norm_add_le _ _
        _ ≤ (1 + ‖Z‖) + ‖R‖ / (k : ℝ) := add_le_add h1Z hR_term
        _ = 1 + (‖A‖ + ‖R‖) / (k : ℝ) := by rw [hZ_norm]; ring
        _ ≤ M := by linarith [Real.add_one_le_exp ((‖A‖ + ‖R‖) / (k : ℝ))]
    have hV_norm : ‖V‖ ≤ M := by
      calc ‖V‖ ≤ Real.exp ‖Z‖ := (h_norm_exp Z).1
        _ ≤ M := Real.exp_le_exp.mpr (by rw [hZ_norm, add_div]; linarith [div_nonneg (norm_nonneg R) (le_of_lt hk_r_pos)])
    have hUV_diff : ‖U - V‖ ≤ (‖R‖ + ‖A‖ ^ 2 * Real.exp ‖A‖) / ((k : ℝ) ^ 2) := by
      have h_split : U - V = ((((k : ℝ) ^ 2)⁻¹ : ℝ) : ℂ) • R - (NormedSpace.exp Z - (1 + Z)) := by
        dsimp [U, V]; abel
      rw [h_split]
      have h_t2' : ‖NormedSpace.exp Z - (1 + Z)‖ ≤ (‖A‖ ^ 2 * Real.exp ‖A‖) / ((k : ℝ) ^ 2) := by
        calc ‖NormedSpace.exp Z - (1 + Z)‖
          _ ≤ ‖Z‖ ^ 2 * Real.exp ‖Z‖ := (h_norm_exp Z).2
          _ ≤ (‖A‖ / (k : ℝ)) ^ 2 * Real.exp ‖A‖ := by
            rw [← hZ_norm]
            exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hZ_le_A) (sq_nonneg _)
          _ = (‖A‖ ^ 2 * Real.exp ‖A‖) / ((k : ℝ) ^ 2) := by rw [div_pow]; ring
      have hR_eq : ‖((((k : ℝ) ^ 2)⁻¹ : ℝ) : ℂ) • R‖ = ‖R‖ / ((k : ℝ) ^ 2) := by
        rw [norm_smul, Complex.norm_real, Real.norm_of_nonneg (by positivity), div_eq_inv_mul]
      calc ‖((((k : ℝ) ^ 2)⁻¹ : ℝ) : ℂ) • R - (NormedSpace.exp Z - (1 + Z))‖
        _ ≤ ‖((((k : ℝ) ^ 2)⁻¹ : ℝ) : ℂ) • R‖ + ‖NormedSpace.exp Z - (1 + Z)‖ := norm_sub_le _ _
        _ ≤ ‖R‖ / ((k : ℝ) ^ 2) + (‖A‖ ^ 2 * Real.exp ‖A‖) / ((k : ℝ) ^ 2) := add_le_add (le_of_eq hR_eq) h_t2'
        _ = (‖R‖ + ‖A‖ ^ 2 * Real.exp ‖A‖) / ((k : ℝ) ^ 2) := by ring
    rw [← hV_pow]
    calc ‖U ^ k - V ^ k‖
      _ ≤ (k : ℝ) * M ^ k * ‖U - V‖ := normedRing_pow_sub_pow_norm_le h1_le U V hM_ge1 hU_norm hV_norm k
      _ ≤ (k : ℝ) * Real.exp (‖A‖ + ‖R‖) * ((‖R‖ + ‖A‖ ^ 2 * Real.exp ‖A‖) / ((k : ℝ) ^ 2)) := by
        rw [hM_pow]; exact mul_le_mul_of_nonneg_left hUV_diff (by positivity)
      _ = K_const / (k : ℝ) := by dsimp [K_const]; field_simp [ne_of_gt hk_r_pos]
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero (fun _ => norm_nonneg _) h_bound ?_
  have h_inv_tend : Filter.Tendsto (fun m : ℕ => K_const * (((m : ℝ) + 1)⁻¹)) Filter.atTop (nhds (K_const * 0)) :=
    tendsto_const_nhds.mul (tendsto_inv_atTop_zero.comp (tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds))
  simpa [div_eq_mul_inv] using h_inv_tend

private lemma superop_exp_isCompletelyPositive_gkls {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] [CompleteSpace E] {α : Type*}
    (H0 : E →L[ℂ] E) (hH0 : IsSelfAdjoint H0)
    (s : Finset α) (K : α → (E →L[ℂ] E)) (γ : α → ℝ) (hγ : ∀ a ∈ s, 0 ≤ γ a)
    {t : ℝ} (ht : 0 ≤ t) :
    let L : (E →L[ℂ] E) →L[ℂ] (E →L[ℂ] E) :=
      Complex.I • opCommutatorCLM H0 +
        ∑ a ∈ s, (γ a : ℂ) • (clmSandwichOp ((K a)†) (K a) -
          (1 / 2 : ℂ) • (clmSandwichOp ((K a)† * K a) 1 + clmSandwichOp 1 ((K a)† * K a)))
    IsCompletelyPositiveMap (NormedSpace.exp ((t : ℂ) • L)) := by
  intro L
  letI : NormedRing ((E →L[ℂ] E) →L[ℂ] (E →L[ℂ] E)) := ContinuousLinearMap.toNormedRing
  letI : NormedAlgebra ℂ ((E →L[ℂ] E) →L[ℂ] (E →L[ℂ] E)) := ContinuousLinearMap.toNormedAlgebra
  letI : NormedAlgebra ℚ ((E →L[ℂ] E) →L[ℂ] (E →L[ℂ] E)) := NormedAlgebra.restrictScalars ℚ ℂ _
  have hc := isCompletelyPositiveMap_closure_props (E := E)
  let G : E →L[ℂ] E := ∑ a ∈ s, (γ a : ℂ) • ((K a)† * K a)
  have hG_sa : star G = G := by
    dsimp only [G]; rw [star_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    change star ((γ a : ℂ) • (star (K a) * K a)) = (γ a : ℂ) • (star (K a) * K a)
    rw [star_smul, RCLike.star_def, Complex.conj_ofReal, star_mul, star_star]
  let B_eff : E →L[ℂ] E := (-Complex.I) • H0 - (1 / 2 : ℂ) • G
  have hB_adj : B_eff† = Complex.I • H0 - (1 / 2 : ℂ) • G := by
    change star B_eff = _
    dsimp only [B_eff]
    rw [star_sub, star_smul, star_neg, RCLike.star_def, Complex.conj_I, neg_neg,
      hH0.star_eq, star_smul, hG_sa]
    congr 2; norm_num [RCLike.star_def]
  let A : (E →L[ℂ] E) →L[ℂ] (E →L[ℂ] E) := (t : ℂ) • L
  let R : (E →L[ℂ] E) →L[ℂ] (E →L[ℂ] E) := ((t ^ 2 : ℝ) : ℂ) • clmSandwichOp (B_eff†) B_eff
  let T_step : ℝ → ((E →L[ℂ] E) →L[ℂ] (E →L[ℂ] E)) := fun ε =>
    clmSandwichOp ((1 + (ε : ℂ) • B_eff)†) (1 + (ε : ℂ) • B_eff) +
      ∑ a ∈ s, ((ε * γ a : ℝ) : ℂ) • clmSandwichOp ((K a)†) (K a)
  have hT_cp : ∀ ε : ℝ, 0 ≤ ε → IsCompletelyPositiveMap (T_step ε) := by
    intro ε hε
    exact hc.2.2.1 _ _ (isCompletelyPositiveMap_clmSandwichOp_adjoint _)
      (isCompletelyPositiveMap_finset_sum s _ fun a ha =>
        hc.2.2.2.1 (ε * γ a) _ (mul_nonneg hε (hγ a ha))
          (isCompletelyPositiveMap_clmSandwichOp_adjoint (K a)))
  have hT_pow_cp : ∀ (m : ℕ) (Φ : (E →L[ℂ] E) →L[ℂ] (E →L[ℂ] E)),
      IsCompletelyPositiveMap Φ → IsCompletelyPositiveMap (Φ ^ m) := by
    intro m Φ hΦ; induction m with
    | zero => exact hc.1
    | succ m ih => rw [pow_succ]; exact hc.2.2.2.2 _ Φ ih hΦ
  have hT_expand : ∀ k : ℕ, 0 < k →
      T_step (t / (k : ℝ)) =
        1 + ((k : ℂ)⁻¹) • A + ((((k : ℝ) ^ 2)⁻¹ : ℝ) : ℂ) • R := by
    intro k hk
    set ε : ℝ := t / (k : ℝ)
    apply ContinuousLinearMap.ext; intro X
    have h1_adj : (1 + (ε : ℂ) • B_eff)† = 1 + (ε : ℂ) • (B_eff†) := by
      change star (1 + (ε : ℂ) • B_eff) = _
      rw [star_add, star_one, star_smul, RCLike.star_def, Complex.conj_ofReal]; rfl
    have h_lin : B_eff† * X + X * B_eff + ∑ a ∈ s, (γ a : ℂ) • ((K a)† * X * K a) = L X := by
      rw [hB_adj]
      have h_rhs : L X = Complex.I • (H0 * X - X * H0) +
          ∑ a ∈ s, (γ a : ℂ) • ((K a)† * X * K a -
            (1 / 2 : ℂ) • ((K a)† * K a * X + X * ((K a)† * K a))) := by
        dsimp only [L]
        rw [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
          opCommutatorCLM_apply, opCommutator, ContinuousLinearMap.sum_apply]
        refine congrArg (Complex.I • (H0 * X - X * H0) + ·) (Finset.sum_congr rfl fun a _ => ?_)
        rw [ContinuousLinearMap.smul_apply, ContinuousLinearMap.sub_apply,
          ContinuousLinearMap.smul_apply, ContinuousLinearMap.add_apply,
          clmSandwichOp_apply, clmSandwichOp_apply, clmSandwichOp_apply, mul_one, one_mul]
      rw [h_rhs]
      dsimp only [B_eff, G]
      rw [sub_mul, clm_smul_mul_gkls, clm_smul_mul_gkls, Finset.sum_mul,
        mul_sub, clm_mul_smul_gkls, clm_mul_smul_gkls, Finset.mul_sum, neg_smul,
        show Complex.I • (H0 * X) - (1 / 2 : ℂ) • ∑ x ∈ s, ((γ x : ℂ) • ((K x)† * K x)) * X +
          (-(Complex.I • (X * H0)) - (1 / 2 : ℂ) • ∑ x ∈ s, X * ((γ x : ℂ) • ((K x)† * K x))) +
          ∑ a ∈ s, (γ a : ℂ) • ((K a)† * X * K a) =
          Complex.I • (H0 * X - X * H0) +
          (∑ a ∈ s, (γ a : ℂ) • ((K a)† * X * K a) -
           (1 / 2 : ℂ) • ∑ a ∈ s, (((γ a : ℂ) • ((K a)† * K a)) * X + X * ((γ a : ℂ) • ((K a)† * K a)))) by
            rw [smul_sub, Finset.sum_add_distrib, smul_add]; abel]
      congr 1
      rw [Finset.smul_sum, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [clm_smul_mul_gkls, clm_mul_smul_gkls, ← smul_add, smul_comm (1 / 2 : ℂ) (γ a : ℂ),
        ← smul_sub]
    dsimp only [T_step, A, R]
    rw [ContinuousLinearMap.add_apply, clmSandwichOp_apply, ContinuousLinearMap.sum_apply,
      ContinuousLinearMap.add_apply, ContinuousLinearMap.add_apply,
      ContinuousLinearMap.one_apply, ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.smul_apply, ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.smul_apply, clmSandwichOp_apply, h1_adj]
    have h_quad : (1 + (ε : ℂ) • (B_eff†)) * X * (1 + (ε : ℂ) • B_eff) =
        X + (ε : ℂ) • (B_eff† * X + X * B_eff) + ((ε ^ 2 : ℝ) : ℂ) • (B_eff† * X * B_eff) := by
      rw [add_mul, one_mul, mul_add, mul_one, add_mul, clm_smul_mul_gkls,
        clm_smul_mul_gkls, clm_mul_smul_gkls, clm_mul_smul_gkls, smul_smul, smul_add]
      have hε2 : (ε : ℂ) * (ε : ℂ) = ((ε ^ 2 : ℝ) : ℂ) := by push_cast; ring
      rw [hε2, mul_assoc]; abel
    have h_sum_ε : (∑ a ∈ s, (((ε * γ a : ℝ) : ℂ) • clmSandwichOp ((K a)†) (K a)) X) =
        (ε : ℂ) • ∑ a ∈ s, (γ a : ℂ) • ((K a)† * X * K a) := by
      rw [Finset.smul_sum]; refine Finset.sum_congr rfl fun a _ => ?_
      rw [ContinuousLinearMap.smul_apply, clmSandwichOp_apply, smul_smul]; congr 1; push_cast; ring
    have hε_eq : (ε : ℂ) = (k : ℂ)⁻¹ * (t : ℂ) := by dsimp [ε]; push_cast; ring
    have hε2_eq : ((ε ^ 2 : ℝ) : ℂ) = ((((k : ℝ) ^ 2)⁻¹ : ℝ) : ℂ) * ((t ^ 2 : ℝ) : ℂ) := by
      dsimp [ε]; push_cast; ring
    rw [h_quad, h_sum_ε]
    calc X + (ε : ℂ) • (B_eff† * X + X * B_eff) + ((ε ^ 2 : ℝ) : ℂ) • (B_eff† * X * B_eff) +
          (ε : ℂ) • ∑ a ∈ s, (γ a : ℂ) • ((K a)† * X * K a)
      _ = X + ((ε : ℂ) • (B_eff† * X + X * B_eff) +
            (ε : ℂ) • ∑ a ∈ s, (γ a : ℂ) • ((K a)† * X * K a)) +
          ((ε ^ 2 : ℝ) : ℂ) • (B_eff† * X * B_eff) := by abel
      _ = X + (ε : ℂ) • L X + ((ε ^ 2 : ℝ) : ℂ) • (B_eff† * X * B_eff) := by
          rw [← smul_add, h_lin]
      _ = _ := by rw [hε_eq, hε2_eq, smul_smul, smul_smul]
  refine isCompletelyPositiveMap_of_tendsto
    (fun m => (T_step (t / ((m + 1 : ℕ) : ℝ))) ^ (m + 1)) (NormedSpace.exp A)
    (fun m => hT_pow_cp (m + 1) _ (hT_cp _ (div_nonneg ht (Nat.cast_nonneg _)))) ?_
  have h_seq_eq : (fun m : ℕ => (T_step (t / ((m + 1 : ℕ) : ℝ))) ^ (m + 1)) =
      (fun m : ℕ =>
        (1 + (((m + 1 : ℕ) : ℂ)⁻¹) • A +
          (((((m + 1 : ℕ) : ℝ) ^ 2)⁻¹ : ℝ) : ℂ) • R) ^ (m + 1)) := by
    ext m : 1; rw [hT_expand (m + 1) (Nat.succ_pos m)]
  rw [h_seq_eq]
  exact normedAlgebra_euler_quadratic_tendsto_exp
    (𝔸 := (E →L[ℂ] E) →L[ℂ] (E →L[ℂ] E)) ContinuousLinearMap.norm_id_le A R
    superop_exp_norm_and_taylor2

lemma isCompletelyPositiveMap_opDaviesThermalSemigroup {D L_box : ℕ}
    {Site : BoxD D L_box → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (sys : IndexedCommutingProjectorHamiltonian D L_box Site ι)
    (β : ℝ)
    (couplings : Finset (SingleSiteThermalCoupling D L_box Site β))
    {t : ℝ} (ht : 0 ≤ t) :
    IsCompletelyPositiveMap (opDaviesThermalSemigroup sys β couplings t) := by
  let s := couplings ×ˢ Finset.Icc (-(Fintype.card ι : ℤ)) (Fintype.card ι : ℤ)
  have h_eq : opDaviesThermalGeneratorCLM sys β couplings =
      Complex.I • opCommutatorCLM sys.H0 +
        ∑ p ∈ s, (p.1.h_spec p.2 : ℂ) • (clmSandwichOp ((bohrEigenop sys p.1.S p.2)†) (bohrEigenop sys p.1.S p.2) -
          (1 / 2 : ℂ) • (clmSandwichOp ((bohrEigenop sys p.1.S p.2)† * bohrEigenop sys p.1.S p.2) 1 +
            clmSandwichOp 1 ((bohrEigenop sys p.1.S p.2)† * bohrEigenop sys p.1.S p.2))) := by
    dsimp [opDaviesThermalGeneratorCLM, s]; rw [Finset.sum_product]
  dsimp [opDaviesThermalSemigroup]
  rw [h_eq]
  exact superop_exp_isCompletelyPositive_gkls sys.H0 sys.isSelfAdjoint_H0 s
    (fun p => bohrEigenop sys p.1.S p.2) (fun p => p.1.h_spec p.2)
    (fun p _ => (p.1.kms_detailed_balance p.2).1) ht

end
