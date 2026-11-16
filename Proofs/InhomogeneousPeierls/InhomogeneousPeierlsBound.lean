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

import Proofs.InhomogeneousPeierls.GridSnapPullbackAndImmunity

/-!
# Quantum Gibbs Failure Bound via Factorized Pinning and Walsh-Fourier Witness Peeling

Factorizes the quantum Gibbs partition function of an inhomogeneous CSS Hamiltonian into unused-slot Z-pinning modes and independent X/Z check-syndrome sectors (`factorized_gibbs_ratio_le`). Applies F2 Walsh-Fourier coset peeling (`gibbsFailureProb_staticCSS_le_of_witnesses`) and calibrates the macroscopic free-energy barrier scaling against witness multiplicity (`bdlFreeEnergyBarrier_le_clusterRawWeight`, `witness_card_mul_exp_le_half_barrier`).

## References

* Part I, Section 5.3 (`subsec:walsh-fourier-peierls`), Theorem 5.5 (`thm:walsh-fourier-peierls`)
* Part I, Section 5.4 (`subsec:safe-decoded-observables`), Proposition 5.7 (`prop:safe-subspace-immunity`)
* Part II, Section 3.3 (`subsec:walsh-coset-peeling`), Proposition 3.5 (`prop:witness-coset-reduction`), Proposition 3.6 (`prop:walsh-coset-dominance`)
-/

noncomputable section

open scoped Classical BigOperators InnerProduct ComplexConjugate
open ContinuousLinearMap WeldedHierarchy WeldedHierarchy.BDLDecoder

set_option linter.constructorNameAsVariable false
set_option linter.unusedVariables false
set_option maxRecDepth 200000
set_option maxHeartbeats 800000

/-! ## 1. Polymorphic Realizable Syndrome Embedding & Factorized Partition Ratio -/

def embedCheckBits {I M : Type} (f : M → I) (s : M → ZMod 2) (ix : I) : Bool :=
  if h : ∃ m : M, f m = ix then decide (s (Classical.choose h) ≠ 0) else false

def pullCheckBits {I M : Type} (f : M → I) (σ : I → Bool) (m : M) : ZMod 2 :=
  boolToZMod2 (σ (f m))

def embedSynGen {P I_X I_Z M_X M_Z : Type}
    (fX : M_X → I_X) (fZ : M_Z → I_Z)
    (s_pin : P → Bool) (s_X : M_X → ZMod 2) (s_Z : M_Z → ZMod 2) :
    P ⊕ I_X ⊕ I_Z → Bool
  | Sum.inl p => s_pin p
  | Sum.inr (Sum.inl ix) => embedCheckBits fX s_X ix
  | Sum.inr (Sum.inr iz) => embedCheckBits fZ s_Z iz

def pinWeightGen {P : Type} [Fintype P] (s_pin : P → Bool) : ℝ :=
  ((Finset.univ.filter (fun p : P => s_pin p = true)).card : ℝ)

lemma pullCheckBits_embedCheckBits {I M : Type}
    {f : M → I} (hf : Function.Injective f) (s : M → ZMod 2) :
    pullCheckBits f (embedCheckBits f s) = s := by
  ext m
  dsimp [pullCheckBits, embedCheckBits]
  have hex : ∃ m' : M, f m' = f m := ⟨m, rfl⟩
  rw [dif_pos hex, hf (Classical.choose_spec hex)]
  rcases _root_.zmod2_eq_zero_or_one (s m) with h0 | h1 <;> [rw [h0]; rw [h1]] <;> rfl

lemma embedSynGen_injective {P I_X I_Z M_X M_Z : Type}
    {fX : M_X → I_X} {fZ : M_Z → I_Z}
    (hfX : Function.Injective fX) (hfZ : Function.Injective fZ) :
    Function.Injective (fun t : (P → Bool) × (M_X → ZMod 2) × (M_Z → ZMod 2) =>
      embedSynGen fX fZ t.1 t.2.1 t.2.2) := by
  intro ⟨p₁, x₁, z₁⟩ ⟨p₂, x₂, z₂⟩ h
  have hp : p₁ = p₂ := funext fun p => congr_fun h (Sum.inl p)
  have hx : x₁ = x₂ := by
    rw [← pullCheckBits_embedCheckBits hfX x₁, ← pullCheckBits_embedCheckBits hfX x₂]
    ext mX; exact congr_arg boolToZMod2 (congr_fun h (Sum.inr (Sum.inl (fX mX))))
  have hz : z₁ = z₂ := by
    rw [← pullCheckBits_embedCheckBits hfZ z₁, ← pullCheckBits_embedCheckBits hfZ z₂]
    ext mZ; exact congr_arg boolToZMod2 (congr_fun h (Sum.inr (Sum.inr (fZ mZ))))
  exact Prod.ext hp (Prod.ext hx hz)

lemma sum_filter_embedCheckBits_eq {I M : Type} [Fintype I] [DecidableEq I]
    [Fintype M] [DecidableEq M] {f : M → I} (hf : Function.Injective f) (s : M → ZMod 2) :
    (∑ ix ∈ Finset.univ.filter (fun ix : I => embedCheckBits f s ix = true), (1 : ℝ)) =
      WeldedHierarchy.syndromeWeight s := by
  have h_set : Finset.univ.filter (fun ix : I => embedCheckBits f s ix = true) =
      (Finset.univ.filter (fun m : M => s m ≠ 0)).image f := by
    ext ix
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
    constructor
    · intro h_tr
      dsimp [embedCheckBits] at h_tr
      split_ifs at h_tr with hex
      exact ⟨Classical.choose hex, of_decide_eq_true h_tr, Classical.choose_spec hex⟩
    · rintro ⟨m, hm, rfl⟩
      dsimp [embedCheckBits]
      have hex : ∃ m' : M, f m' = f m := ⟨m, rfl⟩
      rw [dif_pos hex, hf (Classical.choose_spec hex)]
      exact decide_eq_true hm
  rw [Finset.sum_const, nsmul_eq_mul, mul_one, h_set,
    Finset.card_image_of_injective _ hf]
  rfl

lemma sum_filter_embedSynGen_eq {P I_X I_Z M_X M_Z : Type}
    [Fintype P] [DecidableEq P] [Fintype I_X] [DecidableEq I_X] [Fintype I_Z] [DecidableEq I_Z]
    [Fintype M_X] [DecidableEq M_X] [Fintype M_Z] [DecidableEq M_Z]
    {fX : M_X → I_X} {fZ : M_Z → I_Z}
    (hfX : Function.Injective fX) (hfZ : Function.Injective fZ)
    (wt : P ⊕ I_X ⊕ I_Z → ℝ) (hwt : ∀ i, wt i = 1)
    (s_pin : P → Bool) (s_X : M_X → ZMod 2) (s_Z : M_Z → ZMod 2) :
    (∑ i ∈ Finset.univ.filter (fun i : P ⊕ I_X ⊕ I_Z =>
        embedSynGen fX fZ s_pin s_X s_Z i = true), wt i) =
      pinWeightGen s_pin + WeldedHierarchy.syndromeWeight s_X + WeldedHierarchy.syndromeWeight s_Z := by
  have h_congr : (∑ i ∈ Finset.univ.filter (fun i : P ⊕ I_X ⊕ I_Z =>
        embedSynGen fX fZ s_pin s_X s_Z i = true), wt i) =
      ∑ i ∈ Finset.univ.filter (fun i : P ⊕ I_X ⊕ I_Z =>
        embedSynGen fX fZ s_pin s_X s_Z i = true), (1 : ℝ) :=
    Finset.sum_congr rfl fun i _ => hwt i
  rw [h_congr, Finset.sum_filter, Fintype.sum_sum_type, Fintype.sum_sum_type]
  have h1 : (∑ x : P, if embedSynGen fX fZ s_pin s_X s_Z (Sum.inl x) = true then (1 : ℝ) else 0) =
      ∑ x ∈ Finset.univ.filter (fun x : P => s_pin x = true), (1 : ℝ) := by
    rw [Finset.sum_filter]; rfl
  have h2 : (∑ x : I_X, if embedSynGen fX fZ s_pin s_X s_Z (Sum.inr (Sum.inl x)) = true then (1 : ℝ) else 0) =
      ∑ x ∈ Finset.univ.filter (fun x : I_X => embedCheckBits fX s_X x = true), (1 : ℝ) := by
    rw [Finset.sum_filter]; rfl
  have h3 : (∑ x : I_Z, if embedSynGen fX fZ s_pin s_X s_Z (Sum.inr (Sum.inr x)) = true then (1 : ℝ) else 0) =
      ∑ x ∈ Finset.univ.filter (fun x : I_Z => embedCheckBits fZ s_Z x = true), (1 : ℝ) := by
    rw [Finset.sum_filter]; rfl
  rw [h1, h2, h3,
    sum_filter_embedCheckBits_eq hfX s_X, sum_filter_embedCheckBits_eq hfZ s_Z]
  have h_pin : (∑ x ∈ Finset.univ.filter (fun x : P => s_pin x = true), (1 : ℝ)) =
      pinWeightGen s_pin := by
    rw [Finset.sum_const, nsmul_eq_mul, mul_one]; rfl
  rw [h_pin, add_assoc]

lemma factorized_gibbs_ratio_le {P I_X I_Z M_X M_Z : Type}
    [Fintype P] [DecidableEq P] [Fintype I_X] [DecidableEq I_X] [Fintype I_Z] [DecidableEq I_Z]
    [Fintype M_X] [DecidableEq M_X] [Fintype M_Z] [DecidableEq M_Z]
    {fX : M_X → I_X} {fZ : M_Z → I_Z}
    (hfX : Function.Injective fX) (hfZ : Function.Injective fZ)
    (S_pin : Finset (P → Bool))
    (ImX FailX : Finset (M_X → ZMod 2))
    (ImZ FailZ : Finset (M_Z → ZMod 2))
    (Safe : Finset (P ⊕ I_X ⊕ I_Z → Bool))
    (wt : (P ⊕ I_X ⊕ I_Z → Bool) → ℝ)
    (tr : (P ⊕ I_X ⊕ I_Z → Bool) → ℝ)
    (T0 β r : ℝ)
    (hr0 : 0 ≤ r)
    (htr_nonneg : ∀ σ, 0 ≤ tr σ)
    (hT0 : 0 ≤ T0)
    (hwt_eq : ∀ p sX sZ, wt (embedSynGen fX fZ p sX sZ) =
      pinWeightGen p + WeldedHierarchy.syndromeWeight sX + WeldedHierarchy.syndromeWeight sZ)
    (htr_eq : ∀ p ∈ S_pin, ∀ sX ∈ ImX, ∀ sZ ∈ ImZ, tr (embedSynGen fX fZ p sX sZ) = T0)
    (h_realizable : ∀ σ, tr σ ≠ 0 →
      ∃ p ∈ S_pin, ∃ sX ∈ ImX, ∃ sZ ∈ ImZ, σ = embedSynGen fX fZ p sX sZ)
    (h_unsafe : ∀ p ∈ S_pin, ∀ sX ∈ ImX, ∀ sZ ∈ ImZ,
      embedSynGen fX fZ p sX sZ ∉ Safe → sX ∈ FailX ∨ sZ ∈ FailZ)
    (hrX : (∑ sX ∈ FailX, Real.exp (-β * WeldedHierarchy.syndromeWeight sX)) ≤
      (r / 2) * ∑ sX ∈ ImX, Real.exp (-β * WeldedHierarchy.syndromeWeight sX))
    (hrZ : (∑ sZ ∈ FailZ, Real.exp (-β * WeldedHierarchy.syndromeWeight sZ)) ≤
      (r / 2) * ∑ sZ ∈ ImZ, Real.exp (-β * WeldedHierarchy.syndromeWeight sZ)) :
    (∑ σ ∈ Finset.univ \ Safe, Real.exp (-β * wt σ) * tr σ) ≤
      r * ∑ σ : P ⊕ I_X ⊕ I_Z → Bool, Real.exp (-β * wt σ) * tr σ := by
  let emb : (P → Bool) × (M_X → ZMod 2) × (M_Z → ZMod 2) → (P ⊕ I_X ⊕ I_Z → Bool) :=
    fun t => embedSynGen fX fZ t.1 t.2.1 t.2.2
  let g : (P ⊕ I_X ⊕ I_Z → Bool) → ℝ := fun σ => Real.exp (-β * wt σ) * tr σ
  have hg_nonneg : ∀ σ, 0 ≤ g σ := fun σ => mul_nonneg (le_of_lt (Real.exp_pos _)) (htr_nonneg σ)
  let f_pin : (P → Bool) → ℝ := fun p => Real.exp (-β * pinWeightGen p)
  let f_X : (M_X → ZMod 2) → ℝ := fun sX => Real.exp (-β * WeldedHierarchy.syndromeWeight sX)
  let f_Z : (M_Z → ZMod 2) → ℝ := fun sZ => Real.exp (-β * WeldedHierarchy.syndromeWeight sZ)
  have h_prod_sum : ∀ (A : Finset (P → Bool)) (B : Finset (M_X → ZMod 2)) (C : Finset (M_Z → ZMod 2)),
      (∀ p ∈ A, ∀ sX ∈ B, ∀ sZ ∈ C, tr (emb (p, sX, sZ)) = T0) →
      (∑ t ∈ A ×ˢ (B ×ˢ C), g (emb t)) =
        T0 * (∑ p ∈ A, f_pin p) * (∑ sX ∈ B, f_X sX) * (∑ sZ ∈ C, f_Z sZ) := by
    intro A B C h_tr_ABC
    rw [Finset.sum_product]
    have h_inner : ∀ p ∈ A, (∑ y ∈ B ×ˢ C, g (emb (p, y))) =
        T0 * f_pin p * (∑ sX ∈ B, f_X sX) * (∑ sZ ∈ C, f_Z sZ) := by
      intro p hp
      rw [Finset.sum_product]
      have h_in2 : ∀ sX ∈ B, (∑ sZ ∈ C, g (emb (p, sX, sZ))) =
          T0 * f_pin p * f_X sX * (∑ sZ ∈ C, f_Z sZ) := by
        intro sX hsX
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun sZ hsZ => ?_
        dsimp [g, emb, f_pin, f_X, f_Z]
        rw [h_tr_ABC p hp sX hsX sZ hsZ, hwt_eq p sX sZ]
        have h_exp : Real.exp (-β * (pinWeightGen p + WeldedHierarchy.syndromeWeight sX + WeldedHierarchy.syndromeWeight sZ)) =
            Real.exp (-β * pinWeightGen p) * Real.exp (-β * WeldedHierarchy.syndromeWeight sX) *
              Real.exp (-β * WeldedHierarchy.syndromeWeight sZ) := by
          rw [← Real.exp_add, ← Real.exp_add]; ring_nf
        rw [h_exp]; ring
      rw [Finset.sum_congr rfl h_in2, ← Finset.sum_mul, ← Finset.mul_sum]
    rw [Finset.sum_congr rfl h_inner, ← Finset.sum_mul, ← Finset.sum_mul, ← Finset.mul_sum]
  have hZ_pin_nonneg : 0 ≤ ∑ p ∈ S_pin, f_pin p :=
    Finset.sum_nonneg fun _ _ => le_of_lt (Real.exp_pos _)
  have hZ_X_nonneg : 0 ≤ ∑ sX ∈ ImX, f_X sX :=
    Finset.sum_nonneg fun _ _ => le_of_lt (Real.exp_pos _)
  have hZ_Z_nonneg : 0 ≤ ∑ sZ ∈ ImZ, f_Z sZ :=
    Finset.sum_nonneg fun _ _ => le_of_lt (Real.exp_pos _)
  have h_denom : T0 * (∑ p ∈ S_pin, f_pin p) * (∑ sX ∈ ImX, f_X sX) * (∑ sZ ∈ ImZ, f_Z sZ) ≤
      ∑ σ : P ⊕ I_X ⊕ I_Z → Bool, g σ := by
    rw [← h_prod_sum S_pin ImX ImZ htr_eq]
    have h_inj : Set.InjOn emb ↑(S_pin ×ˢ (ImX ×ˢ ImZ)) :=
      fun _ _ _ _ h => embedSynGen_injective hfX hfZ h
    rw [← Finset.sum_image h_inj]
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun _ _ _ => hg_nonneg _)
  let U1 := S_pin ×ˢ ((ImX ∩ FailX) ×ˢ ImZ)
  let U2 := S_pin ×ˢ (ImX ×ˢ (ImZ ∩ FailZ))
  have h_num_filter : (∑ σ ∈ Finset.univ \ Safe, g σ) =
      ∑ σ ∈ (Finset.univ \ Safe).filter (fun σ => tr σ ≠ 0), g σ := by
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl fun σ _ => ?_
    by_cases h0 : tr σ ≠ 0
    · rw [if_pos h0]
    · push_neg at h0; rw [if_neg (not_not.mpr h0)]; dsimp [g]; rw [h0, mul_zero]
  have h_sub_union : (Finset.univ \ Safe).filter (fun σ => tr σ ≠ 0) ⊆
      U1.image emb ∪ U2.image emb := by
    intro σ hσ
    rcases Finset.mem_filter.mp hσ with ⟨h_not_safe, htr_nz⟩
    have h_ns : σ ∉ Safe := (Finset.mem_sdiff.mp h_not_safe).2
    obtain ⟨p, hp, sX, hsX, sZ, hsZ, rfl⟩ := h_realizable σ htr_nz
    rcases h_unsafe p hp sX hsX sZ hsZ h_ns with hFX | hFZ
    · exact Finset.mem_union_left _ (Finset.mem_image.mpr
        ⟨(p, sX, sZ), Finset.mem_product.mpr ⟨hp, Finset.mem_product.mpr ⟨Finset.mem_inter.mpr ⟨hsX, hFX⟩, hsZ⟩⟩, rfl⟩)
    · exact Finset.mem_union_right _ (Finset.mem_image.mpr
        ⟨(p, sX, sZ), Finset.mem_product.mpr ⟨hp, Finset.mem_product.mpr ⟨hsX, Finset.mem_inter.mpr ⟨hsZ, hFZ⟩⟩⟩, rfl⟩)
  have h_U1_sum : (∑ t ∈ U1, g (emb t)) ≤
      T0 * (∑ p ∈ S_pin, f_pin p) * ((r / 2) * ∑ sX ∈ ImX, f_X sX) * (∑ sZ ∈ ImZ, f_Z sZ) := by
    rw [h_prod_sum S_pin (ImX ∩ FailX) ImZ
      (fun p hp sX hsX sZ hsZ => htr_eq p hp sX (Finset.mem_inter.mp hsX).1 sZ hsZ)]
    have h_le_FX : (∑ sX ∈ ImX ∩ FailX, f_X sX) ≤ (r / 2) * ∑ sX ∈ ImX, f_X sX :=
      (Finset.sum_le_sum_of_subset_of_nonneg Finset.inter_subset_right
        (fun _ _ _ => le_of_lt (Real.exp_pos _))).trans hrX
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left h_le_FX (mul_nonneg hT0 hZ_pin_nonneg)) hZ_Z_nonneg
  have h_U2_sum : (∑ t ∈ U2, g (emb t)) ≤
      T0 * (∑ p ∈ S_pin, f_pin p) * (∑ sX ∈ ImX, f_X sX) * ((r / 2) * ∑ sZ ∈ ImZ, f_Z sZ) := by
    rw [h_prod_sum S_pin ImX (ImZ ∩ FailZ)
      (fun p hp sX hsX sZ hsZ => htr_eq p hp sX hsX sZ (Finset.mem_inter.mp hsZ).1)]
    have h_le_FZ : (∑ sZ ∈ ImZ ∩ FailZ, f_Z sZ) ≤ (r / 2) * ∑ sZ ∈ ImZ, f_Z sZ :=
      (Finset.sum_le_sum_of_subset_of_nonneg Finset.inter_subset_right
        (fun _ _ _ => le_of_lt (Real.exp_pos _))).trans hrZ
    exact mul_le_mul_of_nonneg_left h_le_FZ
      (mul_nonneg (mul_nonneg hT0 hZ_pin_nonneg) hZ_X_nonneg)
  calc (∑ σ ∈ Finset.univ \ Safe, g σ)
    _ = ∑ σ ∈ (Finset.univ \ Safe).filter (fun σ => tr σ ≠ 0), g σ := h_num_filter
    _ ≤ ∑ σ ∈ U1.image emb ∪ U2.image emb, g σ :=
      Finset.sum_le_sum_of_subset_of_nonneg h_sub_union (fun _ _ _ => hg_nonneg _)
    _ ≤ (∑ σ ∈ U1.image emb, g σ) + ∑ σ ∈ U2.image emb, g σ := by
      have h_ui := Finset.sum_union_inter (s₁ := U1.image emb) (s₂ := U2.image emb) (f := g)
      have h_pos : 0 ≤ ∑ σ ∈ U1.image emb ∩ U2.image emb, g σ :=
        Finset.sum_nonneg fun _ _ => hg_nonneg _
      linarith
    _ ≤ (∑ t ∈ U1, g (emb t)) + ∑ t ∈ U2, g (emb t) :=
      add_le_add (Finset.sum_image_le_of_nonneg fun _ _ => hg_nonneg _)
        (Finset.sum_image_le_of_nonneg fun _ _ => hg_nonneg _)
    _ ≤ T0 * (∑ p ∈ S_pin, f_pin p) * ((r / 2) * ∑ sX ∈ ImX, f_X sX) * (∑ sZ ∈ ImZ, f_Z sZ) +
        T0 * (∑ p ∈ S_pin, f_pin p) * (∑ sX ∈ ImX, f_X sX) * ((r / 2) * ∑ sZ ∈ ImZ, f_Z sZ) :=
      add_le_add h_U1_sum h_U2_sum
    _ = r * (T0 * (∑ p ∈ S_pin, f_pin p) * (∑ sX ∈ ImX, f_X sX) * (∑ sZ ∈ ImZ, f_Z sZ)) := by ring
    _ ≤ r * ∑ σ : P ⊕ I_X ⊕ I_Z → Bool, g σ := mul_le_mul_of_nonneg_left h_denom hr0

/-! ## 2. Polymorphic Witness-Peeling Coset Bound & Quantum Gibbs Reduction -/

lemma witness_fail_sum_le_of_sum_coset_peel {Q M_Z M_X : Type}
    [Fintype Q] [DecidableEq Q] [Fintype M_Z] [DecidableEq M_Z] [Fintype M_X] [DecidableEq M_X]
    (code : CSSCode3D Q M_Z M_X)
    (W : Finset (M_X → ZMod 2)) (β r_half : ℝ)
    (hβ : 0 ≤ β)
    (h_sum : (∑ c ∈ W, Real.exp (-β * WeldedHierarchy.syndromeWeight c)) ≤ r_half) :
    let Im := Finset.univ.image (syndrome code)
    let Fail := Im.filter (fun s => ∃ c ∈ W, ∀ m : M_X, c m ≠ 0 → s m ≠ 0)
    (∑ s ∈ Fail, Real.exp (-β * WeldedHierarchy.syndromeWeight s)) ≤
      r_half * ∑ u ∈ Im, Real.exp (-β * WeldedHierarchy.syndromeWeight u) := by
  intro Im Fail
  let Z := ∑ u ∈ Im, Real.exp (-β * WeldedHierarchy.syndromeWeight u)
  have hZ_nonneg : 0 ≤ Z := Finset.sum_nonneg fun _ _ => le_of_lt (Real.exp_pos _)
  let F : (M_X → ZMod 2) → Finset (M_X → ZMod 2) :=
    fun c => Fail.filter (fun s => ∀ m : M_X, c m ≠ 0 → s m ≠ 0)
  have h_cov : Fail ⊆ W.biUnion F := by
    intro s hs
    obtain ⟨c, hcW, hcs⟩ := (Finset.mem_filter.mp hs).2
    exact Finset.mem_biUnion.mpr ⟨c, hcW, Finset.mem_filter.mpr ⟨hs, hcs⟩⟩
  have h_each_c : ∀ c ∈ W,
      (∑ s ∈ F c, Real.exp (-β * WeldedHierarchy.syndromeWeight s)) ≤
        Real.exp (-β * WeldedHierarchy.syndromeWeight c) * Z := by
    intro c hcW
    have h_term : ∀ s ∈ F c,
        Real.exp (-β * WeldedHierarchy.syndromeWeight s) ≤
          Real.exp (-β * WeldedHierarchy.syndromeWeight c) *
            Real.exp (-β * WeldedHierarchy.syndromeWeight (c + s)) := by
      intro s hsF
      have h_sub : ∀ m : M_X, c m ≠ 0 → s m ≠ 0 := (Finset.mem_filter.mp hsF).2
      have h_peel := (syndromeWeight_peel_of_subsupport s c h_sub).2
      have h_add_comm : s + c = c + s := add_comm s c
      rw [h_peel, h_add_comm, ← Real.exp_add]
      exact Real.exp_le_exp.mpr (by linarith)
    have h_fc_sub : F c ⊆ Im :=
      fun s hsF => (Finset.mem_filter.mp (Finset.mem_filter.mp hsF).1).1
    calc (∑ s ∈ F c, Real.exp (-β * WeldedHierarchy.syndromeWeight s))
      _ ≤ ∑ s ∈ F c, (Real.exp (-β * WeldedHierarchy.syndromeWeight c) *
            Real.exp (-β * WeldedHierarchy.syndromeWeight (c + s))) :=
          Finset.sum_le_sum h_term
      _ = Real.exp (-β * WeldedHierarchy.syndromeWeight c) *
            ∑ s ∈ F c, Real.exp (-β * WeldedHierarchy.syndromeWeight (c + s)) := by
          rw [← Finset.mul_sum]
      _ ≤ Real.exp (-β * WeldedHierarchy.syndromeWeight c) *
            ∑ u ∈ Im, Real.exp (-β * WeldedHierarchy.syndromeWeight (c + u)) :=
          mul_le_mul_of_nonneg_left
            (Finset.sum_le_sum_of_subset_of_nonneg h_fc_sub fun _ _ _ => le_of_lt (Real.exp_pos _))
            (le_of_lt (Real.exp_pos _))
      _ ≤ Real.exp (-β * WeldedHierarchy.syndromeWeight c) * Z :=
          mul_le_mul_of_nonneg_left (coset_syndromeWeight_sum_le code β hβ c) (le_of_lt (Real.exp_pos _))
  calc (∑ s ∈ Fail, Real.exp (-β * WeldedHierarchy.syndromeWeight s))
    _ ≤ ∑ s ∈ W.biUnion F, Real.exp (-β * WeldedHierarchy.syndromeWeight s) :=
        Finset.sum_le_sum_of_subset_of_nonneg h_cov fun _ _ _ => le_of_lt (Real.exp_pos _)
    _ ≤ ∑ c ∈ W, ∑ s ∈ F c, Real.exp (-β * WeldedHierarchy.syndromeWeight s) :=
        sum_biUnion_le_of_nonneg W F _ fun _ => le_of_lt (Real.exp_pos _)
    _ ≤ ∑ c ∈ W, (Real.exp (-β * WeldedHierarchy.syndromeWeight c) * Z) := Finset.sum_le_sum h_each_c
    _ = (∑ c ∈ W, Real.exp (-β * WeldedHierarchy.syndromeWeight c)) * Z := by
        rw [← Finset.sum_mul]
    _ ≤ r_half * Z := mul_le_mul_of_nonneg_right h_sum hZ_nonneg

lemma witness_fail_sum_le_of_coset_peel {Q M_Z M_X : Type}
    [Fintype Q] [DecidableEq Q] [Fintype M_Z] [DecidableEq M_Z] [Fintype M_X] [DecidableEq M_X]
    (code : CSSCode3D Q M_Z M_X)
    (W : Finset (M_X → ZMod 2)) (w β r_half : ℝ)
    (hβ : 0 ≤ β)
    (hw : ∀ c ∈ W, w ≤ WeldedHierarchy.syndromeWeight c)
    (h_card : (W.card : ℝ) * Real.exp (-β * w) ≤ r_half) :
    let Im := Finset.univ.image (syndrome code)
    let Fail := Im.filter (fun s => ∃ c ∈ W, ∀ m : M_X, c m ≠ 0 → s m ≠ 0)
    (∑ s ∈ Fail, Real.exp (-β * WeldedHierarchy.syndromeWeight s)) ≤
      r_half * ∑ u ∈ Im, Real.exp (-β * WeldedHierarchy.syndromeWeight u) := by
  refine witness_fail_sum_le_of_sum_coset_peel code W β r_half hβ ?_
  calc (∑ c ∈ W, Real.exp (-β * WeldedHierarchy.syndromeWeight c))
    _ ≤ ∑ _c ∈ W, Real.exp (-β * w) := Finset.sum_le_sum fun c hc =>
        Real.exp_le_exp.mpr (by have := hw c hc; nlinarith)
    _ = (W.card : ℝ) * Real.exp (-β * w) := by rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ r_half := h_card

lemma gibbsFailureProb_staticCSS_le_of_witness_sums
    {L q_code m_max : ℕ}
    (sys : IndexedCommutingProjectorHamiltonian 3 L
      (UniformSite3D L (CodeSlotConfig q_code))
      (StaticCSSCheckIdx L q_code m_max))
    {Q M_Z M_X : Type}
    [Fintype Q] [DecidableEq Q] [Fintype M_Z] [DecidableEq M_Z] [Fintype M_X] [DecidableEq M_X]
    (code : CSSCode3D Q M_Z M_X)
    {fX : M_X → Box3D L × Fin m_max} {fZ : M_Z → Box3D L × Fin m_max}
    (hfX : Function.Injective fX) (hfZ : Function.Injective fZ)
    (P_pin : (BoxSlot3D L q_code → Bool) → Prop)
    (W_Z : Finset (M_X → ZMod 2))
    (W_X : Finset (M_Z → ZMod 2))
    (Safe : Finset (StaticCSSCheckIdx L q_code m_max → Bool))
    (β r : ℝ)
    (hβ : 0 ≤ β) (hr0 : 0 ≤ r)
    (hwt_one : ∀ i : StaticCSSCheckIdx L q_code m_max, sys.weight i = 1)
    (hWZ_sum : (∑ c ∈ W_Z, Real.exp (-β * WeldedHierarchy.syndromeWeight c)) ≤ r / 2)
    (hWX_sum : (∑ c ∈ W_X, Real.exp (-β * WeldedHierarchy.syndromeWeight c)) ≤ r / 2)
    (htr_eq : ∀ p : BoxSlot3D L q_code → Bool, P_pin p → ∀ e_X e_Z : Q → ZMod 2,
      hilbertTrace (sys.syndromeProjector
        (embedSynGen fX fZ p (syndrome code e_X) (syndrome (dualCode code) e_Z))) =
        hilbertTrace sys.P0)
    (h_realizable : ∀ σ, sys.syndromeProjector σ ≠ 0 →
      ∃ p : BoxSlot3D L q_code → Bool, P_pin p ∧ ∃ e_X e_Z : Q → ZMod 2,
        σ = embedSynGen fX fZ p (syndrome code e_X) (syndrome (dualCode code) e_Z))
    (h_unsafe : ∀ p : BoxSlot3D L q_code → Bool, P_pin p →
      ∀ (sX : M_X → ZMod 2) (sZ : M_Z → ZMod 2),
      embedSynGen fX fZ p sX sZ ∉ Safe →
        (∃ c ∈ W_Z, ∀ mX : M_X, c mX ≠ 0 → sX mX ≠ 0) ∨
        (∃ c ∈ W_X, ∀ mZ : M_Z, c mZ ≠ 0 → sZ mZ ≠ 0)) :
    gibbsFailureProb sys.H0 sys.isSelfAdjoint_H0 β
      (1 - syndromeSubsetProj sys Safe) ≤ r := by
  let S_pin : Finset (BoxSlot3D L q_code → Bool) :=
    @Finset.filter _ P_pin (fun _ => Classical.propDecidable _) Finset.univ
  have h_mem_pin : ∀ p : BoxSlot3D L q_code → Bool, p ∈ S_pin ↔ P_pin p := by
    intro p; simp [S_pin]
  let ImX := Finset.univ.image (syndrome code)
  let FailX := ImX.filter (fun sX => ∃ c ∈ W_Z, ∀ mX : M_X, c mX ≠ 0 → sX mX ≠ 0)
  let ImZ := Finset.univ.image (syndrome (dualCode code))
  let FailZ := ImZ.filter (fun sZ => ∃ c ∈ W_X, ∀ mZ : M_Z, c mZ ≠ 0 → sZ mZ ≠ 0)
  have hrX : (∑ sX ∈ FailX, Real.exp (-β * WeldedHierarchy.syndromeWeight sX)) ≤
      (r / 2) * ∑ sX ∈ ImX, Real.exp (-β * WeldedHierarchy.syndromeWeight sX) :=
    witness_fail_sum_le_of_sum_coset_peel code W_Z β (r / 2) hβ hWZ_sum
  have hrZ : (∑ sZ ∈ FailZ, Real.exp (-β * WeldedHierarchy.syndromeWeight sZ)) ≤
      (r / 2) * ∑ sZ ∈ ImZ, Real.exp (-β * WeldedHierarchy.syndromeWeight sZ) :=
    witness_fail_sum_le_of_sum_coset_peel (dualCode code) W_X β (r / 2) hβ hWX_sum
  have hT0_nonneg : 0 ≤ hilbertTrace sys.P0 := by
    rw [← (syndrome_resolution_indexed sys).1]
    exact hilbertTrace_syndromeProjector_nonneg sys (fun _ => false)
  have hwt_eq : ∀ p sX sZ,
      sys.syndromeEnergy (embedSynGen fX fZ p sX sZ) =
        pinWeightGen p + WeldedHierarchy.syndromeWeight sX + WeldedHierarchy.syndromeWeight sZ := by
    intro p sX sZ
    dsimp [IndexedCommutingProjectorHamiltonian.syndromeEnergy]
    exact sum_filter_embedSynGen_eq hfX hfZ sys.weight hwt_one p sX sZ
  have htr_im : ∀ p ∈ S_pin, ∀ sX ∈ ImX, ∀ sZ ∈ ImZ,
      hilbertTrace (sys.syndromeProjector (embedSynGen fX fZ p sX sZ)) = hilbertTrace sys.P0 := by
    intro p hp sX hsX sZ hsZ
    rcases Finset.mem_image.mp hsX with ⟨e_X, _, rfl⟩
    rcases Finset.mem_image.mp hsZ with ⟨e_Z, _, rfl⟩
    exact htr_eq p ((h_mem_pin p).mp hp) e_X e_Z
  have h_real_im : ∀ σ, hilbertTrace (sys.syndromeProjector σ) ≠ 0 →
      ∃ p ∈ S_pin, ∃ sX ∈ ImX, ∃ sZ ∈ ImZ, σ = embedSynGen fX fZ p sX sZ := by
    intro σ htr_nz
    have h_proj_nz : sys.syndromeProjector σ ≠ 0 := by
      intro h0; apply htr_nz; rw [h0]; unfold hilbertTrace; simp
    obtain ⟨p, hp, e_X, e_Z, rfl⟩ := h_realizable σ h_proj_nz
    exact ⟨p, (h_mem_pin p).mpr hp,
      syndrome code e_X, Finset.mem_image_of_mem _ (Finset.mem_univ _),
      syndrome (dualCode code) e_Z, Finset.mem_image_of_mem _ (Finset.mem_univ _), rfl⟩
  have h_unsafe_im : ∀ p ∈ S_pin, ∀ sX ∈ ImX, ∀ sZ ∈ ImZ,
      embedSynGen fX fZ p sX sZ ∉ Safe → sX ∈ FailX ∨ sZ ∈ FailZ := by
    intro p hp sX hsX sZ hsZ h_ns
    rcases h_unsafe p ((h_mem_pin p).mp hp) sX sZ h_ns with hFX | hFZ
    · exact Or.inl (Finset.mem_filter.mpr ⟨hsX, hFX⟩)
    · exact Or.inr (Finset.mem_filter.mpr ⟨hsZ, hFZ⟩)
  have h_ratio := factorized_gibbs_ratio_le hfX hfZ S_pin ImX FailX ImZ FailZ Safe
    sys.syndromeEnergy (fun σ => hilbertTrace (sys.syndromeProjector σ))
    (hilbertTrace sys.P0) β r hr0
    (hilbertTrace_syndromeProjector_nonneg sys) hT0_nonneg
    hwt_eq htr_im h_real_im h_unsafe_im hrX hrZ
  (try dsimp only at h_ratio)
  rw [← gibbsPartitionZ_eq_sum_syndromeProjector sys β] at h_ratio
  have h_sub_proj := (syndromeSubsetProj_props sys Safe).2.2.2.2
  dsimp [gibbsFailureProb]
  rw [h_sub_proj]
  dsimp [syndromeSubsetProj]
  rw [Finset.mul_sum, hilbertTrace_sum]
  have h_sum_eq : (∑ x ∈ Finset.univ \ Safe,
      hilbertTrace (gibbsDensityOp (opEigenbasis sys.H0 sys.isSelfAdjoint_H0)
        (opEigenvalues sys.H0 sys.isSelfAdjoint_H0) β * sys.syndromeProjector x)) =
      (gibbsPartitionZ (opEigenvalues sys.H0 sys.isSelfAdjoint_H0) β)⁻¹ *
        ∑ x ∈ Finset.univ \ Safe,
          Real.exp (-β * sys.syndromeEnergy x) * hilbertTrace (sys.syndromeProjector x) := by
    refine (Finset.sum_congr rfl fun σ _ =>
      hilbertTrace_gibbsDensityOp_mul_syndromeProjector sys β σ).trans ?_
    rw [← Finset.mul_sum]
  rw [h_sum_eq]
  have hZ_pos : 0 < gibbsPartitionZ (opEigenvalues sys.H0 sys.isSelfAdjoint_H0) β :=
    gibbsPartitionZ_pos _ β
  calc (gibbsPartitionZ (opEigenvalues sys.H0 sys.isSelfAdjoint_H0) β)⁻¹ *
        (∑ x ∈ Finset.univ \ Safe,
          Real.exp (-β * sys.syndromeEnergy x) * hilbertTrace (sys.syndromeProjector x))
    _ ≤ (gibbsPartitionZ (opEigenvalues sys.H0 sys.isSelfAdjoint_H0) β)⁻¹ *
          (r * gibbsPartitionZ (opEigenvalues sys.H0 sys.isSelfAdjoint_H0) β) :=
      mul_le_mul_of_nonneg_left h_ratio (inv_nonneg.mpr (le_of_lt hZ_pos))
    _ = r * ((gibbsPartitionZ (opEigenvalues sys.H0 sys.isSelfAdjoint_H0) β)⁻¹ *
          gibbsPartitionZ (opEigenvalues sys.H0 sys.isSelfAdjoint_H0) β) := by ring
    _ = r := by rw [inv_mul_cancel₀ (ne_of_gt hZ_pos), mul_one]

lemma gibbsFailureProb_staticCSS_le_of_witnesses
    {L q_code m_max : ℕ}
    (sys : IndexedCommutingProjectorHamiltonian 3 L
      (UniformSite3D L (CodeSlotConfig q_code))
      (StaticCSSCheckIdx L q_code m_max))
    {Q M_Z M_X : Type}
    [Fintype Q] [DecidableEq Q] [Fintype M_Z] [DecidableEq M_Z] [Fintype M_X] [DecidableEq M_X]
    (code : CSSCode3D Q M_Z M_X)
    {fX : M_X → Box3D L × Fin m_max} {fZ : M_Z → Box3D L × Fin m_max}
    (hfX : Function.Injective fX) (hfZ : Function.Injective fZ)
    (P_pin : (BoxSlot3D L q_code → Bool) → Prop)
    (W_Z : Finset (M_X → ZMod 2))
    (W_X : Finset (M_Z → ZMod 2))
    (Safe : Finset (StaticCSSCheckIdx L q_code m_max → Bool))
    (w β r : ℝ)
    (hβ : 0 ≤ β) (hr0 : 0 ≤ r)
    (hwt_one : ∀ i : StaticCSSCheckIdx L q_code m_max, sys.weight i = 1)
    (hWZ_wt : ∀ c ∈ W_Z, w ≤ WeldedHierarchy.syndromeWeight c)
    (hWX_wt : ∀ c ∈ W_X, w ≤ WeldedHierarchy.syndromeWeight c)
    (hWZ_card : (W_Z.card : ℝ) * Real.exp (-β * w) ≤ r / 2)
    (hWX_card : (W_X.card : ℝ) * Real.exp (-β * w) ≤ r / 2)
    (htr_eq : ∀ p : BoxSlot3D L q_code → Bool, P_pin p → ∀ e_X e_Z : Q → ZMod 2,
      hilbertTrace (sys.syndromeProjector
        (embedSynGen fX fZ p (syndrome code e_X) (syndrome (dualCode code) e_Z))) =
        hilbertTrace sys.P0)
    (h_realizable : ∀ σ, sys.syndromeProjector σ ≠ 0 →
      ∃ p : BoxSlot3D L q_code → Bool, P_pin p ∧ ∃ e_X e_Z : Q → ZMod 2,
        σ = embedSynGen fX fZ p (syndrome code e_X) (syndrome (dualCode code) e_Z))
    (h_unsafe : ∀ p : BoxSlot3D L q_code → Bool, P_pin p →
      ∀ (sX : M_X → ZMod 2) (sZ : M_Z → ZMod 2),
      embedSynGen fX fZ p sX sZ ∉ Safe →
        (∃ c ∈ W_Z, ∀ mX : M_X, c mX ≠ 0 → sX mX ≠ 0) ∨
        (∃ c ∈ W_X, ∀ mZ : M_Z, c mZ ≠ 0 → sZ mZ ≠ 0)) :
    gibbsFailureProb sys.H0 sys.isSelfAdjoint_H0 β
      (1 - syndromeSubsetProj sys Safe) ≤ r := by
  have hWZ_sum : (∑ c ∈ W_Z, Real.exp (-β * WeldedHierarchy.syndromeWeight c)) ≤ r / 2 := by
    calc (∑ c ∈ W_Z, Real.exp (-β * WeldedHierarchy.syndromeWeight c))
      _ ≤ ∑ _c ∈ W_Z, Real.exp (-β * w) := Finset.sum_le_sum fun c hc =>
          Real.exp_le_exp.mpr (by have := hWZ_wt c hc; nlinarith)
      _ = (W_Z.card : ℝ) * Real.exp (-β * w) := by rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ r / 2 := hWZ_card
  have hWX_sum : (∑ c ∈ W_X, Real.exp (-β * WeldedHierarchy.syndromeWeight c)) ≤ r / 2 := by
    calc (∑ c ∈ W_X, Real.exp (-β * WeldedHierarchy.syndromeWeight c))
      _ ≤ ∑ _c ∈ W_X, Real.exp (-β * w) := Finset.sum_le_sum fun c hc =>
          Real.exp_le_exp.mpr (by have := hWX_wt c hc; nlinarith)
      _ = (W_X.card : ℝ) * Real.exp (-β * w) := by rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ r / 2 := hWX_card
  exact gibbsFailureProb_staticCSS_le_of_witness_sums sys code hfX hfZ P_pin W_Z W_X Safe β r
    hβ hr0 hwt_one hWZ_sum hWX_sum htr_eq h_realizable h_unsafe

lemma safeAndDecoded_props_of_commute {D L : ℕ} {Site : BoxD D L → Type}
    [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)] {ι : Type} [Fintype ι] [DecidableEq ι]
    (sys : IndexedCommutingProjectorHamiltonian D L Site ι)
    (Z_log X_log : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site)
    (hP0_ne_zero : sys.P0 ≠ 0)
    (hZ_sa : IsSelfAdjoint Z_log) (hZ_inv : Z_log * Z_log = 1)
    (hZ_comm : ∀ i : ι, Commute (sys.checkProj i) Z_log)
    (hX_sa : IsSelfAdjoint X_log) (hX_inv : X_log * X_log = 1)
    (hX_comm : ∀ i : ι, Commute (sys.checkProj i) X_log)
    (S_safe : Finset (ι → Bool))
    (h0_mem : (fun _ => false) ∈ S_safe)
    (hPi_ne_one : syndromeSubsetProj sys S_safe ≠ 1)
    (sgn_Z sgn_X : (ι → Bool) → ZMod 2)
    (h_sgnZ0 : sgn_Z (fun _ => false) = 0)
    (h_sgnX0 : sgn_X (fun _ => false) = 0) :
    let Pi_safe := syndromeSubsetProj sys S_safe
    let O_dec_Z := Z_log * syndromeSignOp sys sgn_Z
    let O_dec_X := X_log * syndromeSignOp sys sgn_X
    (IsStarProjection Pi_safe ∧ Pi_safe ≠ 0 ∧ Pi_safe ≠ 1 ∧
      Commute sys.H0 Pi_safe ∧ sys.P0 * Pi_safe = sys.P0) ∧
    (IsSelfAdjoint O_dec_Z ∧ O_dec_Z * O_dec_Z = 1 ∧ ‖O_dec_Z‖ ≤ 1 ∧
      Commute sys.H0 O_dec_Z ∧ O_dec_Z * sys.P0 = Z_log * sys.P0 ∧
      Pi_safe * (sys.P0 - O_dec_Z * sys.P0 * O_dec_Z†) * Pi_safe = 0) ∧
    (IsSelfAdjoint O_dec_X ∧ O_dec_X * O_dec_X = 1 ∧ ‖O_dec_X‖ ≤ 1 ∧
      Commute sys.H0 O_dec_X ∧ O_dec_X * sys.P0 = X_log * sys.P0 ∧
      Pi_safe * (sys.P0 - O_dec_X * sys.P0 * O_dec_X†) * Pi_safe = 0) := by
  intro Pi_safe O_dec_Z O_dec_X
  have h_safe := syndromeSubsetProj_props sys S_safe
  have hP0_Pi : sys.P0 * Pi_safe = sys.P0 := h_safe.2.2.2.1 h0_mem
  have hPi_ne_zero : Pi_safe ≠ 0 := by
    intro h0
    have h_eq : sys.P0 * Pi_safe = 0 := by rw [h0, mul_zero]
    exact hP0_ne_zero (hP0_Pi.symm.trans h_eq)
  have h_dec_Z := decodedObservable_props sys hZ_sa hZ_inv (fun i => (hZ_comm i).symm)
    sgn_Z h_sgnZ0 Pi_safe
  have h_dec_X := decodedObservable_props sys hX_sa hX_inv (fun i => (hX_comm i).symm)
    sgn_X h_sgnX0 Pi_safe
  exact ⟨⟨h_safe.1, hPi_ne_zero, hPi_ne_one, h_safe.2.1, hP0_Pi⟩, h_dec_Z, h_dec_X⟩

/-! ## 3. Calibrated Free-Energy Barrier Inequalities -/

lemma bdlFreeEnergyBarrier_le_clusterRawWeight (k : ℕ) {β : ℝ} (hβ : β > betaCritBDL) :
    bdlFreeEnergyBarrier k β ≤ (β - betaCritBDL) * (clusterRawWeight k : ℝ) := by
  have hb_pos : (0 : ℝ) < (bBDL : ℝ) := Nat.cast_pos.mpr b_bdl_pos
  have hb_ge1 : (1 : ℝ) ≤ (bBDL : ℝ) := by exact_mod_cast Nat.succ_le_of_lt b_bdl_pos
  have hlog_b : 0 ≤ Real.log (bBDL : ℝ) := Real.log_nonneg hb_ge1
  have h_log32 : 0 < Real.log (3 / 2 : ℝ) := Real.log_pos (by norm_num)
  have hL_pos : (0 : ℝ) < ((bdlBoxSide k ^ 3 : ℕ) : ℝ) :=
    Nat.cast_pos.mpr (Nat.pow_pos (Nat.pow_pos b_bdl_pos))
  have h_pow_eq : ((bdlBoxSide k ^ 3 : ℕ) : ℝ) = (bBDL : ℝ) ^ (6 * (k + 2)) := by
    dsimp [bdlBoxSide, bdlPeriodL, bdlHierarchySteps]
    rw [← Nat.pow_mul]
    have hexp : (2 * k + 4) * 3 = 6 * (k + 2) := by omega
    rw [hexp, Nat.cast_pow]
  have h_eta_mul : (6 * Real.log (bBDL : ℝ)) * etaBDL ≤ Real.log (3 / 2 : ℝ) := by
    dsimp [etaBDL]
    have h_den : 0 < 6 * Real.log (bBDL : ℝ) + 1 := by linarith
    rw [mul_div_assoc', div_le_iff₀ h_den]
    nlinarith
  have h_rpow_le : (((bdlBoxSide k ^ 3 : ℕ) : ℝ) ^ etaBDL) ≤ (9 / 4 : ℝ) * (3 / 2 : ℝ) ^ k := by
    rw [Real.rpow_def_of_pos hL_pos, h_pow_eq, Real.log_pow]
    have h_cast : ((6 * (k + 2) : ℕ) : ℝ) * Real.log (bBDL : ℝ) * etaBDL =
        ((k + 2 : ℕ) : ℝ) * ((6 * Real.log (bBDL : ℝ)) * etaBDL) := by push_cast; ring
    rw [h_cast]
    have h_le_log : ((k + 2 : ℕ) : ℝ) * ((6 * Real.log (bBDL : ℝ)) * etaBDL) ≤
        Real.log ((3 / 2 : ℝ) ^ (k + 2)) := by
      rw [Real.log_pow]
      exact mul_le_mul_of_nonneg_left h_eta_mul (by positivity)
    have h_32_pos : (0 : ℝ) < (3 / 2 : ℝ) ^ (k + 2) := by positivity
    calc Real.exp (((k + 2 : ℕ) : ℝ) * ((6 * Real.log (bBDL : ℝ)) * etaBDL))
      _ ≤ Real.exp (Real.log ((3 / 2 : ℝ) ^ (k + 2))) := Real.exp_le_exp.mpr h_le_log
      _ = (3 / 2 : ℝ) ^ (k + 2) := Real.exp_log h_32_pos
      _ = (9 / 4 : ℝ) * (3 / 2 : ℝ) ^ k := by ring
  have hcF_le : cFBDL * (9 / 4 : ℝ) ≤ 1 := by
    dsimp [cFBDL]
    have hb12 : (1 : ℝ) ≤ ((bBDL ^ 12 : ℕ) : ℝ) := by
      exact_mod_cast Nat.succ_le_of_lt (Nat.pow_pos b_bdl_pos)
    have h_den_pos : (0 : ℝ) < 6 * ((bBDL ^ 12 : ℕ) : ℝ) := by linarith
    rw [div_mul_eq_mul_div, div_le_iff₀ h_den_pos]
    linarith
  have hw_le := three_div_two_pow_le_clusterRawWeight k
  have hcF_pos : 0 ≤ cFBDL := le_of_lt c_f_bdl_pos
  have hβ_sub : 0 ≤ β - betaCritBDL := by linarith
  dsimp [bdlFreeEnergyBarrier]
  calc cFBDL * (β - betaCritBDL) * (((bdlBoxSide k ^ 3 : ℕ) : ℝ) ^ etaBDL)
    _ ≤ cFBDL * (β - betaCritBDL) * ((9 / 4 : ℝ) * (3 / 2 : ℝ) ^ k) :=
      mul_le_mul_of_nonneg_left h_rpow_le (mul_nonneg hcF_pos hβ_sub)
    _ = (cFBDL * (9 / 4 : ℝ)) * (β - betaCritBDL) * (3 / 2 : ℝ) ^ k := by ring
    _ ≤ 1 * (β - betaCritBDL) * (clusterRawWeight k : ℝ) := by
      have h1 : (cFBDL * (9 / 4 : ℝ)) * (β - betaCritBDL) ≤ 1 * (β - betaCritBDL) :=
        mul_le_mul_of_nonneg_right hcF_le hβ_sub
      exact mul_le_mul h1 hw_le (by positivity) (by linarith)
    _ = (β - betaCritBDL) * (clusterRawWeight k : ℝ) := by ring

lemma witness_card_mul_exp_le_half_barrier (k : ℕ) {N_card : ℕ}
    (hN : N_card ≤ (bdlClusterStepBase ^ 8) ^ (clusterRawWeight k))
    {β : ℝ} (hβ : β > betaCritBDL) :
    (N_card : ℝ) * Real.exp (-β * (clusterRawWeight k : ℝ)) ≤
      Real.exp (- bdlFreeEnergyBarrier k β) / 2 := by
  let B8 : ℝ := ((bdlClusterStepBase ^ 8 : ℕ) : ℝ)
  let w : ℝ := (clusterRawWeight k : ℝ)
  have hB8_pos : 0 < B8 := by
    have : 2 ≤ bdlClusterStepBase := bdlClusterStepBase_ge_two
    dsimp [B8]; positivity
  have hw_ge1 : (1 : ℝ) ≤ w := by
    have h1 : (1 : ℝ) ≤ (3 / 2 : ℝ) ^ k := one_le_pow₀ (by norm_num)
    exact h1.trans (three_div_two_pow_le_clusterRawWeight k)
  have hN_cast : (N_card : ℝ) ≤ B8 ^ (clusterRawWeight k) := by
    dsimp [B8]; exact_mod_cast hN
  have hB8_pow : B8 ^ (clusterRawWeight k) = Real.exp (w * Real.log B8) := by
    rw [← Real.exp_log hB8_pos, ← Real.exp_nat_mul, Real.log_exp]
  have h_log_B8 := log_bdlClusterStepBase_pow_eight_le_beta_c_BDL
  have h_bar := bdlFreeEnergyBarrier_le_clusterRawWeight k hβ
  have h_exp_arg : w * Real.log B8 + -β * w ≤ -1 + - bdlFreeEnergyBarrier k β := by
    have h1 : w * Real.log B8 ≤ w * (betaCritBDL - 100) :=
      mul_le_mul_of_nonneg_left (by dsimp [B8]; linarith) (by linarith)
    nlinarith
  have hexp_neg1 : Real.exp (-1) ≤ 1 / 2 := by
    have hexp1 : (2 : ℝ) ≤ Real.exp 1 := by
      have h := Real.add_one_le_exp 1; linarith
    rw [Real.exp_neg, one_div]
    exact inv_anti₀ (by norm_num) hexp1
  calc (N_card : ℝ) * Real.exp (-β * w)
    _ ≤ B8 ^ (clusterRawWeight k) * Real.exp (-β * w) :=
      mul_le_mul_of_nonneg_right hN_cast (le_of_lt (Real.exp_pos _))
    _ = Real.exp (w * Real.log B8 + -β * w) := by rw [hB8_pow, ← Real.exp_add]
    _ ≤ Real.exp (-1 + - bdlFreeEnergyBarrier k β) := Real.exp_le_exp.mpr h_exp_arg
    _ = Real.exp (-1) * Real.exp (- bdlFreeEnergyBarrier k β) := Real.exp_add _ _
    _ ≤ (1 / 2) * Real.exp (- bdlFreeEnergyBarrier k β) :=
      mul_le_mul_of_nonneg_right hexp_neg1 (le_of_lt (Real.exp_pos _))
    _ = Real.exp (- bdlFreeEnergyBarrier k β) / 2 := by ring

end
