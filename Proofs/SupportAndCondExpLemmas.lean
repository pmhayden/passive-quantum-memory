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

import Defs.LocalHamiltonian
import Proofs.CylinderAlgebraAndSupport

/-!
# Partial-Trace Conditional Expectation, Group Twirling, and Commutator Localization

Proves spatial support containment and idempotence of the partial-trace conditional expectation `condExp` (`isSupportedOn_condExp`, `partialTrace_cylinderOp`, `condExp_eq_self_of_isSupportedOn`). Constructs the finite-dimensional Weyl–Heisenberg unitary twirling representation (`condExp_eq_twirl_sum`) to establish operator-norm contractivity (`norm_condExp_le`) and the commutator-to-conditional-expectation approximation bound (`norm_sub_condExp_le_of_commutator_bound`).

## References

* Part I, Section 6.2 (`subsec:bochner-lr`), Proposition 6.3 (`prop:bochner-time-convolution`)
* Part I, Section 7.1 (`subsec:single-cube-telescoping`), Proposition 7.2 (`prop:single-cube-telescoping`)
* Bravyi–Hastings–Michalakis (2010), Section 2; Bravyi–Hastings (2011), Section 2
-/

noncomputable section

open scoped Classical InnerProduct ComplexConjugate BigOperators
open ContinuousLinearMap

/-!
## 1. Normalized Partial-Trace Conditional Expectation Properties
-/

/-- The conditional expectation `condExp Site A O` is supported on $A$. -/
lemma isSupportedOn_condExp {D L : ℕ}
    (Site : BoxD D L → Type) [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    (A : Finset (BoxD D L))
    (O : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site) :
    IsSupportedOn Site A (condExp Site A O) :=
  ⟨_, rfl⟩

lemma combineConfig_inj_left {D L : ℕ} {Site : BoxD D L → Type}
    (A : Finset (BoxD D L)) (γ : LocalConfig Site (Finset.univ \ A))
    {α β : LocalConfig Site A}
    (h : combineConfig A α γ = combineConfig A β γ) : α = β := by
  have h1 := congrArg (restrictConfig A) h
  rwa [restrictConfig_combineConfig, restrictConfig_combineConfig] at h1

lemma sliceLp_basisVecGlobal_combineConfig {D L : ℕ} {Site : BoxD D L → Type}
    [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    (A : Finset (BoxD D L)) (β : LocalConfig Site A) (γ : LocalConfig Site (Finset.univ \ A)) :
    sliceLp A γ (basisVecGlobal Site (combineConfig A β γ)) = deltaLp β := by
  ext α
  change (if combineConfig A α γ = combineConfig A β γ then (1 : ℂ) else 0) =
    if α = β then 1 else 0
  by_cases h : α = β
  · subst h; simp
  · have hne : combineConfig A α γ ≠ combineConfig A β γ :=
      fun hc => h (combineConfig_inj_left A γ hc)
    simp [h, hne]

lemma partialTraceEntry_cylinderOp {D L : ℕ} {Site : BoxD D L → Type}
    [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    (A : Finset (BoxD D L))
    (O_loc : LocalHilbertSpace Site A →L[ℂ] LocalHilbertSpace Site A)
    (γ : LocalConfig Site (Finset.univ \ A))
    (α β : LocalConfig Site A) :
    partialTraceEntry Site A (cylinderOp Site A O_loc) γ α β =
      (O_loc (deltaLp β)).ofLp α := by
  dsimp [partialTraceEntry]
  rw [cylinderOp_apply_combineConfig, sliceLp_basisVecGlobal_combineConfig]

lemma partialTrace_cylinderOp {D L : ℕ} {Site : BoxD D L → Type}
    [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    (A : Finset (BoxD D L))
    (O_loc : LocalHilbertSpace Site A →L[ℂ] LocalHilbertSpace Site A) :
    partialTrace Site A (cylinderOp Site A O_loc) =
      (Fintype.card (LocalConfig Site (Finset.univ \ A)) : ℂ) • O_loc := by
  ext ψ_A α
  change (∑ γ : LocalConfig Site (Finset.univ \ A), ∑ β : LocalConfig Site A,
      partialTraceEntry Site A (cylinderOp Site A O_loc) γ α β * ψ_A.ofLp β) =
    (Fintype.card (LocalConfig Site (Finset.univ \ A)) : ℂ) * (O_loc ψ_A).ofLp α
  have h_inner : ∀ γ : LocalConfig Site (Finset.univ \ A),
      (∑ β : LocalConfig Site A,
        partialTraceEntry Site A (cylinderOp Site A O_loc) γ α β * ψ_A.ofLp β) =
      (O_loc ψ_A).ofLp α := by
    intro γ
    rw [clm_apply_ofLp_eq_sum O_loc ψ_A α]
    refine Finset.sum_congr rfl fun β _ => ?_
    rw [partialTraceEntry_cylinderOp, mul_comm]
  simp_rw [h_inner, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

/-- If $O$ is already supported on $A$, then `condExp Site A O = O` (projection property). -/
lemma condExp_eq_self_of_isSupportedOn {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    [∀ x, Nonempty (Site x)]
    {A : Finset (BoxD D L)}
    {O : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site}
    (hO : IsSupportedOn Site A O) :
    condExp Site A O = O := by
  rcases hO with ⟨O_loc, rfl⟩
  dsimp [condExp]
  rw [partialTrace_cylinderOp, smul_smul]
  have h_card_ne : (Fintype.card (LocalConfig Site (Finset.univ \ A)) : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  rw [inv_mul_cancel₀ h_card_ne, one_smul]

private def signChar {D L : ℕ} {Site : BoxD D L → Type}
    {B : Finset (BoxD D L)} (s : LocalConfig Site B → Bool) (γ : LocalConfig Site B) : ℂ :=
  if s γ then -1 else 1

private lemma signChar_mul_self {D L : ℕ} {Site : BoxD D L → Type}
    {B : Finset (BoxD D L)} (s : LocalConfig Site B → Bool) (γ : LocalConfig Site B) :
    signChar s γ * signChar s γ = 1 := by
  dsimp [signChar]
  cases s γ <;> norm_num

private lemma norm_signChar {D L : ℕ} {Site : BoxD D L → Type}
    {B : Finset (BoxD D L)} (s : LocalConfig Site B → Bool) (γ : LocalConfig Site B) :
    ‖signChar s γ‖ = 1 := by
  dsimp [signChar]
  cases s γ <;> simp

private def flipSignAt {D L : ℕ} {Site : BoxD D L → Type} [∀ x, DecidableEq (Site x)]
    {B : Finset (BoxD D L)} (γ : LocalConfig Site B) :
    (LocalConfig Site B → Bool) ≃ (LocalConfig Site B → Bool) where
  toFun s := Function.update s γ (!s γ)
  invFun s := Function.update s γ (!s γ)
  left_inv s := by
    ext x
    by_cases hx : x = γ
    · subst hx; simp
    · simp [hx]
  right_inv s := by
    ext x
    by_cases hx : x = γ
    · subst hx; simp
    · simp [hx]

private lemma sum_signChar_mul {D L : ℕ} {Site : BoxD D L → Type}
    [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    {B : Finset (BoxD D L)} (γ γ' : LocalConfig Site B) :
    (∑ s : LocalConfig Site B → Bool, signChar s γ * signChar s γ') =
      if γ = γ' then (Fintype.card (LocalConfig Site B → Bool) : ℂ) else 0 := by
  by_cases h : γ = γ'
  · subst h
    simp [signChar_mul_self]
  · rw [if_neg h]
    have h_flip : (∑ s : LocalConfig Site B → Bool, signChar s γ * signChar s γ') =
        ∑ s : LocalConfig Site B → Bool, -(signChar s γ * signChar s γ') := by
      rw [← (flipSignAt γ).sum_comp]
      refine Finset.sum_congr rfl fun s _ => ?_
      have h1 : signChar (flipSignAt γ s) γ = -signChar s γ := by
        dsimp [signChar, flipSignAt]
        rw [Function.update_self]
        cases s γ <;> norm_num
      have h2 : signChar (flipSignAt γ s) γ' = signChar s γ' := by
        dsimp [signChar, flipSignAt]
        rw [Function.update_of_ne (Ne.symm h)]
      rw [h1, h2, neg_mul]
    rw [Finset.sum_neg_distrib] at h_flip
    linear_combination (1 / 2 : ℂ) * h_flip

private noncomputable def localConfigZModEquiv {D L : ℕ} {Site : BoxD D L → Type}
    [∀ x, Fintype (Site x)] [∀ x, Nonempty (Site x)]
    (B : Finset (BoxD D L)) :
    LocalConfig Site B ≃ ZMod (Fintype.card (LocalConfig Site B)) :=
  haveI : NeZero (Fintype.card (LocalConfig Site B)) := ⟨Fintype.card_ne_zero⟩
  Fintype.equivOfCardEq (ZMod.card _).symm

private noncomputable def shiftLocalConfigEquiv {D L : ℕ} {Site : BoxD D L → Type}
    [∀ x, Fintype (Site x)] [∀ x, Nonempty (Site x)]
    (B : Finset (BoxD D L))
    (k : ZMod (Fintype.card (LocalConfig Site B))) :
    LocalConfig Site B ≃ LocalConfig Site B :=
  (localConfigZModEquiv B).trans ((Equiv.addRight k).trans (localConfigZModEquiv B).symm)

private noncomputable def orbitLocalConfigEquiv {D L : ℕ} {Site : BoxD D L → Type}
    [∀ x, Fintype (Site x)] [∀ x, Nonempty (Site x)]
    (B : Finset (BoxD D L))
    (γ : LocalConfig Site B) :
    ZMod (Fintype.card (LocalConfig Site B)) ≃ LocalConfig Site B :=
  (Equiv.addLeft (localConfigZModEquiv B γ)).trans (localConfigZModEquiv B).symm

private lemma sum_shiftLocalConfigEquiv {D L : ℕ} {Site : BoxD D L → Type}
    [∀ x, Fintype (Site x)] [∀ x, Nonempty (Site x)]
    (B : Finset (BoxD D L)) (γ : LocalConfig Site B)
    (f : LocalConfig Site B → ℂ) :
    letI : NeZero (Fintype.card (LocalConfig Site B)) := ⟨Fintype.card_ne_zero⟩
    (∑ k : ZMod (Fintype.card (LocalConfig Site B)), f (shiftLocalConfigEquiv B k γ)) =
      ∑ δ : LocalConfig Site B, f δ := by
  letI : NeZero (Fintype.card (LocalConfig Site B)) := ⟨Fintype.card_ne_zero⟩
  exact (orbitLocalConfigEquiv B γ).sum_comp f

private def signedPermLocalOp {D L : ℕ} {Site : BoxD D L → Type}
    [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    (B : Finset (BoxD D L))
    (π : LocalConfig Site B ≃ LocalConfig Site B)
    (η : LocalConfig Site B → ℂ) :
    LocalHilbertSpace Site B →L[ℂ] LocalHilbertSpace Site B :=
  LinearMap.toContinuousLinearMap
    { toFun := fun ψ_B => WithLp.toLp 2 (fun γ => η γ * ψ_B.ofLp (π γ))
      map_add' := fun ψ₁ ψ₂ => by
        ext γ
        change η γ * (ψ₁.ofLp (π γ) + ψ₂.ofLp (π γ)) =
          η γ * ψ₁.ofLp (π γ) + η γ * ψ₂.ofLp (π γ)
        ring
      map_smul' := fun c ψ => by
        ext γ
        change η γ * (c * ψ.ofLp (π γ)) = c * (η γ * ψ.ofLp (π γ))
        ring }

private lemma signedPermLocalOp_mul_inv {D L : ℕ} {Site : BoxD D L → Type}
    [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    (B : Finset (BoxD D L))
    (π : LocalConfig Site B ≃ LocalConfig Site B)
    (η : LocalConfig Site B → ℂ)
    (hη : ∀ γ, η γ * η γ = 1) :
    signedPermLocalOp B π η * signedPermLocalOp B π.symm (fun γ => η (π.symm γ)) = 1 := by
  ext ψ_B γ
  change η γ * (η (π.symm (π γ)) * ψ_B.ofLp (π.symm (π γ))) = ψ_B.ofLp γ
  rw [π.symm_apply_apply, ← mul_assoc, hη γ, one_mul]

private lemma cylinderOp_signedPermLocalOp_apply_combineConfig {D L : ℕ} {Site : BoxD D L → Type}
    [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    (A : Finset (BoxD D L))
    (π : LocalConfig Site (Finset.univ \ A) ≃ LocalConfig Site (Finset.univ \ A))
    (η : LocalConfig Site (Finset.univ \ A) → ℂ)
    (ψ : ManyBodyHilbertSpace Site)
    (α : LocalConfig Site A) (γ : LocalConfig Site (Finset.univ \ A)) :
    (cylinderOp Site (Finset.univ \ A) (signedPermLocalOp (Finset.univ \ A) π η) ψ).ofLp
        (combineConfig A α γ) =
      η γ * ψ.ofLp (combineConfig A α (π γ)) := by
  let B := Finset.univ \ A
  change η (restrictConfig B (combineConfig A α γ)) *
      ψ.ofLp (spliceConfig B (π (restrictConfig B (combineConfig A α γ))) (combineConfig A α γ)) =
    η γ * ψ.ofLp (combineConfig A α (π γ))
  rw [restrictConfig_compl_combineConfig, spliceConfig_compl_combineConfig]

private lemma norm_cylinderOp_signedPermLocalOp_le_one {D L : ℕ} {Site : BoxD D L → Type}
    [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    (A : Finset (BoxD D L))
    (π : LocalConfig Site (Finset.univ \ A) ≃ LocalConfig Site (Finset.univ \ A))
    (η : LocalConfig Site (Finset.univ \ A) → ℂ)
    (hη : ∀ γ, ‖η γ‖ = 1) :
    ‖cylinderOp Site (Finset.univ \ A) (signedPermLocalOp (Finset.univ \ A) π η)‖ ≤ 1 := by
  let W := cylinderOp Site (Finset.univ \ A) (signedPermLocalOp (Finset.univ \ A) π η)
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro ψ
  rw [one_mul]
  have h_sq : ‖W ψ‖ ^ 2 = ‖ψ‖ ^ 2 := by
    rw [PiLp.norm_sq_eq_of_L2, PiLp.norm_sq_eq_of_L2]
    rw [← (configEquiv (Site := Site) A).sum_comp, ← (configEquiv (Site := Site) A).sum_comp]
    rw [Fintype.sum_prod_type, Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun α _ => ?_
    dsimp [configEquiv]
    rw [← π.sum_comp (fun γ => ‖ψ.ofLp (combineConfig A α γ)‖ ^ 2)]
    refine Finset.sum_congr rfl fun γ _ => ?_
    change ‖(W ψ).ofLp (combineConfig A α γ)‖ ^ 2 = ‖ψ.ofLp (combineConfig A α (π γ))‖ ^ 2
    rw [cylinderOp_signedPermLocalOp_apply_combineConfig, norm_mul, hη γ, one_mul]
  nlinarith [norm_nonneg (W ψ), norm_nonneg ψ]

private noncomputable def twirlLeft {D L : ℕ} {Site : BoxD D L → Type}
    [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)] [∀ x, Nonempty (Site x)]
    (A : Finset (BoxD D L))
    (s : LocalConfig Site (Finset.univ \ A) → Bool)
    (k : ZMod (Fintype.card (LocalConfig Site (Finset.univ \ A)))) :
    ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site :=
  cylinderOp Site (Finset.univ \ A)
    (signedPermLocalOp (Finset.univ \ A) (shiftLocalConfigEquiv (Finset.univ \ A) k) (signChar s))

private noncomputable def twirlRight {D L : ℕ} {Site : BoxD D L → Type}
    [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)] [∀ x, Nonempty (Site x)]
    (A : Finset (BoxD D L))
    (s : LocalConfig Site (Finset.univ \ A) → Bool)
    (k : ZMod (Fintype.card (LocalConfig Site (Finset.univ \ A)))) :
    ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site :=
  cylinderOp Site (Finset.univ \ A)
    (signedPermLocalOp (Finset.univ \ A) (shiftLocalConfigEquiv (Finset.univ \ A) k).symm
      (fun γ => signChar s ((shiftLocalConfigEquiv (Finset.univ \ A) k).symm γ)))

private lemma twirlLeft_mul_twirlRight {D L : ℕ} {Site : BoxD D L → Type}
    [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)] [∀ x, Nonempty (Site x)]
    (A : Finset (BoxD D L))
    (s : LocalConfig Site (Finset.univ \ A) → Bool)
    (k : ZMod (Fintype.card (LocalConfig Site (Finset.univ \ A)))) :
    twirlLeft A s k * twirlRight A s k = 1 := by
  dsimp [twirlLeft, twirlRight]
  rw [cylinderOp_mul, signedPermLocalOp_mul_inv _ _ _ (signChar_mul_self s), cylinderOp_one]

private lemma isSupportedOn_twirlLeft {D L : ℕ} {Site : BoxD D L → Type}
    [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)] [∀ x, Nonempty (Site x)]
    (A : Finset (BoxD D L))
    (s : LocalConfig Site (Finset.univ \ A) → Bool)
    (k : ZMod (Fintype.card (LocalConfig Site (Finset.univ \ A)))) :
    IsSupportedOn Site (Finset.univ \ A) (twirlLeft A s k) :=
  ⟨_, rfl⟩

private lemma norm_twirlLeft_le_one {D L : ℕ} {Site : BoxD D L → Type}
    [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)] [∀ x, Nonempty (Site x)]
    (A : Finset (BoxD D L))
    (s : LocalConfig Site (Finset.univ \ A) → Bool)
    (k : ZMod (Fintype.card (LocalConfig Site (Finset.univ \ A)))) :
    ‖twirlLeft A s k‖ ≤ 1 :=
  norm_cylinderOp_signedPermLocalOp_le_one A _ _ (norm_signChar s)

private lemma norm_twirlRight_le_one {D L : ℕ} {Site : BoxD D L → Type}
    [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)] [∀ x, Nonempty (Site x)]
    (A : Finset (BoxD D L))
    (s : LocalConfig Site (Finset.univ \ A) → Bool)
    (k : ZMod (Fintype.card (LocalConfig Site (Finset.univ \ A)))) :
    ‖twirlRight A s k‖ ≤ 1 :=
  norm_cylinderOp_signedPermLocalOp_le_one A _ _ (fun _ => norm_signChar s _)

private lemma sum_twirl_signChar {D L : ℕ} {Site : BoxD D L → Type}
    [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)] [∀ x, Nonempty (Site x)]
    (A : Finset (BoxD D L))
    (O : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site)
    (k : ZMod (Fintype.card (LocalConfig Site (Finset.univ \ A))))
    (ψ : ManyBodyHilbertSpace Site)
    (α : LocalConfig Site A) (γ : LocalConfig Site (Finset.univ \ A)) :
    (∑ s : LocalConfig Site (Finset.univ \ A) → Bool,
      ((twirlLeft A s k * O * twirlRight A s k) ψ).ofLp (combineConfig A α γ)) =
    (Fintype.card (LocalConfig Site (Finset.univ \ A) → Bool) : ℂ) *
      ∑ β : LocalConfig Site A,
        partialTraceEntry Site A O (shiftLocalConfigEquiv (Finset.univ \ A) k γ) α β *
          ψ.ofLp (combineConfig A β γ) := by
  let B := Finset.univ \ A
  let π := shiftLocalConfigEquiv B k
  have h_pt : ∀ s : LocalConfig Site B → Bool,
      ((twirlLeft A s k * O * twirlRight A s k) ψ).ofLp (combineConfig A α γ) =
      ∑ β : LocalConfig Site A, ∑ γ'' : LocalConfig Site B,
        (signChar s γ * signChar s γ'') *
          ((O (basisVecGlobal Site (combineConfig A β (π γ'')))).ofLp (combineConfig A α (π γ)) *
            ψ.ofLp (combineConfig A β γ'')) := by
    intro s
    change (twirlLeft A s k (O (twirlRight A s k ψ))).ofLp (combineConfig A α γ) = _
    dsimp [twirlLeft]
    rw [cylinderOp_signedPermLocalOp_apply_combineConfig]
    rw [clm_apply_ofLp_eq_sum O (twirlRight A s k ψ) (combineConfig A α (π γ))]
    rw [← (configEquiv (Site := Site) A).sum_comp, Fintype.sum_prod_type, Finset.mul_sum]
    refine Finset.sum_congr rfl fun β _ => ?_
    rw [Finset.mul_sum, ← π.sum_comp]
    refine Finset.sum_congr rfl fun γ'' _ => ?_
    dsimp [configEquiv, twirlRight]
    rw [cylinderOp_signedPermLocalOp_apply_combineConfig, π.symm_apply_apply]
    have h_delta : deltaLp (combineConfig A β (π γ'')) =
        basisVecGlobal Site (combineConfig A β (π γ'')) := rfl
    rw [h_delta]
    ring
  simp_rw [h_pt]
  rw [Finset.sum_comm]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun β _ => ?_
  rw [Finset.sum_comm]
  have h_inner : ∀ γ'' : LocalConfig Site B,
      (∑ s : LocalConfig Site B → Bool,
        (signChar s γ * signChar s γ'') *
          ((O (basisVecGlobal Site (combineConfig A β (π γ'')))).ofLp (combineConfig A α (π γ)) *
            ψ.ofLp (combineConfig A β γ''))) =
      if γ = γ'' then
        (Fintype.card (LocalConfig Site B → Bool) : ℂ) *
          (partialTraceEntry Site A O (π γ) α β * ψ.ofLp (combineConfig A β γ))
      else 0 := by
    intro γ''
    rw [← Finset.sum_mul, sum_signChar_mul γ γ'']
    split_ifs with h
    · subst h
      rfl
    · ring
  rw [Finset.sum_congr rfl fun γ'' _ => h_inner γ'']
  simp only [Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte]
  rfl

private lemma condExp_eq_twirl_sum {D L : ℕ} {Site : BoxD D L → Type}
    [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)] [∀ x, Nonempty (Site x)]
    (A : Finset (BoxD D L))
    (O : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site) :
    letI : NeZero (Fintype.card (LocalConfig Site (Finset.univ \ A))) := ⟨Fintype.card_ne_zero⟩
    condExp Site A O =
      (((Fintype.card (LocalConfig Site (Finset.univ \ A) → Bool) : ℂ) *
        (Fintype.card (LocalConfig Site (Finset.univ \ A)) : ℂ))⁻¹) •
        ∑ k : ZMod (Fintype.card (LocalConfig Site (Finset.univ \ A))),
          ∑ s : LocalConfig Site (Finset.univ \ A) → Bool,
            twirlLeft A s k * O * twirlRight A s k := by
  letI : NeZero (Fintype.card (LocalConfig Site (Finset.univ \ A))) := ⟨Fintype.card_ne_zero⟩
  ext ψ σ
  obtain ⟨⟨α, γ⟩, rfl⟩ := (configEquiv (Site := Site) A).surjective σ
  dsimp [configEquiv]
  have h_lhs : (condExp Site A O ψ).ofLp (combineConfig A α γ) =
      (Fintype.card (LocalConfig Site (Finset.univ \ A)) : ℂ)⁻¹ *
        ∑ δ : LocalConfig Site (Finset.univ \ A), ∑ β : LocalConfig Site A,
          partialTraceEntry Site A O δ α β * ψ.ofLp (combineConfig A β γ) := by
    dsimp [condExp]
    rw [cylinderOp_apply_combineConfig]
    rfl
  rw [h_lhs, clm_ofLp_smul]
  simp only [clm_ofLp_sum]
  simp_rw [sum_twirl_signChar A O _ ψ α γ, ← Finset.mul_sum]
  have h_shift :
      (∑ k : ZMod (Fintype.card (LocalConfig Site (Finset.univ \ A))),
        ∑ β : LocalConfig Site A,
          partialTraceEntry Site A O (shiftLocalConfigEquiv (Finset.univ \ A) k γ) α β *
            ψ.ofLp (combineConfig A β γ)) =
      ∑ δ : LocalConfig Site (Finset.univ \ A), ∑ β : LocalConfig Site A,
        partialTraceEntry Site A O δ α β * ψ.ofLp (combineConfig A β γ) :=
    sum_shiftLocalConfigEquiv (Finset.univ \ A) γ (fun δ =>
      ∑ β : LocalConfig Site A, partialTraceEntry Site A O δ α β * ψ.ofLp (combineConfig A β γ))
  rw [h_shift]
  have h_card_bool : (Fintype.card (LocalConfig Site (Finset.univ \ A) → Bool) : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  rw [mul_inv, mul_comm ((Fintype.card (LocalConfig Site (Finset.univ \ A) → Bool) : ℂ)⁻¹),
    mul_assoc,
    ← mul_assoc (Fintype.card (LocalConfig Site (Finset.univ \ A) → Bool) : ℂ)⁻¹,
    inv_mul_cancel₀ h_card_bool, one_mul]

private lemma sub_eq_inv_card_smul_sum_sub {α β E : Type*} [Fintype α] [Fintype β]
    [Nonempty α] [Nonempty β] [NormedAddCommGroup E] [NormedSpace ℂ E]
    {N : ℕ} (hN : Fintype.card α = N)
    (O S : E) (f : α → β → E)
    (hS : S = (((Fintype.card β : ℂ) * (N : ℂ))⁻¹) • ∑ k : α, ∑ s : β, f k s) :
    O - S = (((Fintype.card β : ℂ) * (N : ℂ))⁻¹) •
      ∑ k : α, ∑ s : β, (O - f k s) := by
  subst hS
  subst hN
  have hα : (Fintype.card α : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have hβ : (Fintype.card β : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  simp only [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
    ← Nat.cast_smul_eq_nsmul ℂ, smul_sub, smul_smul]
  rw [mul_comm (Fintype.card α : ℂ), inv_mul_cancel₀ (mul_ne_zero hβ hα), one_smul]

private lemma norm_inv_card_smul_sum_le {α β E : Type*} [Fintype α] [Fintype β]
    [Nonempty α] [Nonempty β] [NormedAddCommGroup E] [NormedSpace ℂ E]
    {N : ℕ} (hN : Fintype.card α = N)
    (f : α → β → E) {C : ℝ} (hf : ∀ k s, ‖f k s‖ ≤ C) :
    ‖(((Fintype.card β : ℂ) * (N : ℂ))⁻¹) • ∑ k : α, ∑ s : β, f k s‖ ≤ C := by
  subst hN
  rw [norm_smul, norm_inv, norm_mul, Complex.norm_natCast, Complex.norm_natCast]
  have h_pos1 : (0 : ℝ) < Fintype.card β := Nat.cast_pos.mpr Fintype.card_pos
  have h_pos2 : (0 : ℝ) < Fintype.card α := Nat.cast_pos.mpr Fintype.card_pos
  have h_prod_pos : (0 : ℝ) < (Fintype.card β : ℝ) * (Fintype.card α : ℝ) :=
    mul_pos h_pos1 h_pos2
  have h_sum_le : ‖∑ k : α, ∑ s : β, f k s‖ ≤
      (Fintype.card α : ℝ) * ((Fintype.card β : ℝ) * C) := by
    calc ‖∑ k : α, ∑ s : β, f k s‖
      _ ≤ ∑ k : α, ‖∑ s : β, f k s‖ := norm_sum_le _ _
      _ ≤ ∑ k : α, ∑ s : β, ‖f k s‖ := Finset.sum_le_sum fun k _ => norm_sum_le _ _
      _ ≤ ∑ _k : α, ∑ _s : β, C :=
        Finset.sum_le_sum fun k _ => Finset.sum_le_sum fun s _ => hf k s
      _ = (Fintype.card α : ℝ) * ((Fintype.card β : ℝ) * C) := by
        simp [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  calc ((Fintype.card β : ℝ) * (Fintype.card α : ℝ))⁻¹ * ‖∑ k : α, ∑ s : β, f k s‖
    _ ≤ ((Fintype.card β : ℝ) * (Fintype.card α : ℝ))⁻¹ *
        ((Fintype.card α : ℝ) * ((Fintype.card β : ℝ) * C)) :=
      mul_le_mul_of_nonneg_left h_sum_le (inv_nonneg.mpr (le_of_lt h_prod_pos))
    _ = (((Fintype.card β : ℝ) * (Fintype.card α : ℝ))⁻¹ *
        ((Fintype.card β : ℝ) * (Fintype.card α : ℝ))) * C := by ring
    _ = C := by rw [inv_mul_cancel₀ (ne_of_gt h_prod_pos), one_mul]

/-- Contractivity of the partial-trace conditional expectation: $\|\mathbb{E}_A(O)\| \le \|O\|$. -/
lemma norm_condExp_le {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    [∀ x, Nonempty (Site x)]
    (A : Finset (BoxD D L))
    (O : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site) :
    ‖condExp Site A O‖ ≤ ‖O‖ := by
  letI : NeZero (Fintype.card (LocalConfig Site (Finset.univ \ A))) := ⟨Fintype.card_ne_zero⟩
  rw [condExp_eq_twirl_sum A O]
  refine norm_inv_card_smul_sum_le (ZMod.card _) _ (fun k s => ?_)
  calc ‖twirlLeft A s k * O * twirlRight A s k‖
    _ ≤ ‖twirlLeft A s k * O‖ * ‖twirlRight A s k‖ := norm_mul_le _ _
    _ ≤ (‖twirlLeft A s k‖ * ‖O‖) * ‖twirlRight A s k‖ :=
      mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _)
    _ ≤ (1 * ‖O‖) * 1 := by
      apply mul_le_mul (mul_le_mul_of_nonneg_right (norm_twirlLeft_le_one A s k) (norm_nonneg O))
        (norm_twirlRight_le_one A s k) (norm_nonneg _) (mul_nonneg zero_le_one (norm_nonneg O))
    _ = ‖O‖ := by ring

/-- Commutator-to-conditional-expectation bound: if `condExp Site A O` is supported on $A$ and
    every operator $Y$ supported on $A^c$ satisfies $\|[O, Y]\| \le \varepsilon \|Y\|$, then
    $\|O - \mathbb{E}_A(O)\| \le \varepsilon$. -/
lemma norm_sub_condExp_le_of_commutator_bound {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    [∀ x, Nonempty (Site x)]
    (A : Finset (BoxD D L))
    (O : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site)
    {ε : ℝ} (hε : 0 ≤ ε)
    (h_comm : ∀ Y : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site,
      IsSupportedOn Site (Finset.univ \ A) Y → ‖opCommutator O Y‖ ≤ ε * ‖Y‖) :
    ‖O - condExp Site A O‖ ≤ ε := by
  letI : NeZero (Fintype.card (LocalConfig Site (Finset.univ \ A))) := ⟨Fintype.card_ne_zero⟩
  rw [sub_eq_inv_card_smul_sum_sub (ZMod.card _) O (condExp Site A O) _ (condExp_eq_twirl_sum A O)]
  refine norm_inv_card_smul_sum_le (ZMod.card _) _ (fun k s => ?_)
  have h_id : O - twirlLeft A s k * O * twirlRight A s k =
      opCommutator O (twirlLeft A s k) * twirlRight A s k := by
    dsimp [opCommutator]
    rw [sub_mul, mul_assoc O (twirlLeft A s k) (twirlRight A s k),
      twirlLeft_mul_twirlRight A s k, mul_one]
  rw [h_id]
  have h_comm_ks : ‖opCommutator O (twirlLeft A s k)‖ ≤ ε := by
    calc ‖opCommutator O (twirlLeft A s k)‖
      _ ≤ ε * ‖twirlLeft A s k‖ := h_comm (twirlLeft A s k) (isSupportedOn_twirlLeft A s k)
      _ ≤ ε * 1 := mul_le_mul_of_nonneg_left (norm_twirlLeft_le_one A s k) hε
      _ = ε := mul_one ε
  calc ‖opCommutator O (twirlLeft A s k) * twirlRight A s k‖
    _ ≤ ‖opCommutator O (twirlLeft A s k)‖ * ‖twirlRight A s k‖ := norm_mul_le _ _
    _ ≤ ε * 1 := mul_le_mul h_comm_ks (norm_twirlRight_le_one A s k) (norm_nonneg _) hε
    _ = ε := mul_one ε

end
