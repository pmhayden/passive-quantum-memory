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

/-!
# Cylinder Operator Algebra, Spatial Support Closure, and Disjoint Commutativity

Develops the *-algebra homomorphism properties of `cylinderOp` (`cylinderOp_one`, `cylinderOp_add`, `cylinderOp_mul`, `cylinderOp_adjoint`, `cylinderOp_liftLocalOp`) and spatial support closure of `IsSupportedOn` under linear combinations, products, and adjoints. Proves that operators supported on disjoint finite lattice regions commute (`commute_of_isSupportedOn_disjoint`) and establishes spatial locality of local ground projectors for both cube-indexed and general indexed commuting-projector Hamiltonians.

## References

* Part I, Section 6.1 (`subsec:dsuper-banach`), Definition 6.1 (`def:banach-quasilocal`)
* Part I, Section 7.1 (`subsec:single-cube-telescoping`), Lemma 7.1 (`lem:norm-transfer`)
* Part II, Section 2 (`subsec:setup`), Definition 2.3 (`def:perturbation-class`)
-/

noncomputable section

open scoped Classical InnerProduct ComplexConjugate BigOperators
open ContinuousLinearMap

/-!
## 1. Configuration Splicing Identities and Cylinder $C^*$-Algebra Homomorphism Laws
-/

/-- Splicing the restriction of $\sigma$ to $A$ back onto $\sigma$ recovers $\sigma$. -/
lemma spliceConfig_restrictConfig {D L : ℕ} {Site : BoxD D L → Type}
    (A : Finset (BoxD D L)) (σ : ManyBodyConfig Site) :
    spliceConfig A (restrictConfig A σ) σ = σ := by
  funext x
  simp [spliceConfig, restrictConfig]

/-- Overwriting a configuration on $A$ twice is equivalent to the second overwrite alone. -/
lemma spliceConfig_idem {D L : ℕ} {Site : BoxD D L → Type}
    (A : Finset (BoxD D L)) (α β : LocalConfig Site A) (σ : ManyBodyConfig Site) :
    spliceConfig A β (spliceConfig A α σ) = spliceConfig A β σ := by
  ext x
  simp only [spliceConfig]
  split_ifs <;> rfl

/-- Restricting a spliced configuration `spliceConfig A α σ` to $A$ recovers $\alpha$. -/
lemma restrictConfig_spliceConfig {D L : ℕ} {Site : BoxD D L → Type}
    (A : Finset (BoxD D L)) (α : LocalConfig Site A) (σ : ManyBodyConfig Site) :
    restrictConfig A (spliceConfig A α σ) = α := by
  ext ⟨x, hx⟩
  simp [restrictConfig, spliceConfig, hx]

/-- The cylinder embedding of the local identity operator $I_A$ is the global identity $I_{\mathcal{H}}$. -/
lemma cylinderOp_one {D L : ℕ}
    (Site : BoxD D L → Type) [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    (A : Finset (BoxD D L)) :
    cylinderOp Site A (1 : LocalHilbertSpace Site A →L[ℂ] LocalHilbertSpace Site A) = 1 := by
  ext ψ σ
  change ψ.ofLp (spliceConfig A (restrictConfig A σ) σ) = ψ.ofLp σ
  rw [spliceConfig_restrictConfig]

/-- The cylinder embedding preserves operator addition on $\mathcal{B}(\mathcal{H}_A)$. -/
lemma cylinderOp_add {D L : ℕ}
    (Site : BoxD D L → Type) [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    (A : Finset (BoxD D L))
    (O₁ O₂ : LocalHilbertSpace Site A →L[ℂ] LocalHilbertSpace Site A) :
    cylinderOp Site A (O₁ + O₂) = cylinderOp Site A O₁ + cylinderOp Site A O₂ := by
  ext ψ σ
  rfl

/-- The cylinder embedding preserves operator subtraction on $\mathcal{B}(\mathcal{H}_A)$. -/
lemma cylinderOp_sub {D L : ℕ}
    (Site : BoxD D L → Type) [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    (A : Finset (BoxD D L))
    (O₁ O₂ : LocalHilbertSpace Site A →L[ℂ] LocalHilbertSpace Site A) :
    cylinderOp Site A (O₁ - O₂) = cylinderOp Site A O₁ - cylinderOp Site A O₂ := by
  ext ψ σ
  rfl

/-- The cylinder embedding preserves complex scalar multiplication on $\mathcal{B}(\mathcal{H}_A)$. -/
lemma cylinderOp_smul {D L : ℕ}
    (Site : BoxD D L → Type) [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    (A : Finset (BoxD D L))
    (c : ℂ) (O : LocalHilbertSpace Site A →L[ℂ] LocalHilbertSpace Site A) :
    cylinderOp Site A (c • O) = c • cylinderOp Site A O := by
  ext ψ σ
  rfl

/-- The cylinder embedding preserves operator multiplication on $\mathcal{B}(\mathcal{H}_A)$. -/
lemma cylinderOp_mul {D L : ℕ} {Site : BoxD D L → Type}
    [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    (A : Finset (BoxD D L))
    (O₁ O₂ : LocalHilbertSpace Site A →L[ℂ] LocalHilbertSpace Site A) :
    cylinderOp Site A O₁ * cylinderOp Site A O₂ = cylinderOp Site A (O₁ * O₂) := by
  ext ψ σ
  change (O₁ (WithLp.toLp 2 (fun α : LocalConfig Site A =>
      (O₂ (WithLp.toLp 2 (fun β : LocalConfig Site A =>
        ψ.ofLp (spliceConfig A β (spliceConfig A α σ))))).ofLp
          (restrictConfig A (spliceConfig A α σ))))).ofLp (restrictConfig A σ) =
    (O₁ (O₂ (WithLp.toLp 2 (fun β : LocalConfig Site A =>
      ψ.ofLp (spliceConfig A β σ))))).ofLp (restrictConfig A σ)
  have h_inner :
      WithLp.toLp 2 (fun α : LocalConfig Site A =>
        (O₂ (WithLp.toLp 2 (fun β : LocalConfig Site A =>
          ψ.ofLp (spliceConfig A β (spliceConfig A α σ))))).ofLp
            (restrictConfig A (spliceConfig A α σ))) =
      O₂ (WithLp.toLp 2 (fun β : LocalConfig Site A =>
        ψ.ofLp (spliceConfig A β σ))) := by
    ext α
    change (O₂ (WithLp.toLp 2 (fun β : LocalConfig Site A =>
        ψ.ofLp (spliceConfig A β (spliceConfig A α σ))))).ofLp
          (restrictConfig A (spliceConfig A α σ)) =
      (O₂ (WithLp.toLp 2 (fun β : LocalConfig Site A =>
        ψ.ofLp (spliceConfig A β σ)))).ofLp α
    rw [restrictConfig_spliceConfig]
    refine congrArg (fun v => (O₂ v).ofLp α) ?_
    ext β
    change ψ.ofLp (spliceConfig A β (spliceConfig A α σ)) = ψ.ofLp (spliceConfig A β σ)
    rw [spliceConfig_idem]
  rw [h_inner]

/-- Canonical bijection between product configurations on $A \times (\Lambda_L \setminus A)$ and global configurations. -/
def configEquiv {D L : ℕ} {Site : BoxD D L → Type}
    (A : Finset (BoxD D L)) :
    LocalConfig Site A × LocalConfig Site (Finset.univ \ A) ≃ ManyBodyConfig Site where
  toFun p := combineConfig A p.1 p.2
  invFun σ := (restrictConfig A σ, restrictConfig (Finset.univ \ A) σ)
  left_inv := by
    rintro ⟨α, γ⟩
    ext ⟨x, hx⟩
    · simp [combineConfig, restrictConfig, hx]
    · have hxA : x ∉ A := (Finset.mem_sdiff.mp hx).2
      simp [combineConfig, restrictConfig, hxA]
  right_inv := by
    intro σ
    ext x
    by_cases hx : x ∈ A <;> simp [combineConfig, restrictConfig, hx]

lemma restrictConfig_combineConfig {D L : ℕ} {Site : BoxD D L → Type}
    (A : Finset (BoxD D L))
    (α : LocalConfig Site A) (γ : LocalConfig Site (Finset.univ \ A)) :
    restrictConfig A (combineConfig A α γ) = α :=
  congrArg Prod.fst ((configEquiv A).left_inv (α, γ))

lemma restrictConfig_compl_combineConfig {D L : ℕ} {Site : BoxD D L → Type}
    (A : Finset (BoxD D L))
    (α : LocalConfig Site A) (γ : LocalConfig Site (Finset.univ \ A)) :
    restrictConfig (Finset.univ \ A) (combineConfig A α γ) = γ :=
  congrArg Prod.snd ((configEquiv A).left_inv (α, γ))

lemma spliceConfig_combineConfig {D L : ℕ} {Site : BoxD D L → Type}
    (A : Finset (BoxD D L))
    (α β : LocalConfig Site A) (γ : LocalConfig Site (Finset.univ \ A)) :
    spliceConfig A β (combineConfig A α γ) = combineConfig A β γ := by
  ext x
  by_cases hx : x ∈ A <;> simp [spliceConfig, combineConfig, hx]

lemma spliceConfig_compl_combineConfig {D L : ℕ} {Site : BoxD D L → Type}
    (A : Finset (BoxD D L))
    (α : LocalConfig Site A) (γ γ' : LocalConfig Site (Finset.univ \ A)) :
    spliceConfig (Finset.univ \ A) γ' (combineConfig A α γ) = combineConfig A α γ' := by
  ext x
  by_cases hx : x ∈ A
  · have hxB : x ∉ Finset.univ \ A := fun h => (Finset.mem_sdiff.mp h).2 hx
    simp [spliceConfig, combineConfig, hx, hxB]
  · have hxB : x ∈ Finset.univ \ A := Finset.mem_sdiff.mpr ⟨Finset.mem_univ x, hx⟩
    simp [spliceConfig, combineConfig, hx, hxB]

/-- Fiber slice of a global state $\psi \in \mathcal{H}$ along a fixed complement configuration $\gamma$. -/
def sliceLp {D L : ℕ} {Site : BoxD D L → Type}
    [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    (A : Finset (BoxD D L)) (γ : LocalConfig Site (Finset.univ \ A))
    (ψ : ManyBodyHilbertSpace Site) : LocalHilbertSpace Site A :=
  WithLp.toLp 2 (fun β : LocalConfig Site A => ψ.ofLp (combineConfig A β γ))

lemma cylinderOp_apply_combineConfig {D L : ℕ} {Site : BoxD D L → Type}
    [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    (A : Finset (BoxD D L))
    (O_A : LocalHilbertSpace Site A →L[ℂ] LocalHilbertSpace Site A)
    (ψ : ManyBodyHilbertSpace Site)
    (α : LocalConfig Site A) (γ : LocalConfig Site (Finset.univ \ A)) :
    (cylinderOp Site A O_A ψ).ofLp (combineConfig A α γ) =
      (O_A (sliceLp A γ ψ)).ofLp α := by
  change (O_A (WithLp.toLp 2 (fun β : LocalConfig Site A =>
      ψ.ofLp (spliceConfig A β (combineConfig A α γ))))).ofLp
        (restrictConfig A (combineConfig A α γ)) =
    (O_A (sliceLp A γ ψ)).ofLp α
  rw [restrictConfig_combineConfig]
  refine congrArg (fun v => (O_A v).ofLp α) ?_
  ext β
  change ψ.ofLp (spliceConfig A β (combineConfig A α γ)) = ψ.ofLp (combineConfig A β γ)
  rw [spliceConfig_combineConfig]

lemma inner_manyBody_eq_sum_slices {D L : ℕ} {Site : BoxD D L → Type}
    [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    (A : Finset (BoxD D L))
    (φ ψ : ManyBodyHilbertSpace Site) :
    inner ℂ φ ψ = ∑ γ : LocalConfig Site (Finset.univ \ A), inner ℂ (sliceLp A γ φ) (sliceLp A γ ψ) := by
  rw [PiLp.inner_apply]
  rw [← (configEquiv (Site := Site) A).sum_comp]
  rw [Fintype.sum_prod_type, Finset.sum_comm]
  congr 1

/-- The cylinder embedding commutes with the Hilbert-space adjoint: $(O_A \otimes I_{A^c})^\dagger = O_A^\dagger \otimes I_{A^c}$. -/
lemma cylinderOp_adjoint {D L : ℕ} {Site : BoxD D L → Type}
    [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    (A : Finset (BoxD D L))
    (O_A : LocalHilbertSpace Site A →L[ℂ] LocalHilbertSpace Site A) :
    (cylinderOp Site A O_A)† = cylinderOp Site A (O_A†) := by
  ext φ : 1
  apply ext_inner_right ℂ
  intro ψ
  rw [ContinuousLinearMap.adjoint_inner_left,
    inner_manyBody_eq_sum_slices A φ (cylinderOp Site A O_A ψ),
    inner_manyBody_eq_sum_slices A (cylinderOp Site A (O_A†) φ) ψ]
  congr 1
  ext γ
  have h1 : sliceLp A γ (cylinderOp Site A O_A ψ) = O_A (sliceLp A γ ψ) := by
    ext α
    exact cylinderOp_apply_combineConfig A O_A ψ α γ
  have h2 : sliceLp A γ (cylinderOp Site A (O_A†) φ) = (O_A†) (sliceLp A γ φ) := by
    ext α
    exact cylinderOp_apply_combineConfig A (O_A†) φ α γ
  rw [h1, h2, ← ContinuousLinearMap.adjoint_inner_left]

/-!
## 2. Subsystem Support Monotonicity and Closure Under Algebraic Operations
-/

def restrictLocal {D L : ℕ} {Site : BoxD D L → Type}
    {A B : Finset (BoxD D L)} (hAB : A ⊆ B) (β : LocalConfig Site B) :
    LocalConfig Site A :=
  fun x => β ⟨x.1, hAB x.2⟩

def spliceLocal {D L : ℕ} {Site : BoxD D L → Type}
    (A B : Finset (BoxD D L)) (α : LocalConfig Site A) (β : LocalConfig Site B) :
    LocalConfig Site B :=
  fun x => if hx : x.1 ∈ A then α ⟨x.1, hx⟩ else β x

def liftLocalOp {D L : ℕ} {Site : BoxD D L → Type}
    [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    {A B : Finset (BoxD D L)} (hAB : A ⊆ B)
    (O_A : LocalHilbertSpace Site A →L[ℂ] LocalHilbertSpace Site A) :
    LocalHilbertSpace Site B →L[ℂ] LocalHilbertSpace Site B :=
  LinearMap.toContinuousLinearMap
    { toFun := fun ψ_B =>
        WithLp.toLp 2 (fun β : LocalConfig Site B =>
          (O_A (WithLp.toLp 2 (fun α : LocalConfig Site A =>
            ψ_B.ofLp (spliceLocal A B α β)))).ofLp (restrictLocal hAB β))
      map_add' := fun ψ₁ ψ₂ => by
        ext β
        change (O_A (WithLp.toLp 2 (fun α => (ψ₁ + ψ₂).ofLp (spliceLocal A B α β)))).ofLp (restrictLocal hAB β) =
          (O_A (WithLp.toLp 2 (fun α => ψ₁.ofLp (spliceLocal A B α β)))).ofLp (restrictLocal hAB β) +
          (O_A (WithLp.toLp 2 (fun α => ψ₂.ofLp (spliceLocal A B α β)))).ofLp (restrictLocal hAB β)
        have h_add : WithLp.toLp 2 (fun α : LocalConfig Site A => (ψ₁ + ψ₂).ofLp (spliceLocal A B α β)) =
            WithLp.toLp 2 (fun α : LocalConfig Site A => ψ₁.ofLp (spliceLocal A B α β)) +
            WithLp.toLp 2 (fun α : LocalConfig Site A => ψ₂.ofLp (spliceLocal A B α β)) := rfl
        rw [h_add, map_add]
        rfl
      map_smul' := fun c ψ => by
        ext β
        change (O_A (WithLp.toLp 2 (fun α => (c • ψ).ofLp (spliceLocal A B α β)))).ofLp (restrictLocal hAB β) =
          c • (O_A (WithLp.toLp 2 (fun α => ψ.ofLp (spliceLocal A B α β)))).ofLp (restrictLocal hAB β)
        have h_smul : WithLp.toLp 2 (fun α : LocalConfig Site A => (c • ψ).ofLp (spliceLocal A B α β)) =
            c • WithLp.toLp 2 (fun α : LocalConfig Site A => ψ.ofLp (spliceLocal A B α β)) := rfl
        rw [h_smul, map_smul]
        rfl }

lemma cylinderOp_liftLocalOp {D L : ℕ} {Site : BoxD D L → Type}
    [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    {A B : Finset (BoxD D L)} (hAB : A ⊆ B)
    (O_A : LocalHilbertSpace Site A →L[ℂ] LocalHilbertSpace Site A) :
    cylinderOp Site B (liftLocalOp hAB O_A) = cylinderOp Site A O_A := by
  ext ψ σ
  change (O_A (WithLp.toLp 2 (fun α : LocalConfig Site A =>
      ψ.ofLp (spliceConfig B (spliceLocal A B α (restrictConfig B σ)) σ)))).ofLp
        (restrictLocal hAB (restrictConfig B σ)) =
    (O_A (WithLp.toLp 2 (fun α : LocalConfig Site A =>
      ψ.ofLp (spliceConfig A α σ)))).ofLp (restrictConfig A σ)
  have h_rest : restrictLocal hAB (restrictConfig B σ) = restrictConfig A σ := rfl
  rw [h_rest]
  refine congrArg (fun v => (O_A v).ofLp (restrictConfig A σ)) ?_
  ext α
  change ψ.ofLp (spliceConfig B (spliceLocal A B α (restrictConfig B σ)) σ) =
    ψ.ofLp (spliceConfig A α σ)
  refine congrArg ψ.ofLp ?_
  ext x
  by_cases hxA : x ∈ A
  · have hxB : x ∈ B := hAB hxA
    simp [spliceConfig, spliceLocal, hxA, hxB]
  · by_cases hxB : x ∈ B <;> simp [spliceConfig, spliceLocal, restrictConfig, hxA, hxB]

/-- Monotonicity of operator support: if $O$ is supported on $A$ and $A \subseteq B$, then $O$ is supported on $B$. -/
lemma isSupportedOn_mono {D L : ℕ} {Site : BoxD D L → Type}
    [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    {A B : Finset (BoxD D L)} (hAB : A ⊆ B)
    {O : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site}
    (hO : IsSupportedOn Site A O) :
    IsSupportedOn Site B O := by
  rcases hO with ⟨O_A, rfl⟩
  exact ⟨liftLocalOp hAB O_A, (cylinderOp_liftLocalOp hAB O_A).symm⟩

/-- The global identity operator $1$ is supported on any region $B \subseteq \mathrm{BoxD}\ D\ L$. -/
lemma isSupportedOn_one {D L : ℕ} {Site : BoxD D L → Type}
    [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    (B : Finset (BoxD D L)) :
    IsSupportedOn Site B 1 :=
  ⟨1, (cylinderOp_one Site B).symm⟩

/-- The zero operator $0$ is supported on any region $B \subseteq \mathrm{BoxD}\ D\ L$. -/
lemma isSupportedOn_zero {D L : ℕ} {Site : BoxD D L → Type}
    [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    (B : Finset (BoxD D L)) :
    IsSupportedOn Site B 0 := by
  refine ⟨0, ?_⟩
  ext ψ σ
  rfl

/-- Operators supported on $B$ are closed under addition. -/
lemma isSupportedOn_add {D L : ℕ} {Site : BoxD D L → Type}
    [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    (B : Finset (BoxD D L))
    {O₁ O₂ : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site}
    (h₁ : IsSupportedOn Site B O₁) (h₂ : IsSupportedOn Site B O₂) :
    IsSupportedOn Site B (O₁ + O₂) := by
  rcases h₁ with ⟨L₁, rfl⟩
  rcases h₂ with ⟨L₂, rfl⟩
  exact ⟨L₁ + L₂, (cylinderOp_add Site B L₁ L₂).symm⟩

/-- Operators supported on $B$ are closed under subtraction. -/
lemma isSupportedOn_sub {D L : ℕ} {Site : BoxD D L → Type}
    [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    (B : Finset (BoxD D L))
    {O₁ O₂ : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site}
    (h₁ : IsSupportedOn Site B O₁) (h₂ : IsSupportedOn Site B O₂) :
    IsSupportedOn Site B (O₁ - O₂) := by
  rcases h₁ with ⟨L₁, rfl⟩
  rcases h₂ with ⟨L₂, rfl⟩
  exact ⟨L₁ - L₂, (cylinderOp_sub Site B L₁ L₂).symm⟩

/-- Operators supported on $B$ are closed under scalar multiplication. -/
lemma isSupportedOn_smul {D L : ℕ} {Site : BoxD D L → Type}
    [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    (B : Finset (BoxD D L)) (c : ℂ)
    {O : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site}
    (hO : IsSupportedOn Site B O) :
    IsSupportedOn Site B (c • O) := by
  rcases hO with ⟨L_B, rfl⟩
  exact ⟨c • L_B, (cylinderOp_smul Site B c L_B).symm⟩

/-- Subtracting a scalar multiple of the identity preserves local support on $A$. -/
lemma isSupportedOn_sub_smul_one {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    {A : Finset (BoxD D L)}
    {O : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site}
    (hO : IsSupportedOn Site A O) (c : ℂ) :
    IsSupportedOn Site A (O - c • 1) :=
  isSupportedOn_sub A hO (isSupportedOn_smul A c (isSupportedOn_one A))

/-- Operators supported on $B$ are closed under multiplication. -/
lemma isSupportedOn_mul {D L : ℕ} {Site : BoxD D L → Type}
    [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    (B : Finset (BoxD D L))
    {O₁ O₂ : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site}
    (h₁ : IsSupportedOn Site B O₁) (h₂ : IsSupportedOn Site B O₂) :
    IsSupportedOn Site B (O₁ * O₂) := by
  rcases h₁ with ⟨L₁, rfl⟩
  rcases h₂ with ⟨L₂, rfl⟩
  exact ⟨L₁ * L₂, cylinderOp_mul B L₁ L₂⟩

/-- Operators supported on $B$ are closed under taking the Hilbert-space adjoint. -/
lemma isSupportedOn_adjoint {D L : ℕ} {Site : BoxD D L → Type}
    [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    (B : Finset (BoxD D L))
    {O : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site}
    (hO : IsSupportedOn Site B O) :
    IsSupportedOn Site B (O†) := by
  rcases hO with ⟨L_B, rfl⟩
  exact ⟨L_B†, cylinderOp_adjoint B L_B⟩

/-- Any list product of operators supported on $B$ is itself supported on $B$. -/
lemma isSupportedOn_list_prod {D L : ℕ} {Site : BoxD D L → Type}
    [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    (B : Finset (BoxD D L))
    (l : List (ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site))
    (hl : ∀ p ∈ l, IsSupportedOn Site B p) :
    IsSupportedOn Site B l.prod := by
  induction l with
  | nil =>
    rw [List.prod_nil]
    exact isSupportedOn_one B
  | cons p tail ih =>
    rw [List.prod_cons]
    exact isSupportedOn_mul B (hl p List.mem_cons_self)
      (ih (fun q hq => hl q (List.mem_cons_of_mem p hq)))

/-- Any finite sum of operators supported on $B$ is itself supported on $B$. -/
lemma isSupportedOn_finset_sum {D L : ℕ} {Site : BoxD D L → Type}
    [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    {α : Type*} (B : Finset (BoxD D L)) (s : Finset α)
    (f : α → (ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site))
    (hf : ∀ a ∈ s, IsSupportedOn Site B (f a)) :
    IsSupportedOn Site B (∑ a ∈ s, f a) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    rw [Finset.sum_empty]
    exact isSupportedOn_zero B
  | @insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact isSupportedOn_add B (hf a (Finset.mem_insert_self a s))
      (ih (fun b hb => hf b (Finset.mem_insert_of_mem hb)))

lemma restrictConfig_spliceConfig_of_disjoint {D L : ℕ} {Site : BoxD D L → Type}
    {X Y : Finset (BoxD D L)} (hXY : Disjoint X Y)
    (α : LocalConfig Site X) (σ : ManyBodyConfig Site) :
    restrictConfig Y (spliceConfig X α σ) = restrictConfig Y σ := by
  ext ⟨y, hyY⟩
  simp only [restrictConfig, spliceConfig]
  have hyX : y ∉ X := Finset.disjoint_right.mp hXY hyY
  rw [dif_neg hyX]

lemma spliceConfig_comm_of_disjoint {D L : ℕ} {Site : BoxD D L → Type}
    {X Y : Finset (BoxD D L)} (hXY : Disjoint X Y)
    (α : LocalConfig Site X) (β : LocalConfig Site Y) (σ : ManyBodyConfig Site) :
    spliceConfig Y β (spliceConfig X α σ) = spliceConfig X α (spliceConfig Y β σ) := by
  ext z
  simp only [spliceConfig]
  by_cases hzY : z ∈ Y
  · have hzX : z ∉ X := Finset.disjoint_right.mp hXY hzY
    rw [dif_pos hzY, dif_neg hzX, dif_pos hzY]
  · rw [dif_neg hzY]
    by_cases hzX : z ∈ X
    · rw [dif_pos hzX, dif_pos hzX]
    · rw [dif_neg hzX, dif_neg hzX, dif_neg hzY]

def deltaLp {ι : Type*} [Fintype ι] [DecidableEq ι] (i : ι) : EuclideanSpace ℂ ι :=
  WithLp.toLp 2 (fun j => if j = i then 1 else 0)

lemma ofLp_sum {α ι : Type*} (s : Finset α) (f : α → EuclideanSpace ℂ ι) (j : ι) :
    (∑ a ∈ s, f a).ofLp j = ∑ a ∈ s, (f a).ofLp j := by
  induction s using Finset.cons_induction with
  | empty => rfl
  | cons a s ha ih =>
    rw [Finset.sum_cons, Finset.sum_cons]
    exact congrArg ((f a).ofLp j + ·) ih

lemma clm_ofLp_smul {ι : Type*} [Fintype ι] [DecidableEq ι]
    (c : ℂ) (T : EuclideanSpace ℂ ι →L[ℂ] EuclideanSpace ℂ ι)
    (ψ : EuclideanSpace ℂ ι) (j : ι) :
    ((c • T) ψ).ofLp j = c * (T ψ).ofLp j :=
  rfl

lemma clm_ofLp_sum {α ι : Type*} [Fintype ι] [DecidableEq ι]
    (s : Finset α) (f : α → (EuclideanSpace ℂ ι →L[ℂ] EuclideanSpace ℂ ι))
    (ψ : EuclideanSpace ℂ ι) (j : ι) :
    ((∑ a ∈ s, f a) ψ).ofLp j = ∑ a ∈ s, (f a ψ).ofLp j := by
  rw [ContinuousLinearMap.sum_apply, ofLp_sum]

lemma euclidean_eq_sum_deltaLp {ι : Type*} [Fintype ι] [DecidableEq ι]
    (v : EuclideanSpace ℂ ι) :
    v = ∑ i : ι, v.ofLp i • deltaLp i := by
  ext j
  rw [ofLp_sum]
  have h_eq : (∑ i : ι, (v.ofLp i • deltaLp i).ofLp j) =
      ∑ i : ι, v.ofLp i * (if j = i then 1 else 0) := rfl
  rw [h_eq]
  simp

lemma clm_apply_ofLp_eq_sum {ι : Type*} [Fintype ι] [DecidableEq ι]
    (O : EuclideanSpace ℂ ι →L[ℂ] EuclideanSpace ℂ ι) (v : EuclideanSpace ℂ ι) (j : ι) :
    (O v).ofLp j = ∑ i : ι, v.ofLp i * (O (deltaLp i)).ofLp j := by
  conv_lhs => rw [euclidean_eq_sum_deltaLp v]
  rw [map_sum, ofLp_sum]
  congr 1
  ext i
  rw [O.map_smul]
  rfl

lemma cylinderOp_comm_of_disjoint {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    {X Y : Finset (BoxD D L)} (hXY : Disjoint X Y)
    (O_X : LocalHilbertSpace Site X →L[ℂ] LocalHilbertSpace Site X)
    (O_Y : LocalHilbertSpace Site Y →L[ℂ] LocalHilbertSpace Site Y) :
    cylinderOp Site X O_X * cylinderOp Site Y O_Y =
      cylinderOp Site Y O_Y * cylinderOp Site X O_X := by
  ext ψ σ
  change (cylinderOp Site X O_X (cylinderOp Site Y O_Y ψ)).ofLp σ =
    (cylinderOp Site Y O_Y (cylinderOp Site X O_X ψ)).ofLp σ
  dsimp [cylinderOp]
  rw [clm_apply_ofLp_eq_sum O_X, clm_apply_ofLp_eq_sum O_Y]
  have hLHS :
      (∑ α : LocalConfig Site X,
        (O_Y (WithLp.toLp 2 (fun β : LocalConfig Site Y =>
          ψ.ofLp (spliceConfig Y β (spliceConfig X α σ))))).ofLp
          (restrictConfig Y (spliceConfig X α σ)) *
        (O_X (deltaLp α)).ofLp (restrictConfig X σ)) =
      ∑ α : LocalConfig Site X, ∑ β : LocalConfig Site Y,
        ψ.ofLp (spliceConfig X α (spliceConfig Y β σ)) *
        (O_Y (deltaLp β)).ofLp (restrictConfig Y σ) *
        (O_X (deltaLp α)).ofLp (restrictConfig X σ) := by
    congr 1
    ext α
    rw [restrictConfig_spliceConfig_of_disjoint hXY, clm_apply_ofLp_eq_sum O_Y, Finset.sum_mul]
    congr 1
    ext β
    change ψ.ofLp (spliceConfig Y β (spliceConfig X α σ)) *
        (O_Y (deltaLp β)).ofLp (restrictConfig Y σ) *
        (O_X (deltaLp α)).ofLp (restrictConfig X σ) = _
    rw [spliceConfig_comm_of_disjoint hXY]
  have hRHS :
      (∑ β : LocalConfig Site Y,
        (O_X (WithLp.toLp 2 (fun α : LocalConfig Site X =>
          ψ.ofLp (spliceConfig X α (spliceConfig Y β σ))))).ofLp
          (restrictConfig X (spliceConfig Y β σ)) *
        (O_Y (deltaLp β)).ofLp (restrictConfig Y σ)) =
      ∑ β : LocalConfig Site Y, ∑ α : LocalConfig Site X,
        ψ.ofLp (spliceConfig X α (spliceConfig Y β σ)) *
        (O_X (deltaLp α)).ofLp (restrictConfig X σ) *
        (O_Y (deltaLp β)).ofLp (restrictConfig Y σ) := by
    congr 1
    ext β
    rw [restrictConfig_spliceConfig_of_disjoint hXY.symm, clm_apply_ofLp_eq_sum O_X, Finset.sum_mul]
  rw [hLHS, hRHS, Finset.sum_comm]
  congr 1
  ext β
  congr 1
  ext α
  ring

/-- Two operators supported on disjoint regions $A, B \subseteq \mathrm{BoxD}\ D\ L$ commute. -/
lemma commute_of_isSupportedOn_disjoint {D L : ℕ} {Site : BoxD D L → Type}
    [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    {A B : Finset (BoxD D L)} (hDisj : Disjoint A B)
    {O₁ O₂ : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site}
    (h₁ : IsSupportedOn Site A O₁) (h₂ : IsSupportedOn Site B O₂) :
    Commute O₁ O₂ := by
  rcases h₁ with ⟨O_A, rfl⟩
  rcases h₂ with ⟨O_B, rfl⟩
  exact cylinderOp_comm_of_disjoint hDisj O_A O_B

/-- The local ground-state projector `sys.P_loc B` of a `CommutingProjectorHamiltonian` is supported on $B$. -/
lemma CommutingProjectorHamiltonian.isSupportedOn_P_loc {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    (sys : CommutingProjectorHamiltonian D L Site) (B : Finset (BoxD D L)) :
    IsSupportedOn Site B (sys.localGroundProj B) := by
  dsimp [CommutingProjectorHamiltonian.localGroundProj, localGroundProjector]
  apply isSupportedOn_list_prod B
  intro p hp
  rcases List.mem_map.mp hp with ⟨K, hK_mem, rfl⟩
  rcases Finset.mem_filter.mp (Finset.mem_toList.mp hK_mem) with ⟨hK_cube, hKB⟩
  exact isSupportedOn_sub B (isSupportedOn_one B)
    (isSupportedOn_mono hKB (sys.is_supported K hK_cube))

/-- The local ground-state projector `sys.P_loc B` of an `IndexedCommutingProjectorHamiltonian` is supported on $B$. -/
lemma IndexedCommutingProjectorHamiltonian.isSupportedOn_P_loc {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (sys : IndexedCommutingProjectorHamiltonian D L Site ι) (B : Finset (BoxD D L)) :
    IsSupportedOn Site B (sys.localGroundProj B) := by
  dsimp [IndexedCommutingProjectorHamiltonian.localGroundProj, IndexedCommutingProjectorHamiltonian.localGroundProj]
  apply isSupportedOn_list_prod B
  intro p hp
  rcases List.mem_map.mp hp with ⟨i, hi_mem, rfl⟩
  have hiB : sys.support i ⊆ B := (Finset.mem_filter.mp (Finset.mem_toList.mp hi_mem)).2
  exact isSupportedOn_sub B (isSupportedOn_one B)
    (isSupportedOn_mono hiB (sys.is_supported i))

end
