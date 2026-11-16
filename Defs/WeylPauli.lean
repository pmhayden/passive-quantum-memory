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

import Defs.BoxLattice
import Defs.ManyBodyHilbert
import Defs.LocalHamiltonian
import Defs.F2ChainAndCSS

/-!
# Symplectic Weyl-Pauli Operators and CSS Stabilizer Check Projectors

Defines the F_2 symplectic phase character (`pauliPhase`), per-site qubit slot configurations (`CodeSlotConfig`, `BoxSlot3D`), and multi-qubit Weyl-Pauli X and Z operators (`weylPauliX`, `weylPauliZ`) on `ManyBodyHilbertSpace`. Constructs elementary CSS check violation projectors (`weylCheckProjX`, `weylCheckProjZ`) and proves fundamental symplectic Weyl commutation (`weylPauliX_mul_weylPauliZ`, `weylPauliX_commute_weylPauliZ_of_ortho`).

## References

* Part I, Section 3.1 (`subsec:rca-trinity`), Proposition 3.3 (`prop:trinity-equivalence`), Section 5.4 (`subsec:safe-decoded-observables`), Definition 5.6 (`def:safe-decoded-observables`)
* Part II, Section 2 (`subsec:setup`), Definition 2.1 (`def:bdl-lattice`)
-/

noncomputable section

open scoped Classical BigOperators InnerProduct ComplexConjugate
open ContinuousLinearMap

/-! ## 1. Symplectic $\mathbb{F}_2$ Phase and Sign Characters -/

/-- $\mathbb{F}_2$-symplectic sign character $(-1)^{\langle a, z \rangle} \in \{+1, -1\} \subset \mathbb{C}$
    for bitstrings $a, z : Q \to \mathrm{ZMod}\ 2$. -/
def pauliPhase {Q : Type*} [Fintype Q] (a z : Q → ZMod 2) : ℂ :=
  if (∑ q : Q, a q * z q) = 0 then 1 else -1

/-- Multiplicativity of the `ZMod 2` sign map $x \mapsto (-1)^x \in \mathbb{C}$. -/
lemma zmod2_sign_add (x y : ZMod 2) :
    (if x + y = 0 then (1 : ℂ) else -1) =
      (if x = 0 then (1 : ℂ) else -1) * (if y = 0 then (1 : ℂ) else -1) := by
  have h10 : (1 : ZMod 2) ≠ 0 := by decide
  have h11 : (1 + 1 : ZMod 2) = 0 := by decide
  rcases zmod2_eq_zero_or_one x with rfl | rfl <;>
    rcases zmod2_eq_zero_or_one y with rfl | rfl <;>
    simp [h10, h11]

/-- Right linearity of `pauliPhase`: $(-1)^{\langle a, z_1 + z_2 \rangle} = (-1)^{\langle a, z_1 \rangle} (-1)^{\langle a, z_2 \rangle}$. -/
lemma pauliPhase_add_right {Q : Type*} [Fintype Q] (a z₁ z₂ : Q → ZMod 2) :
    pauliPhase a (z₁ + z₂) = pauliPhase a z₁ * pauliPhase a z₂ := by
  unfold pauliPhase
  simp only [Pi.add_apply]
  have h_sum : (∑ q : Q, a q * (z₁ q + z₂ q)) =
      (∑ q : Q, a q * z₁ q) + (∑ q : Q, a q * z₂ q) := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun q _ => mul_add (a q) (z₁ q) (z₂ q))
  rw [h_sum]
  exact zmod2_sign_add _ _

/-- Left linearity of `pauliPhase`: $(-1)^{\langle a_1 + a_2, z \rangle} = (-1)^{\langle a_1, z \rangle} (-1)^{\langle a_2, z \rangle}$. -/
lemma pauliPhase_add_left {Q : Type*} [Fintype Q] (a₁ a₂ z : Q → ZMod 2) :
    pauliPhase (a₁ + a₂) z = pauliPhase a₁ z * pauliPhase a₂ z := by
  unfold pauliPhase
  simp only [Pi.add_apply]
  have h_sum : (∑ q : Q, (a₁ q + a₂ q) * z q) =
      (∑ q : Q, a₁ q * z q) + (∑ q : Q, a₂ q * z q) := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun q _ => add_mul (a₁ q) (a₂ q) (z q))
  rw [h_sum]
  exact zmod2_sign_add _ _

/-- Involution property `pauliPhase a z * pauliPhase a z = 1`. -/
lemma pauliPhase_mul_self {Q : Type*} [Fintype Q] (a z : Q → ZMod 2) :
    pauliPhase a z * pauliPhase a z = 1 := by
  rw [← pauliPhase_add_right]
  have h_zero : z + z = 0 := by ext q; exact zmod2_add_self (z q)
  rw [h_zero]
  simp [pauliPhase]

/-- Complex conjugation fixes `pauliPhase a z` since $(-1)^{\langle a, z \rangle} \in \{\pm 1\} \subset \mathbb{R}$. -/
lemma star_pauliPhase {Q : Type*} [Fintype Q] (a z : Q → ZMod 2) :
    star (pauliPhase a z) = pauliPhase a z := by
  dsimp [pauliPhase]
  split_ifs <;> simp

/-! ## 2. Open-Box Qubit Slot Configurations and Multi-Qubit Weyl–Pauli Operators -/

/-- Local $q_{\mathrm{code}}$-qubit slot configuration at a single lattice site $v \in \mathrm{Box3D}\ L$. -/
abbrev CodeSlotConfig (q_code : ℕ) : Type := Fin q_code → Bool

/-- Global slot index `(v, s) ∈ Box3D L × Fin q_code` on the open 3D box `Box3D L`. -/
abbrev BoxSlot3D (L q_code : ℕ) : Type := Box3D L × Fin q_code

/-- Convert a Boolean bit `b : Bool` to `ZMod 2` (`false ↦ 0`, `true ↦ 1`). -/
def boolToZMod2 (b : Bool) : ZMod 2 :=
  if b then 1 else 0

/-- Convert a `ZMod 2` element `x : ZMod 2` to `Bool` (`x ≠ 0`). -/
def zmod2ToBool (x : ZMod 2) : Bool :=
  decide (x ≠ 0)

lemma boolToZMod2_xor (b₁ b₂ : Bool) :
    boolToZMod2 (xor b₁ b₂) = boolToZMod2 b₁ + boolToZMod2 b₂ := by
  cases b₁ <;> cases b₂ <;> decide

/-- Extract the global $\mathbb{F}_2$-bitstring `BoxSlot3D L q_code → ZMod 2` from a many-body
    configuration $\sigma \in \mathrm{ManyBodyConfig}(\mathrm{UniformSite3D}\ L\ (\mathrm{CodeSlotConfig}\ q_{\mathrm{code}}))$. -/
def codeConfigBits {L q_code : ℕ}
    (σ : ManyBodyConfig (UniformSite3D L (CodeSlotConfig q_code))) :
    BoxSlot3D L q_code → ZMod 2 :=
  fun p => boolToZMod2 (σ p.1 p.2)

/-- Bitwise Pauli-$X$ flip of a many-body configuration $\sigma$ by a bitstring $b : \mathrm{BoxSlot3D}\ L\ q_{\mathrm{code}} \to \mathrm{ZMod}\ 2$. -/
def flipCodeConfig {L q_code : ℕ}
    (b : BoxSlot3D L q_code → ZMod 2)
    (σ : ManyBodyConfig (UniformSite3D L (CodeSlotConfig q_code))) :
    ManyBodyConfig (UniformSite3D L (CodeSlotConfig q_code)) :=
  fun v s => xor (σ v s) (zmod2ToBool (b (v, s)))

lemma flipCodeConfig_involutive {L q_code : ℕ} (b : BoxSlot3D L q_code → ZMod 2) :
    Function.Involutive (flipCodeConfig b) := by
  intro σ; ext v s
  dsimp [flipCodeConfig]
  cases σ v s <;> cases zmod2ToBool (b (v, s)) <;> rfl

lemma codeConfigBits_flipCodeConfig {L q_code : ℕ}
    (b : BoxSlot3D L q_code → ZMod 2)
    (σ : ManyBodyConfig (UniformSite3D L (CodeSlotConfig q_code))) :
    codeConfigBits (flipCodeConfig b σ) = codeConfigBits σ + b := by
  ext ⟨v, s⟩
  dsimp [codeConfigBits, flipCodeConfig]
  rw [boolToZMod2_xor]
  congr 1
  rcases zmod2_eq_zero_or_one (b (v, s)) with h | h <;> rw [h] <;> decide

/-- Multi-qubit Pauli-$Z$ operator $Z(a)$ on `ManyBodyHilbertSpace (UniformSite3D L (CodeSlotConfig q_code))`
    for $a : \mathrm{BoxSlot3D}\ L\ q_{\mathrm{code}} \to \mathrm{ZMod}\ 2$. -/
def weylPauliZ {L q_code : ℕ} (a : BoxSlot3D L q_code → ZMod 2) :
    ManyBodyHilbertSpace (UniformSite3D L (CodeSlotConfig q_code)) →L[ℂ]
      ManyBodyHilbertSpace (UniformSite3D L (CodeSlotConfig q_code)) :=
  LinearMap.toContinuousLinearMap
    { toFun := fun ψ => WithLp.toLp 2 (fun σ =>
        pauliPhase a (codeConfigBits σ) * ψ.ofLp σ)
      map_add' := fun ψ₁ ψ₂ => by
        ext σ
        change pauliPhase a (codeConfigBits σ) * (ψ₁.ofLp σ + ψ₂.ofLp σ) =
          pauliPhase a (codeConfigBits σ) * ψ₁.ofLp σ +
          pauliPhase a (codeConfigBits σ) * ψ₂.ofLp σ
        ring
      map_smul' := fun c ψ => by
        ext σ
        change pauliPhase a (codeConfigBits σ) * (c * ψ.ofLp σ) =
          c * (pauliPhase a (codeConfigBits σ) * ψ.ofLp σ)
        ring }

/-- Multi-qubit Pauli-$X$ operator $X(b)$ on `ManyBodyHilbertSpace (UniformSite3D L (CodeSlotConfig q_code))`
    for $b : \mathrm{BoxSlot3D}\ L\ q_{\mathrm{code}} \to \mathrm{ZMod}\ 2$. -/
def weylPauliX {L q_code : ℕ} (b : BoxSlot3D L q_code → ZMod 2) :
    ManyBodyHilbertSpace (UniformSite3D L (CodeSlotConfig q_code)) →L[ℂ]
      ManyBodyHilbertSpace (UniformSite3D L (CodeSlotConfig q_code)) :=
  LinearMap.toContinuousLinearMap
    { toFun := fun ψ => WithLp.toLp 2 (fun σ =>
        ψ.ofLp (flipCodeConfig b σ))
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }

/-- Elementary Pauli-$Z$ check violation projector $\Pi^Z(a) := \frac{1}{2}(I - Z(a))$. -/
def weylCheckProjZ {L q_code : ℕ} (a : BoxSlot3D L q_code → ZMod 2) :
    ManyBodyHilbertSpace (UniformSite3D L (CodeSlotConfig q_code)) →L[ℂ]
      ManyBodyHilbertSpace (UniformSite3D L (CodeSlotConfig q_code)) :=
  (2 : ℂ)⁻¹ • (1 - weylPauliZ a)

/-- Elementary Pauli-$X$ check violation projector $\Pi^X(b) := \frac{1}{2}(I - X(b))$. -/
def weylCheckProjX {L q_code : ℕ} (b : BoxSlot3D L q_code → ZMod 2) :
    ManyBodyHilbertSpace (UniformSite3D L (CodeSlotConfig q_code)) →L[ℂ]
      ManyBodyHilbertSpace (UniformSite3D L (CodeSlotConfig q_code)) :=
  (2 : ℂ)⁻¹ • (1 - weylPauliX b)

/-- Fundamental Weyl–Pauli commutation relation $X(b) Z(a) = (-1)^{\langle a, b \rangle} Z(a) X(b)$. -/
theorem weylPauliX_mul_weylPauliZ {L q_code : ℕ}
    (a b : BoxSlot3D L q_code → ZMod 2) :
    weylPauliX b * weylPauliZ a = pauliPhase a b • (weylPauliZ a * weylPauliX b) := by
  ext ψ σ
  change pauliPhase a (codeConfigBits (flipCodeConfig b σ)) * ψ.ofLp (flipCodeConfig b σ) =
    pauliPhase a b * (pauliPhase a (codeConfigBits σ) * ψ.ofLp (flipCodeConfig b σ))
  rw [codeConfigBits_flipCodeConfig, pauliPhase_add_right]
  ring

/-- Two Pauli operators $X(b)$ and $Z(a)$ commute whenever $\langle a, b \rangle = 0 \pmod 2$. -/
theorem weylPauliX_commute_weylPauliZ_of_ortho {L q_code : ℕ}
    (a b : BoxSlot3D L q_code → ZMod 2)
    (h_ortho : (∑ p : BoxSlot3D L q_code, a p * b p) = 0) :
    Commute (weylPauliX b) (weylPauliZ a) := by
  rw [commute_iff_eq, weylPauliX_mul_weylPauliZ]
  have h_phase : pauliPhase a b = 1 := by simp [pauliPhase, h_ortho]
  rw [h_phase, one_smul]
