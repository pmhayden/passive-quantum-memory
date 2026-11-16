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

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Tactic

/-!
# Strong Deformation Retractions, DAG Sector Grading, and Nilpotent HPL Transfer Series

Defines truncated Neumann series (`neumannTwo`, `neumannFour`), the three-tier directed acyclic sector grading (`sectorGrade`, `PreservesSectorGradeAndVanishesOnZ`, `StrictlyIncreasesSectorGrade`), and abstract strong deformation retractions (`StrongDeformationRetraction`). Constructs the explicit four-step nilpotent homological perturbation transfer, homotopy, projection, and inclusion operators (`hplSigmaFour`, `hplHFour`, `hplPFour`, `hplIFour`).

## References

* Part I, Section 3.2 (`subsec:nilpotent-hpl`), Lemma 3.5 (`lem:general-hpl`), Lemma 3.6 (`lem:block-sdr`), Proposition 3.7 (`prop:classical-hpl`)
* Part II, Section 4 (`subsec:welded-hierarchy-cleaner`), Proposition 4.3 (`prop:rca-hierarchy`)
-/

noncomputable section

open scoped Classical BigOperators

/-! ## 1. Truncated Neumann Series for Nilpotent Perturbations -/

/-- The 2-term truncated Neumann series $1 - x$ in any ring $R$. -/
def neumannTwo {R : Type*} [Ring R] (x : R) : R :=
  1 - x

/-- The 4-term truncated Neumann series $1 - x + x^2 - x^3$ in any ring $R$. -/
def neumannFour {R : Type*} [Ring R] (x : R) : R :=
  1 - x + x ^ 2 - x ^ 3

/-- Polynomial telescoping identity $(1 + x)(1 - x) = 1 - x^2$ in any ring $R$. -/
lemma one_add_mul_neumannTwo {R : Type*} [Ring R] (x : R) :
    (1 + x) * neumannTwo x = 1 - x ^ 2 := by
  dsimp [neumannTwo]; noncomm_ring

/-- Polynomial telescoping identity $(1 - x)(1 + x) = 1 - x^2$ in any ring $R$. -/
lemma neumannTwo_mul_one_add {R : Type*} [Ring R] (x : R) :
    neumannTwo x * (1 + x) = 1 - x ^ 2 := by
  dsimp [neumannTwo]; noncomm_ring

/-- Polynomial telescoping identity $(1 + x)(1 - x + x^2 - x^3) = 1 - x^4$ in any ring $R$. -/
lemma one_add_mul_neumannFour {R : Type*} [Ring R] (x : R) :
    (1 + x) * neumannFour x = 1 - x ^ 4 := by
  dsimp [neumannFour]; noncomm_ring

/-- Polynomial telescoping identity $(1 - x + x^2 - x^3)(1 + x) = 1 - x^4$ in any ring $R$. -/
lemma neumannFour_mul_one_add {R : Type*} [Ring R] (x : R) :
    neumannFour x * (1 + x) = 1 - x ^ 4 := by
  dsimp [neumannFour]; noncomm_ring

/-! ## 2. 3-Tier DAG Sector Grading ($X \to Q \to Z$) -/

/-- The 3-tier sector grading (`Fin 3`) on a 3-layer cylinder or star complex
    $C^X \oplus C^Q \oplus C^Z$ (`α ⊕ β ⊕ γ`):
    - Sector `0` (`X`): $X$-check / top cellular layer,
    - Sector `1` (`Q`): Qubit / middle cellular layer,
    - Sector `2` (`Z`): $Z$-check / bottom cellular layer. -/
def sectorGrade {α β γ : Type*} : α ⊕ β ⊕ γ → Fin 3
  | Sum.inl _ => 0
  | Sum.inr (Sum.inl _) => 1
  | Sum.inr (Sum.inr _) => 2

/-- Sector-grading preservation with vanishing on the terminal $Z$-sector (`grade = 2`):
    models the unperturbed horizontal contracting homotopy $h = h_X \oplus h_Q \oplus 0$. -/
def PreservesSectorGradeAndVanishesOnZ {I : Type*} (grade : I → Fin 3)
    (h : (I → ZMod 2) → (I → ZMod 2)) : Prop :=
  (∀ c : I → ZMod 2, ∀ s : Fin 3,
    (∀ i, c i ≠ 0 → grade i = s) →
    (∀ i, h c i ≠ 0 → grade i = s)) ∧
  (∀ c : I → ZMod 2,
    (∀ i, c i ≠ 0 → grade i = 2) → h c = 0)

/-- Strict sector-grading increase ($0 \mapsto 1$, $1 \mapsto 2$, $2 \mapsto \text{zero}$):
    models the vertical attachment perturbation $g = g_{XQ} + g_{QZ}$ along the DAG $X \to Q \to Z$. -/
def StrictlyIncreasesSectorGrade {I : Type*} (grade : I → Fin 3)
    (g : (I → ZMod 2) → (I → ZMod 2)) : Prop :=
  (∀ c : I → ZMod 2,
    (∀ i, c i ≠ 0 → grade i = 0) →
    (∀ i, g c i ≠ 0 → grade i = 1)) ∧
  (∀ c : I → ZMod 2,
    (∀ i, c i ≠ 0 → grade i = 1) →
    (∀ i, g c i ≠ 0 → grade i = 2)) ∧
  (∀ c : I → ZMod 2,
    (∀ i, c i ≠ 0 → grade i = 2) → g c = 0)

/-! ## 3. Explicit 4-Step Nilpotent HPL Transfer Operators and SDR Data -/

/-- The 4-step HPL transfer operator $\Sigma_4(g, h) = \mathrm{neumannFour}(g h) \cdot g$ in any ring $R$. -/
def hplSigmaFour {R : Type*} [Ring R] (g h : R) : R :=
  neumannFour (g * h) * g

/-- The 4-step HPL deformed contracting homotopy $H_4(g, h) = h \cdot \mathrm{neumannFour}(g h)$. -/
def hplHFour {R : Type*} [Ring R] (g h : R) : R :=
  h * neumannFour (g * h)

/-- The 4-step HPL deformed projection $P_4(g, h, p) = p \cdot (1 - \Sigma_4(g, h) \cdot h)$. -/
def hplPFour {R : Type*} [Ring R] (g h p : R) : R :=
  p * (1 - hplSigmaFour g h * h)

/-- The 4-step HPL deformed inclusion $I_4(g, h, \iota) = (1 - h \cdot \Sigma_4(g, h)) \cdot \iota$. -/
def hplIFour {R : Type*} [Ring R] (g h ι : R) : R :=
  (1 - h * hplSigmaFour g h) * ι

/-- Abstract Strong Deformation Retraction (SDR) data in a noncommutative ring $R$:
    $(\delta, d, \iota, p, h)$ satisfying $\delta^2 = 0$, $d^2 = 0$, $p \iota = 1$,
    $\iota p + d h + h d = 1$, $p d = \delta p$, $d \iota = \iota \delta$, and the side conditions
    $h^2 = 0$, $p h = 0$, $h \iota = 0$. -/
structure StrongDeformationRetraction (R : Type*) [Ring R] where
  δ : R
  d : R
  ι : R
  p : R
  h : R
  h_δ_sq : δ * δ = 0
  h_d_sq : d * d = 0
  h_p_ι : p * ι = 1
  h_homotopy : ι * p + d * h + h * d = 1
  h_p_d : p * d = δ * p
  h_d_ι : d * ι = ι * δ
  h_h_sq : h * h = 0
  h_p_h : p * h = 0
  h_h_ι : h * ι = 0
