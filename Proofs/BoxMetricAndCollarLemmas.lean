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
import Defs.LocalHamiltonian

/-!
# Open-Box Metric, Ball Inclusions, Collar Geometry, and Chromatic Subgrids

Establishes metric axioms for the open-box l_infty distance boxDist on BoxD D L, monotonicity and triangle-inequality collar growth of boxBall and boxThickening, concentric enclosing-cube inclusion boxCube_subset_enclosingBoxCube, unit-collar shift inclusion isOneCollarOf_boxCube_shiftDownOne, and pairwise cube disjointness disjoint_boxCube_of_mem_chromaticSubgrid on strided chromatic subgrids.

## References

* Part I, Section 3.1 (`subsec:rca-trinity`), Definition 3.2 (`def:tqo`)
* Part I, Section 6.1 (`subsec:dsuper-banach`), Definition 6.1 (`def:banach-quasilocal`)
* Part I, Section 7.1 (`subsec:single-cube-telescoping`), Proposition 7.2 (`prop:single-cube-telescoping`)
* Part II, Section 2 (`subsec:setup`), Definition 2.1 (`def:bdl-lattice`)
-/

noncomputable section

open scoped Classical BigOperators

/-!
## 1. $\ell_\infty$ Metric Balls and Thickening Monotonicity on `BoxD D L`
-/

lemma boxDist_self {D L : ℕ} (x : BoxD D L) : boxDist x x = 0 := by
  apply Nat.eq_zero_of_le_zero
  dsimp [boxDist]
  refine Finset.sup_le fun i _ => ?_
  rw [coordDist_self]

lemma boxDist_comm {D L : ℕ} (x y : BoxD D L) : boxDist x y = boxDist y x := by
  dsimp [boxDist]
  congr 1
  ext i
  exact coordDist_comm (x i) (y i)

lemma boxDist_triangle {D L : ℕ} (x y z : BoxD D L) :
    boxDist x z ≤ boxDist x y + boxDist y z := by
  dsimp [boxDist]
  refine Finset.sup_le fun i hi => ?_
  have h1 : coordDist (x i) (y i) ≤ Finset.univ.sup (fun j => coordDist (x j) (y j)) :=
    Finset.le_sup (f := fun j => coordDist (x j) (y j)) hi
  have h2 : coordDist (y i) (z i) ≤ Finset.univ.sup (fun j => coordDist (y j) (z j)) :=
    Finset.le_sup (f := fun j => coordDist (y j) (z j)) hi
  have h_tri := coordDist_triangle (x i) (y i) (z i)
  omega

lemma boxDist_eq_zero_iff {D L : ℕ} (x y : BoxD D L) :
    boxDist x y = 0 ↔ x = y := by
  constructor
  · intro h
    funext i
    have hi : coordDist (x i) (y i) ≤ boxDist x y :=
      Finset.le_sup (f := fun j => coordDist (x j) (y j)) (Finset.mem_univ i)
    rw [h] at hi
    dsimp [coordDist] at hi
    ext
    omega
  · rintro rfl
    exact boxDist_self x

/-- Every site $x \in \mathrm{BoxD}\ D\ L$ belongs to its own $\ell_\infty$ ball of any radius $r$. -/
lemma mem_boxBall_self {D L : ℕ} (x : BoxD D L) (r : ℕ) :
    x ∈ boxBall x r := by
  simp [boxBall, boxDist_self]

/-- Membership in `boxBall x r` is symmetric in the center and target site. -/
lemma mem_boxBall_comm {D L : ℕ} (x y : BoxD D L) (r : ℕ) :
    y ∈ boxBall x r ↔ x ∈ boxBall y r := by
  simp only [boxBall, Finset.mem_filter, Finset.mem_univ, true_and, boxDist_comm]

/-- Monotonicity of `boxBall x r` in the radius $r_1 \le r_2$. -/
lemma boxBall_mono {D L : ℕ} (x : BoxD D L) {r₁ r₂ : ℕ} (hr : r₁ ≤ r₂) :
    boxBall x r₁ ⊆ boxBall x r₂ := by
  intro y hy
  simp only [boxBall, Finset.mem_filter, Finset.mem_univ, true_and] at hy ⊢
  omega

/-- Point-to-set $\ell_\infty$ distance `boxRegionDist y A = regionDist {y} A` on `BoxD D L`. -/
def boxRegionDist {D L : ℕ} (y : BoxD D L) (A : Finset (BoxD D L)) : ℕ :=
  regionDist {y} A

/-!
## 2. Open-Box Cube Collar Inclusion and Concentric Enclosing Cubes
-/

/-- Coordinate-wise shift down by $1$ (clamped at $0$) on the open box `BoxD D L`:
    `(shiftDownOneBox x0 i).val = (x0 i).val - 1`. -/
def shiftDownOneBox {D L : ℕ} (x0 : BoxD D L) : BoxD D L :=
  fun i => ⟨(x0 i).val - 1, Nat.sub_lt_of_lt (x0 i).isLt⟩

/-- Every open-box cube `boxCube y0 r` is contained in its concentric enclosing cube
    `enclosingBoxCube y0 r R` whenever $r \le R$. -/
lemma boxCube_subset_enclosingBoxCube {D L : ℕ}
    (y0 : BoxD D L) {r R : ℕ} (hrR : r ≤ R) :
    boxCube y0 r ⊆ enclosingBoxCube y0 r R := by
  intro x hx
  simp only [boxCube, enclosingBoxCube, Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
  intro i
  have hxi := hx i
  omega

/-- The shifted cube `boxCube (shiftDownOneBox x0) (ℓ + 2)` is a $1$-collar of `boxCube x0 ℓ`
    on the open box `BoxD D L`. -/
lemma isOneCollarOf_boxCube_shiftDownOne {D L : ℕ}
    (x0 : BoxD D L) (ℓ : ℕ) :
    IsOneCollarOf (boxCube x0 ℓ) (boxCube (shiftDownOneBox x0) (ℓ + 2)) := by
  constructor
  · intro x hx
    simp only [boxCube, Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
    dsimp [shiftDownOneBox]
    intro i
    have hxi := hx i
    omega
  · intro K hK h_not_disj
    simp only [boxCubes, Finset.mem_image, Finset.mem_univ, true_and] at hK
    rcases hK with ⟨y0, rfl⟩
    rw [Finset.not_disjoint_iff] at h_not_disj
    rcases h_not_disj with ⟨z, hzK, hzx0⟩
    intro w hwK
    simp only [boxCube, Finset.mem_filter, Finset.mem_univ, true_and] at hzK hzx0 hwK ⊢
    dsimp [shiftDownOneBox]
    intro i
    have hzi1 := hzK i
    have hzi2 := hzx0 i
    have hwi := hwK i
    omega

/-!
## 3. Chromatic Subgrid Partition on `BoxD D L`
-/

/-- The $s$-strided chromatic subgrid class on `BoxD D L` associated with color offset
    $c : \mathrm{Fin}\ D \to \mathbb{N}$: sites $u \in \mathrm{BoxD}\ D\ L$ satisfying
    $(u_i : \mathbb{N}) \equiv c_i \pmod{s}$ for all $i \in \mathrm{Fin}\ D$. -/
def chromaticSubgrid {D L : ℕ} (s : ℕ) (c : Fin D → ℕ) : Finset (BoxD D L) :=
  Finset.univ.filter (fun u : BoxD D L => ∀ i : Fin D, (u i).val % s = c i % s)

private lemma nat_add_le_of_mod_eq_of_lt {a b s : ℕ} (hmod : a % s = b % s) (hab : a < b) :
    a + s ≤ b := by
  have ha := (Nat.div_add_mod a s).symm
  have hb := (Nat.div_add_mod b s).symm
  have hdiv : a / s < b / s := by
    by_contra h_not
    have h_le : b / s ≤ a / s := Nat.le_of_not_lt h_not
    have h_mul : s * (b / s) ≤ s * (a / s) := Nat.mul_le_mul_left s h_le
    omega
  have h_mul : s * (a / s + 1) ≤ s * (b / s) := Nat.mul_le_mul_left s hdiv
  have h_expand : s * (a / s + 1) = s * (a / s) + s := by ring
  omega

/-- Distinct sites $u \neq v$ in the same $s$-strided chromatic subgrid are separated by
    at least $s$ in $\ell_\infty$ distance `boxDist`. -/
lemma le_boxDist_of_mem_chromaticSubgrid {D L : ℕ} {s : ℕ} (hs : 0 < s)
    {c : Fin D → ℕ} {u v : BoxD D L}
    (hu : u ∈ chromaticSubgrid s c) (hv : v ∈ chromaticSubgrid s c) (huv : u ≠ v) :
    s ≤ boxDist u v := by
  have _ := hs
  rcases Function.ne_iff.mp huv with ⟨i, hi_ne⟩
  simp only [chromaticSubgrid, Finset.mem_filter, Finset.mem_univ, true_and] at hu hv
  have hmod : (u i).val % s = (v i).val % s := (hu i).trans (hv i).symm
  have hval_ne : (u i).val ≠ (v i).val := fun h => hi_ne (Fin.ext h)
  have h_coord : s ≤ coordDist (u i) (v i) := by
    rcases lt_or_gt_of_ne hval_ne with hlt | hgt
    · have hle := nat_add_le_of_mod_eq_of_lt hmod hlt
      dsimp [coordDist]
      omega
    · have hle := nat_add_le_of_mod_eq_of_lt hmod.symm hgt
      dsimp [coordDist]
      omega
  exact le_trans h_coord (Finset.le_sup (f := fun j => coordDist (u j) (v j)) (Finset.mem_univ i))

/-- Cubes `boxCube u r` and `boxCube v r` anchored at distinct sites $u \neq v$ in the same
    $s$-strided chromatic subgrid are disjoint whenever $r \le s$. -/
lemma disjoint_boxCube_of_mem_chromaticSubgrid {D L : ℕ} {s r : ℕ} (hrs : r ≤ s) (hr : 0 < r)
    {c : Fin D → ℕ} {u v : BoxD D L}
    (hu : u ∈ chromaticSubgrid s c) (hv : v ∈ chromaticSubgrid s c) (huv : u ≠ v) :
    Disjoint (boxCube u r) (boxCube v r) := by
  rw [Finset.disjoint_left]
  intro w hwu hwv
  have hs : 0 < s := lt_of_lt_of_le hr hrs
  have hdist : s ≤ boxDist u v := le_boxDist_of_mem_chromaticSubgrid hs hu hv huv
  have hle : boxDist u v ≤ r - 1 := by
    dsimp [boxDist]
    refine Finset.sup_le fun i _ => ?_
    simp only [boxCube, Finset.mem_filter, Finset.mem_univ, true_and] at hwu hwv
    have hu_i := hwu i
    have hv_i := hwv i
    dsimp [coordDist]
    omega
  omega
