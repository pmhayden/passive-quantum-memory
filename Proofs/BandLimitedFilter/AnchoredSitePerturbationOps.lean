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

import Proofs.BandLimitedFilter.BochnerFilterUnitaryCovariance

noncomputable section

open scoped Classical InnerProduct ComplexConjugate BigOperators
open Filter Topology Asymptotics ContinuousLinearMap MeasureTheory

/-!
# Anchored Site Perturbation Operators and Overlap Commutator Factors

Constructs the site-anchored decomposition `anchoredSitePerturbationOp` and `qacSitePerturbationOp` (`qacAnchorOfCube`) regrouping cube-indexed quasi-local perturbations over lattice sites while preserving the total perturbation sum. Defines `siteOverlapCommutatorFactor` and `uniformCubeCommutatorFactor` to obtain linear-in-coupling commutator and unitary conjugation drift bounds under `SatisfiesDecayBound`.

## References

* Part I, Section 6.1 (`subsec:dsuper-banach`), Equations (63)–(64) (`eq:cube-perturbation-decomp`, `eq:site-anchored-decomp`)
* Part I, Section 6.2 (`subsec:bochner-lr`), Equation (72) (`eq:bochner-bare-Q-tail`)
-/

/-!
## 1. Site-Anchored Perturbation Operator & Explicit $O(J)$ Norm Bounds
-/

/-- Canonical anchor vertex of a cube $A \in \mathrm{BoxCubes}\ D\ L\ r$, chosen via `Finset.mem_image`
    so that `boxCube (qacAnchorOfCube r A) r = A` whenever $A \in \mathrm{BoxCubes}\ D\ L\ r$. -/
def qacAnchorOfCube {D L : ℕ} [NeZero L] (r : ℕ) (A : Finset (BoxD D L)) : BoxD D L :=
  if hA : A ∈ boxCubes D L r then (Finset.mem_image.mp hA).choose
  else fun _ => ⟨0, NeZero.pos L⟩

/-- Reconstructs $A = \mathrm{boxCube}(\mathrm{qacAnchorOfCube}\ r\ A, r)$ for every $A \in \mathrm{BoxCubes}\ D\ L\ r$. -/
lemma boxCube_qacAnchorOfCube {D L : ℕ} [NeZero L] (r : ℕ) {A : Finset (BoxD D L)}
    (hA : A ∈ boxCubes D L r) :
    boxCube (qacAnchorOfCube r A) r = A := by
  dsimp [qacAnchorOfCube]
  rw [dif_pos hA]
  exact (Finset.mem_image.mp hA).choose_spec.2

/-- Parameterized site-anchored perturbation operator for any cube-anchor map
    `anchor : ℕ → Finset (BoxD D L) → BoxD D L`. When `anchor = anchorOfCube` in
    `Defs.BHMStability`, this is definitionally (`rfl`) equal to `sitePerturbationOp V u`. -/
def anchoredSitePerturbationOp {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    (anchor : ℕ → Finset (BoxD D L) → BoxD D L)
    (V : QuasiLocalPerturbation D L Site) (u : BoxD D L) :
    ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site :=
  ∑ q ∈ Finset.Icc 1 L,
    ∑ A ∈ (boxCubes D L q).filter (fun A => anchor q A = u), V.term q A

/-- Canonical site-anchored perturbation operator using `qacAnchorOfCube`. -/
def qacSitePerturbationOp {D L : ℕ} [NeZero L]
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    (V : QuasiLocalPerturbation D L Site) (u : BoxD D L) :
    ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site :=
  anchoredSitePerturbationOp qacAnchorOfCube V u

/-- Self-adjointness of `anchoredSitePerturbationOp anchor V u`. -/
theorem isSelfAdjoint_anchoredSitePerturbationOp {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    (anchor : ℕ → Finset (BoxD D L) → BoxD D L)
    (V : QuasiLocalPerturbation D L Site) (u : BoxD D L) :
    IsSelfAdjoint (anchoredSitePerturbationOp anchor V u) :=
  isSelfAdjoint_finset_sum _ _ (fun q _ =>
    isSelfAdjoint_finset_sum _ _ (fun A _ => V.is_selfAdjoint q A))

/-- If `anchor q A` reconstructs `boxCube (anchor q A) q = A` for all `A ∈ BoxCubes D L q`, then
    at most one cube in `BoxCubes D L q` has anchor `u`, namely `boxCube u q`. -/
lemma filter_anchor_subset_singleton {D L : ℕ}
    {anchor : ℕ → Finset (BoxD D L) → BoxD D L} (q : ℕ) (u : BoxD D L)
    (h_anchor : ∀ A ∈ boxCubes D L q, boxCube (anchor q A) q = A) :
    (boxCubes D L q).filter (fun A => anchor q A = u) ⊆ {boxCube u q} := by
  intro A hA
  rw [Finset.mem_filter] at hA
  rw [Finset.mem_singleton, ← h_anchor A hA.1, hA.2]

/-- Cardinality of `(BoxCubes D L q).filter (fun A => anchor q A = u)` is at most $1$ whenever
    `∀ A ∈ BoxCubes D L q, boxCube (anchor q A) q = A`. -/
lemma card_filter_anchor_le_one {D L : ℕ}
    {anchor : ℕ → Finset (BoxD D L) → BoxD D L} (q : ℕ) (u : BoxD D L)
    (h_anchor : ∀ A ∈ boxCubes D L q, boxCube (anchor q A) q = A) :
    ((boxCubes D L q).filter (fun A => anchor q A = u)).card ≤ 1 := by
  calc ((boxCubes D L q).filter (fun A => anchor q A = u)).card
    _ ≤ ({boxCube u q} : Finset (Finset (BoxD D L))).card :=
      Finset.card_le_card (filter_anchor_subset_singleton q u h_anchor)
    _ = 1 := Finset.card_singleton _

/-- Nonnegativity `0 ≤ J * f q` for `q ∈ Finset.Icc 1 L` deduced directly from `V.SatisfiesDecayBound J f`
    and any site `u : BoxD D L`. -/
lemma mul_decay_nonneg_of_satisfiesDecayBound {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    (V : QuasiLocalPerturbation D L Site) {J : ℝ} {f : ℕ → ℝ}
    (hV : V.SatisfiesDecayBound J f) (u : BoxD D L)
    {q : ℕ} (hq : q ∈ Finset.Icc 1 L) :
    0 ≤ J * f q := by
  have h_cube : boxCube u q ∈ boxCubes D L q :=
    Finset.mem_image_of_mem _ (Finset.mem_univ u)
  exact le_trans (norm_nonneg (V.term q (boxCube u q))) (hV q hq (boxCube u q) h_cube)

/-- **Explicit $O(J)$ Norm Bound for `anchoredSitePerturbationOp` (`norm_anchoredSitePerturbationOp_le`)**:
    If `V.SatisfiesDecayBound J f` and `∀ q ∈ Finset.Icc 1 L, ∀ A ∈ BoxCubes D L q, boxCube (anchor q A) q = A`,
    then for every site `u : BoxD D L`,
    $$\|\mathrm{anchoredSitePerturbationOp}\ \mathrm{anchor}\ V\ u\| \le J \sum_{q \in \mathrm{Icc}\ 1\ L} f(q).$$ -/
theorem norm_anchoredSitePerturbationOp_le {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    {anchor : ℕ → Finset (BoxD D L) → BoxD D L}
    (V : QuasiLocalPerturbation D L Site) {J : ℝ} {f : ℕ → ℝ}
    (hV : V.SatisfiesDecayBound J f) (u : BoxD D L)
    (h_anchor : ∀ q ∈ Finset.Icc 1 L, ∀ A ∈ boxCubes D L q, boxCube (anchor q A) q = A) :
    ‖anchoredSitePerturbationOp anchor V u‖ ≤ J * ∑ q ∈ Finset.Icc 1 L, f q := by
  have h_inner : ∀ q ∈ Finset.Icc 1 L,
      ‖∑ A ∈ (boxCubes D L q).filter (fun A => anchor q A = u), V.term q A‖ ≤ J * f q := by
    intro q hq
    have hJf : 0 ≤ J * f q := mul_decay_nonneg_of_satisfiesDecayBound V hV u hq
    have hcard : (((boxCubes D L q).filter (fun A => anchor q A = u)).card : ℝ) ≤ 1 := by
      exact_mod_cast card_filter_anchor_le_one q u (h_anchor q hq)
    calc ‖∑ A ∈ (boxCubes D L q).filter (fun A => anchor q A = u), V.term q A‖
      _ ≤ ∑ A ∈ (boxCubes D L q).filter (fun A => anchor q A = u), ‖V.term q A‖ :=
        norm_sum_le _ _
      _ ≤ ∑ _A ∈ (boxCubes D L q).filter (fun A => anchor q A = u), (J * f q) :=
        Finset.sum_le_sum (fun A hA => hV q hq A (Finset.mem_filter.mp hA).1)
      _ = (((boxCubes D L q).filter (fun A => anchor q A = u)).card : ℝ) * (J * f q) := by
        rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ 1 * (J * f q) := mul_le_mul_of_nonneg_right hcard hJf
      _ = J * f q := one_mul _
  calc ‖anchoredSitePerturbationOp anchor V u‖
    _ ≤ ∑ q ∈ Finset.Icc 1 L,
          ‖∑ A ∈ (boxCubes D L q).filter (fun A => anchor q A = u), V.term q A‖ :=
      norm_sum_le _ _
    _ ≤ ∑ q ∈ Finset.Icc 1 L, J * f q := Finset.sum_le_sum h_inner
    _ = J * ∑ q ∈ Finset.Icc 1 L, f q := by rw [← Finset.mul_sum]

/-- Inclusion `Finset.Icc 1 L ⊆ Finset.range (L + 1)`. -/
lemma icc_one_subset_range_succ (L : ℕ) : Finset.Icc 1 L ⊆ Finset.range (L + 1) := by
  intro q hq
  rw [Finset.mem_Icc] at hq
  rw [Finset.mem_range]
  omega

/-- Range-indexed variant of `norm_anchoredSitePerturbationOp_le`: when `0 ≤ J` and `∀ r, 0 ≤ f r`,
    $$\|\mathrm{anchoredSitePerturbationOp}\ \mathrm{anchor}\ V\ u\|
      \le J \sum_{r \in \mathrm{range}(L + 1)} f(r).$$ -/
theorem norm_anchoredSitePerturbationOp_le_range {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    {anchor : ℕ → Finset (BoxD D L) → BoxD D L}
    (V : QuasiLocalPerturbation D L Site) {J : ℝ} {f : ℕ → ℝ}
    (hV : V.SatisfiesDecayBound J f) (hJ : 0 ≤ J) (hf : ∀ r, 0 ≤ f r) (u : BoxD D L)
    (h_anchor : ∀ q ∈ Finset.Icc 1 L, ∀ A ∈ boxCubes D L q, boxCube (anchor q A) q = A) :
    ‖anchoredSitePerturbationOp anchor V u‖ ≤ J * ∑ r ∈ Finset.range (L + 1), f r := by
  have h1 := norm_anchoredSitePerturbationOp_le V hV u h_anchor
  have h2 : ∑ q ∈ Finset.Icc 1 L, f q ≤ ∑ r ∈ Finset.range (L + 1), f r :=
    Finset.sum_le_sum_of_subset_of_nonneg (icc_one_subset_range_succ L) (fun r _ _ => hf r)
  exact le_trans h1 (mul_le_mul_of_nonneg_left h2 hJ)

/-- Specialization of `norm_anchoredSitePerturbationOp_le` to `qacSitePerturbationOp`. -/
theorem norm_qacSitePerturbationOp_le {D L : ℕ} [NeZero L]
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    (V : QuasiLocalPerturbation D L Site) {J : ℝ} {f : ℕ → ℝ}
    (hV : V.SatisfiesDecayBound J f) (u : BoxD D L) :
    ‖qacSitePerturbationOp V u‖ ≤ J * ∑ q ∈ Finset.Icc 1 L, f q :=
  norm_anchoredSitePerturbationOp_le V hV u (fun q _ _ hA => boxCube_qacAnchorOfCube q hA)

/-- Specialization of `norm_anchoredSitePerturbationOp_le_range` to `qacSitePerturbationOp`. -/
theorem norm_qacSitePerturbationOp_le_range {D L : ℕ} [NeZero L]
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    (V : QuasiLocalPerturbation D L Site) {J : ℝ} {f : ℕ → ℝ}
    (hV : V.SatisfiesDecayBound J f) (hJ : 0 ≤ J) (hf : ∀ r, 0 ≤ f r) (u : BoxD D L) :
    ‖qacSitePerturbationOp V u‖ ≤ J * ∑ r ∈ Finset.range (L + 1), f r :=
  norm_anchoredSitePerturbationOp_le_range V hV hJ hf u
    (fun q _ _ hA => boxCube_qacAnchorOfCube q hA)

/-!
## 2. Explicit $O(J)$ Local Check Commutator Bound `norm_opCommutator_V_tot_localOp_le`
-/

/-- Commutator linearity on the left over a finite sum:
    `opCommutator (∑ a ∈ s, g a) Q = ∑ a ∈ s, opCommutator (g a) Q`. -/
lemma opCommutator_sum_left {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    {α : Type*} (s : Finset α) (g : α → (E →L[ℂ] E)) (Q : E →L[ℂ] E) :
    opCommutator (∑ a ∈ s, g a) Q = ∑ a ∈ s, opCommutator (g a) Q := by
  unfold opCommutator
  rw [Finset.sum_mul, Finset.mul_sum, ← Finset.sum_sub_distrib]

/-- If $Q$ is supported on $S_0 \subseteq \mathrm{BoxD}\ D\ L$, then $[V_{\mathrm{tot}}, Q]$ receives
    contributions only from cubes $A \in \mathrm{BoxCubes}\ D\ L\ q$ that intersect $S_0$
    ($\neg \mathrm{Disjoint}\ A\ S_0$). -/
theorem opCommutator_V_tot_eq_sum_filter_not_disjoint {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    (V : QuasiLocalPerturbation D L Site) {S_0 : Finset (BoxD D L)}
    {Q : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site}
    (hQ : IsSupportedOn Site S_0 Q) :
    opCommutator V.totalPerturbation Q =
      ∑ q ∈ Finset.Icc 1 L,
        ∑ A ∈ (boxCubes D L q).filter (fun A => ¬ Disjoint A S_0),
          opCommutator (V.term q A) Q := by
  dsimp [QuasiLocalPerturbation.totalPerturbation]
  rw [opCommutator_sum_left]
  refine Finset.sum_congr rfl (fun q hq => ?_)
  rw [opCommutator_sum_left]
  rw [← Finset.sum_filter_add_sum_filter_not (boxCubes D L q) (fun A => ¬ Disjoint A S_0)]
  have h_zero : ∑ A ∈ (boxCubes D L q).filter (fun A => ¬¬ Disjoint A S_0),
      opCommutator (V.term q A) Q = 0 := by
    refine Finset.sum_eq_zero (fun A hA => ?_)
    rw [Finset.mem_filter, not_not] at hA
    exact opCommutator_eq_zero_of_disjoint hA.2 (V.is_supported q hq A hA.1) hQ
  rw [h_zero, add_zero]

/-- Site-dependent overlap commutator factor counting cubes $A \in \mathrm{BoxCubes}\ D\ L\ q$
    that intersect $S_0$, weighted by $f(q)$. -/
def siteOverlapCommutatorFactor (D L : ℕ) (S_0 : Finset (BoxD D L)) (f : ℕ → ℝ) : ℝ :=
  ∑ q ∈ Finset.Icc 1 L,
    (((boxCubes D L q).filter (fun A => ¬ Disjoint A S_0)).card : ℝ) * f q

/-- Uniform-in-$u$ cube overlap commutator factor taking the supremum over $u \in \mathrm{BoxD}\ D\ L$
    of the number of scale-$q$ cubes intersecting $\mathrm{boxCube}(u, r_0)$, weighted by $f(q)$. -/
def uniformCubeCommutatorFactor (D L r_0 : ℕ) (f : ℕ → ℝ) : ℝ :=
  ∑ q ∈ Finset.Icc 1 L,
    ((Finset.univ.sup (fun u : BoxD D L =>
      ((boxCubes D L q).filter (fun A => ¬ Disjoint A (boxCube u r_0))).card) : ℕ) : ℝ) * f q

/-- Nonnegativity of `siteOverlapCommutatorFactor` when $f \ge 0$ on $\mathrm{Icc}\ 1\ L$. -/
lemma siteOverlapCommutatorFactor_nonneg (D L : ℕ) (S_0 : Finset (BoxD D L)) {f : ℕ → ℝ}
    (hf : ∀ q ∈ Finset.Icc 1 L, 0 ≤ f q) :
    0 ≤ siteOverlapCommutatorFactor D L S_0 f :=
  Finset.sum_nonneg (fun q hq => mul_nonneg (Nat.cast_nonneg _) (hf q hq))

/-- Nonnegativity of `uniformCubeCommutatorFactor` when $f \ge 0$ on $\mathrm{Icc}\ 1\ L$. -/
lemma uniformCubeCommutatorFactor_nonneg (D L r_0 : ℕ) {f : ℕ → ℝ}
    (hf : ∀ q ∈ Finset.Icc 1 L, 0 ≤ f q) :
    0 ≤ uniformCubeCommutatorFactor D L r_0 f :=
  Finset.sum_nonneg (fun q hq => mul_nonneg (Nat.cast_nonneg _) (hf q hq))

/-- For any site $u \in \mathrm{BoxD}\ D\ L$ and radius $r_0$, the site-dependent overlap factor on
    $\mathrm{boxCube}(u, r_0)$ is bounded by `uniformCubeCommutatorFactor D L r_0 f` whenever $f \ge 0$. -/
lemma siteOverlapCommutatorFactor_boxCube_le_uniformCubeCommutatorFactor
    {D L : ℕ} (u : BoxD D L) (r_0 : ℕ) {f : ℕ → ℝ}
    (hf : ∀ q ∈ Finset.Icc 1 L, 0 ≤ f q) :
    siteOverlapCommutatorFactor D L (boxCube u r_0) f ≤
      uniformCubeCommutatorFactor D L r_0 f := by
  dsimp [siteOverlapCommutatorFactor, uniformCubeCommutatorFactor]
  refine Finset.sum_le_sum (fun q hq => ?_)
  apply mul_le_mul_of_nonneg_right _ (hf q hq)
  exact Nat.cast_le.mpr (Finset.le_sup (f := fun v : BoxD D L =>
    ((boxCubes D L q).filter (fun A => ¬ Disjoint A (boxCube v r_0))).card) (Finset.mem_univ u))

/-- **Explicit $O(J)$ Commutator Bound for Arbitrary Local Support (`norm_opCommutator_V_tot_localOp_le`)**:
    If `V.SatisfiesDecayBound J f` and `IsSupportedOn Site S_0 Q` (with nonnegativity witnessed by
    any site `u0 : BoxD D L`), then
    $$\|[V_{\mathrm{tot}}, Q]\| \le 2 \|Q\| J \cdot \mathrm{siteOverlapCommutatorFactor}(D, L, S_0, f).$$ -/
theorem norm_opCommutator_V_tot_localOp_le {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    (V : QuasiLocalPerturbation D L Site) {J : ℝ} {f : ℕ → ℝ}
    (hV : V.SatisfiesDecayBound J f) (_u0 : BoxD D L)
    {S_0 : Finset (BoxD D L)}
    {Q : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site}
    (hQ : IsSupportedOn Site S_0 Q) :
    ‖opCommutator V.totalPerturbation Q‖ ≤ 2 * ‖Q‖ * J * siteOverlapCommutatorFactor D L S_0 f := by
  rw [opCommutator_V_tot_eq_sum_filter_not_disjoint V hQ]
  have h_inner : ∀ q ∈ Finset.Icc 1 L,
      ‖∑ A ∈ (boxCubes D L q).filter (fun A => ¬ Disjoint A S_0), opCommutator (V.term q A) Q‖ ≤
        (2 * ‖Q‖ * J) *
          ((((boxCubes D L q).filter (fun A => ¬ Disjoint A S_0)).card : ℝ) * f q) := by
    intro q hq
    calc ‖∑ A ∈ (boxCubes D L q).filter (fun A => ¬ Disjoint A S_0), opCommutator (V.term q A) Q‖
      _ ≤ ∑ A ∈ (boxCubes D L q).filter (fun A => ¬ Disjoint A S_0), ‖opCommutator (V.term q A) Q‖ :=
        norm_sum_le _ _
      _ ≤ ∑ _A ∈ (boxCubes D L q).filter (fun A => ¬ Disjoint A S_0), (2 * (J * f q) * ‖Q‖) := by
        refine Finset.sum_le_sum (fun A hA => ?_)
        have h1 := norm_opCommutator_le (V.term q A) Q
        have h2 := hV q hq A (Finset.mem_filter.mp hA).1
        have h3 : 2 * ‖V.term q A‖ * ‖Q‖ ≤ 2 * (J * f q) * ‖Q‖ :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h2 zero_le_two) (norm_nonneg Q)
        exact le_trans h1 h3
      _ = (((boxCubes D L q).filter (fun A => ¬ Disjoint A S_0)).card : ℝ) * (2 * (J * f q) * ‖Q‖) := by
        rw [Finset.sum_const, nsmul_eq_mul]
      _ = (2 * ‖Q‖ * J) *
            ((((boxCubes D L q).filter (fun A => ¬ Disjoint A S_0)).card : ℝ) * f q) := by ring
  calc ‖∑ q ∈ Finset.Icc 1 L,
          ∑ A ∈ (boxCubes D L q).filter (fun A => ¬ Disjoint A S_0), opCommutator (V.term q A) Q‖
    _ ≤ ∑ q ∈ Finset.Icc 1 L,
          ‖∑ A ∈ (boxCubes D L q).filter (fun A => ¬ Disjoint A S_0), opCommutator (V.term q A) Q‖ :=
      norm_sum_le _ _
    _ ≤ ∑ q ∈ Finset.Icc 1 L,
          (2 * ‖Q‖ * J) *
            ((((boxCubes D L q).filter (fun A => ¬ Disjoint A S_0)).card : ℝ) * f q) :=
      Finset.sum_le_sum h_inner
    _ = 2 * ‖Q‖ * J * siteOverlapCommutatorFactor D L S_0 f := by
      dsimp [siteOverlapCommutatorFactor]
      rw [← Finset.mul_sum]

/-- **Uniform-in-$u$ Explicit $O(J)$ Commutator Bound for Cube-Supported Operators
    (`norm_opCommutator_V_tot_boxCube_le_uniform`)**:
    If `V.SatisfiesDecayBound J f` and `IsSupportedOn Site (boxCube u r_0) Q_u`, then
    $$\|[V_{\mathrm{tot}}, Q_u]\| \le 2 \|Q_u\| J \cdot \mathrm{uniformCubeCommutatorFactor}(D, L, r_0, f).$$ -/
theorem norm_opCommutator_V_tot_boxCube_le_uniform {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    (V : QuasiLocalPerturbation D L Site) {J : ℝ} {f : ℕ → ℝ}
    (hV : V.SatisfiesDecayBound J f)
    (u : BoxD D L) (r_0 : ℕ)
    {Q_u : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site}
    (hQ : IsSupportedOn Site (boxCube u r_0) Q_u) :
    ‖opCommutator V.totalPerturbation Q_u‖ ≤ 2 * ‖Q_u‖ * J * uniformCubeCommutatorFactor D L r_0 f := by
  have h1 := norm_opCommutator_V_tot_localOp_le V hV u hQ
  have h_sum_le :
      J * siteOverlapCommutatorFactor D L (boxCube u r_0) f ≤
        J * uniformCubeCommutatorFactor D L r_0 f := by
    dsimp [siteOverlapCommutatorFactor, uniformCubeCommutatorFactor]
    rw [Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_le_sum (fun q hq => ?_)
    have hJf : 0 ≤ J * f q := mul_decay_nonneg_of_satisfiesDecayBound V hV u hq
    have hcard : (((boxCubes D L q).filter (fun A => ¬ Disjoint A (boxCube u r_0))).card : ℝ) ≤
        ((Finset.univ.sup (fun v : BoxD D L =>
          ((boxCubes D L q).filter (fun A => ¬ Disjoint A (boxCube v r_0))).card) : ℕ) : ℝ) :=
      Nat.cast_le.mpr (Finset.le_sup (f := fun v : BoxD D L =>
        ((boxCubes D L q).filter (fun A => ¬ Disjoint A (boxCube v r_0))).card) (Finset.mem_univ u))
    calc J * ((((boxCubes D L q).filter (fun A => ¬ Disjoint A (boxCube u r_0))).card : ℝ) * f q)
      _ = (((boxCubes D L q).filter (fun A => ¬ Disjoint A (boxCube u r_0))).card : ℝ) * (J * f q) := by ring
      _ ≤ ((Finset.univ.sup (fun v : BoxD D L =>
            ((boxCubes D L q).filter (fun A => ¬ Disjoint A (boxCube v r_0))).card) : ℕ) : ℝ) * (J * f q) :=
        mul_le_mul_of_nonneg_right hcard hJf
      _ = J * (((Finset.univ.sup (fun v : BoxD D L =>
            ((boxCubes D L q).filter (fun A => ¬ Disjoint A (boxCube v r_0))).card) : ℕ) : ℝ) * f q) := by ring
  have h2 : 2 * ‖Q_u‖ * (J * siteOverlapCommutatorFactor D L (boxCube u r_0) f) ≤
      2 * ‖Q_u‖ * (J * uniformCubeCommutatorFactor D L r_0 f) :=
    mul_le_mul_of_nonneg_left h_sum_le (by positivity)
  linarith

/-!
## 3. Explicit $O(J)$ Bare-Frame Check Drift & Three-Term `condExp` Tail Bounds
-/

/-- **Explicit $O(J)$ Bare-Frame Bochner Check Drift Bound (`norm_bochnerFilteredOp_sub_self_le_of_satisfiesDecayBound`)**:
    When $[H_0, Q_u] = 0$, `V.SatisfiesDecayBound J f`, and `IsSupportedOn Site (boxCube u r_0) Q_u`,
    $$\|\mathcal{F}_w^{H_0 + V_{\mathrm{tot}}}(Q_u) - Q_u\|
      \le \left(\int \|w(t)\| |t|\,dt\right) \left(2 \|Q_u\| J \cdot \mathrm{uniformCubeCommutatorFactor}(D, L, r_0, f)\right).$$ -/
theorem norm_bochnerFilteredOp_sub_self_le_of_satisfiesDecayBound {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    {H0 Q_u : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site}
    (V : QuasiLocalPerturbation D L Site) {J : ℝ} {f : ℕ → ℝ}
    (hH : IsSelfAdjoint (H0 + V.totalPerturbation)) (h_comm : Commute H0 Q_u)
    (hV : V.SatisfiesDecayBound J f)
    (u : BoxD D L) (r_0 : ℕ) (hQ : IsSupportedOn Site (boxCube u r_0) Q_u)
    {w : ℝ → ℂ} (hw_int : Integrable w) (hw_one : (∫ t : ℝ, w t) = 1)
    (hw_t_int : Integrable (fun t : ℝ => ‖w t‖ * |t|)) :
    ‖bochnerFilteredOp (H0 + V.totalPerturbation) w Q_u - Q_u‖ ≤
      (∫ t : ℝ, ‖w t‖ * |t|) * (2 * ‖Q_u‖ * J * uniformCubeCommutatorFactor D L r_0 f) := by
  have h1 := norm_bochnerFilteredOp_sub_self_le_of_commute_left hH h_comm hw_int hw_one hw_t_int
  have h2 := norm_opCommutator_V_tot_boxCube_le_uniform V hV u r_0 hQ
  have h_int_nn : 0 ≤ ∫ t : ℝ, ‖w t‖ * |t| :=
    integral_nonneg (fun t => mul_nonneg (norm_nonneg (w t)) (abs_nonneg t))
  exact le_trans h1 (mul_le_mul_of_nonneg_left h2 h_int_nn)

/-- Specialization of `norm_bochnerFilteredOp_sub_self_le_of_satisfiesDecayBound` to `bhFilterWeight`:
    $$\|\mathcal{F}_{w_{\mathrm{BH11}}}^{H_0 + V_{\mathrm{tot}}}(Q_u) - Q_u\|
      \le 2 \pi \|Q_u\| J \cdot \mathrm{uniformCubeCommutatorFactor}(D, L, r_0, f).$$ -/
theorem norm_bochnerFilteredOp_w_BH11_sub_self_le_of_satisfiesDecayBound {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    {H0 Q_u : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site}
    (V : QuasiLocalPerturbation D L Site) {J : ℝ} {f : ℕ → ℝ}
    (hH : IsSelfAdjoint (H0 + V.totalPerturbation)) (h_comm : Commute H0 Q_u)
    (hV : V.SatisfiesDecayBound J f)
    (u : BoxD D L) (r_0 : ℕ) (hQ : IsSupportedOn Site (boxCube u r_0) Q_u) :
    ‖bochnerFilteredOp (H0 + V.totalPerturbation) bhFilterWeight Q_u - Q_u‖ ≤
      2 * Real.pi * ‖Q_u‖ * J * uniformCubeCommutatorFactor D L r_0 f := by
  rcases integrable_and_integral_norm_w_BH11_mul_abs_le with ⟨hw_t_int, hw_t_le⟩
  have h1 := norm_bochnerFilteredOp_sub_self_le_of_satisfiesDecayBound
    V hH h_comm hV u r_0 hQ integrable_w_BH11 integral_w_BH11_eq_one hw_t_int
  have h_comm_nn : 0 ≤ 2 * ‖Q_u‖ * J * uniformCubeCommutatorFactor D L r_0 f :=
    le_trans (norm_nonneg _) (norm_opCommutator_V_tot_boxCube_le_uniform V hV u r_0 hQ)
  have h2 := mul_le_mul_of_nonneg_right hw_t_le h_comm_nn
  linarith

/-- **Explicit $J$-Factored Three-Term Bare-Split `condExp` Tail Bound
    (`norm_bochnerFilteredSiteOp_sub_condExp_le_J_mul_of_satisfiesDecayBound`)**:
    Combines `norm_bochnerFilteredSiteOp_sub_condExp_le_of_bare_split_and_unitary_tail`
    (`Proofs.BandLimitedFilter.BochnerFilterUnitaryCovariance`; Part I, Proposition 6.4 (`prop:qac-block-diagonalization`), Equation (79) (`eq:Xu-bare-three-term`)),
    `norm_anchoredSitePerturbationOp_le`, and `norm_opCommutator_V_tot_boxCube_le_uniform` so that when `ε_bare_V ≤ J * g_bare_V`,
    `ε_bare_Q ≤ J * g_bare_Q`, and `ε_LR_Q ≤ J * g_LR_Q`, the `condExp` tail on `boxCube u K`
    satisfies an explicit $O(J)$ bound with $J$ factored out of every term:
    $$\|X_u - \mathbb{E}_{\mathrm{boxCube}(u, K)}(X_u)\| \le
      J \cdot \left(2 g_{\mathrm{bare}, V} + 2 g_{\mathrm{bare}, Q} +
        \varepsilon_{\mathrm{LR}} \left(\sum_{q=1}^L f(q) +
          2 \pi C_Q \cdot \mathrm{uniformCubeCommutatorFactor}(D, L, r_0, f)\right) +
        g_{\mathrm{LR}, Q}\right).$$ -/
theorem norm_bochnerFilteredSiteOp_sub_condExp_le_J_mul_of_satisfiesDecayBound {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    [∀ x, Nonempty (Site x)]
    {anchor : ℕ → Finset (BoxD D L) → BoxD D L}
    {H0 Q_u : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site}
    (V : QuasiLocalPerturbation D L Site) {J : ℝ} {f : ℕ → ℝ}
    (hJ : 0 ≤ J) (hf : ∀ q ∈ Finset.Icc 1 L, 0 ≤ f q)
    (hV : V.SatisfiesDecayBound J f)
    (h_anchor : ∀ q ∈ Finset.Icc 1 L, ∀ A ∈ boxCubes D L q, boxCube (anchor q A) q = A)
    (hH : IsSelfAdjoint (H0 + V.totalPerturbation)) (h_comm : Commute H0 Q_u)
    (U_dress : unitary (ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site))
    (u : BoxD D L) (K r_bare r_0 : ℕ)
    {C_Q g_bare_V g_bare_Q ε_LR g_LR_Q : ℝ} (hε_LR_nn : 0 ≤ ε_LR)
    (hQ_norm : ‖Q_u‖ ≤ C_Q)
    (hQ_supp_0 : IsSupportedOn Site (boxCube u r_0) Q_u)
    (hQ_supp_bare : IsSupportedOn Site (boxCube u r_bare) Q_u)
    (hQ_supp_K : IsSupportedOn Site (boxCube u K) Q_u)
    (h_bare_V :
      ‖bochnerFilteredOp (H0 + V.totalPerturbation) bhFilterWeight (anchoredSitePerturbationOp anchor V u) -
        condExp Site (boxCube u r_bare)
          (bochnerFilteredOp (H0 + V.totalPerturbation) bhFilterWeight (anchoredSitePerturbationOp anchor V u))‖ ≤
        J * g_bare_V)
    (h_bare_Q :
      ‖bochnerFilteredOp (H0 + V.totalPerturbation) bhFilterWeight Q_u -
        condExp Site (boxCube u r_bare)
          (bochnerFilteredOp (H0 + V.totalPerturbation) bhFilterWeight Q_u)‖ ≤ J * g_bare_Q)
    (h_U_tail : ∀ B_loc : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site,
      IsSupportedOn Site (boxCube u r_bare) B_loc →
      ‖U_dress.1† * B_loc * U_dress.1 -
        condExp Site (boxCube u K) (U_dress.1† * B_loc * U_dress.1)‖ ≤ ε_LR * ‖B_loc‖)
    (h_U_Q_tail :
      ‖U_dress.1† * Q_u * U_dress.1 -
        condExp Site (boxCube u K) (U_dress.1† * Q_u * U_dress.1)‖ ≤ J * g_LR_Q) :
    let X_u := bochnerFilteredSiteOp (U_dress.1† * (H0 + V.totalPerturbation) * U_dress.1)
      U_dress.1 bhFilterWeight (anchoredSitePerturbationOp anchor V u) Q_u
    ‖X_u - condExp Site (boxCube u K) X_u‖ ≤
      J * (2 * g_bare_V + 2 * g_bare_Q +
        ε_LR * ((∑ q ∈ Finset.Icc 1 L, f q) +
          2 * Real.pi * C_Q * uniformCubeCommutatorFactor D L r_0 f) +
        g_LR_Q) := by
  intro X_u
  rcases integrable_and_integral_norm_w_BH11_mul_abs_le with ⟨hw_t_int, hw_t_le⟩
  have h_base := norm_bochnerFilteredSiteOp_sub_condExp_le_of_bare_split_and_unitary_tail
    hH h_comm U_dress integrable_w_BH11 integral_w_BH11_eq_one hw_t_int
    u K r_bare hε_LR_nn hQ_supp_bare hQ_supp_K h_bare_V h_bare_Q h_U_tail h_U_Q_tail
  dsimp only at h_base
  rw [integral_norm_w_BH11_eq_one, one_mul] at h_base
  have hVu_le : ‖anchoredSitePerturbationOp anchor V u‖ ≤ J * ∑ q ∈ Finset.Icc 1 L, f q :=
    norm_anchoredSitePerturbationOp_le V hV u h_anchor
  have h_uc_nn : 0 ≤ uniformCubeCommutatorFactor D L r_0 f :=
    uniformCubeCommutatorFactor_nonneg D L r_0 hf
  have h_comm_le : ‖opCommutator V.totalPerturbation Q_u‖ ≤
      J * (2 * C_Q * uniformCubeCommutatorFactor D L r_0 f) := by
    have h1 := norm_opCommutator_V_tot_boxCube_le_uniform V hV u r_0 hQ_supp_0
    have h2 : 2 * ‖Q_u‖ * J * uniformCubeCommutatorFactor D L r_0 f ≤
        2 * C_Q * J * uniformCubeCommutatorFactor D L r_0 f := by
      have h_mul := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hQ_norm zero_le_two) hJ
      exact mul_le_mul_of_nonneg_right h_mul h_uc_nn
    linarith
  have h_wt_comm : (∫ t : ℝ, ‖bhFilterWeight t‖ * |t|) * ‖opCommutator V.totalPerturbation Q_u‖ ≤
      J * (2 * Real.pi * C_Q * uniformCubeCommutatorFactor D L r_0 f) := by
    have h1 : (∫ t : ℝ, ‖bhFilterWeight t‖ * |t|) * ‖opCommutator V.totalPerturbation Q_u‖ ≤
        Real.pi * ‖opCommutator V.totalPerturbation Q_u‖ :=
      mul_le_mul_of_nonneg_right hw_t_le (norm_nonneg _)
    have h2 : Real.pi * ‖opCommutator V.totalPerturbation Q_u‖ ≤
        Real.pi * (J * (2 * C_Q * uniformCubeCommutatorFactor D L r_0 f)) :=
      mul_le_mul_of_nonneg_left h_comm_le Real.pi_pos.le
    linarith
  have h_mid :
      ε_LR * (‖anchoredSitePerturbationOp anchor V u‖ +
        (∫ t : ℝ, ‖bhFilterWeight t‖ * |t|) * ‖opCommutator V.totalPerturbation Q_u‖) ≤
      ε_LR * (J * ∑ q ∈ Finset.Icc 1 L, f q +
        J * (2 * Real.pi * C_Q * uniformCubeCommutatorFactor D L r_0 f)) :=
    mul_le_mul_of_nonneg_left (add_le_add hVu_le h_wt_comm) hε_LR_nn
  linarith

end
