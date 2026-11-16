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

import Defs.BHMStability
import Proofs.CubeTelescoping.CoarseCubeFunctor
import Proofs.GapBootstrap.CourantFischerAndBootstrap
import Proofs.LiebRobinson.DuhamelAndGronwall
import Proofs.KatoHastingsFlow.KatoHastingsODEFlow

/-!
# Constructive Kato–Hastings ODE Flows and Sector-Filtered Scale-r Form Bounds

Proves constructive existence and Duhamel integral properties of `IsKatoHastingsFlowSystem` on finite-dimensional many-body Hilbert spaces without spectral low-pass filter hypotheses, establishes `(2(r + R) + 1)^D` enclosing-cube multiplicity bounds against `H0`, and proves sector-filtered scale-`r` relative form bounds for `indexedLocalBlockDiagonalProjection`.

## References

* Part I, Section 6.3 (`subsec:qac-block-diag`), Proposition 6.4 (`prop:qac-block-diagonalization`)
* Part I, Section 7.1 (`subsec:single-cube-telescoping`), Lemma 7.1 (`lem:norm-transfer`)
* Part I, Section 7.2 (`subsec:gap-bootstrap`), Theorem 7.3 (`thm:gap-bootstrap`)
* Bravyi, Hastings, and Michalakis (2010), J. Math. Phys. 51, 093512
* Bravyi and Hastings (2011), Commun. Math. Phys. 307, 609–627
-/

noncomputable section

open scoped Classical InnerProduct ComplexConjugate BigOperators
open Filter Topology Asymptotics ContinuousLinearMap MeasureTheory

/-!
## 1. Unconditional Constructive Kato–Hastings Flow Existence & Universal ODE Properties
-/

/-- **Unconditional Kato–Hastings Flow Existence & Universal ODE Package
    (`theorem_unconditional_kato_hastings_flow_and_duhamel`)**:
    For any initial projector $P_0$:
    1. (**Constructive Existence**): For every self-adjoint generator $D_0$, the autonomous flow
       `D_gen s = D0`, `U_flow s = timeEvolutionOp D0 s`, `P_flow s = heisenbergFlow D0 s P0`
       satisfies `IsKatoHastingsFlowSystem P0 D_gen U_flow P_flow` with `D_gen 0 = D0`;
    2. (**Universal ODE Unitarity, Intertwining & Duhamel Bound**): Every solution
       `(D_gen, U_flow, P_flow)` of `IsKatoHastingsFlowSystem P0 D_gen U_flow P_flow` satisfies
       unitarity, exact subspace intertwining $(U_{\mathrm{flow}}(s))^\dagger P_{\mathrm{flow}}(s) U_{\mathrm{flow}}(s) = P_0$,
       commutation transport, and the linear-in-$s$ Duhamel conjugation bound. -/
theorem theorem_unconditional_kato_hastings_flow_and_duhamel {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    (P0 : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site) :
    (∀ (D0 : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site),
      IsSelfAdjoint D0 →
      ∃ (D_gen U_flow P_flow : ℝ →
          (ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site)),
        D_gen 0 = D0 ∧
        IsKatoHastingsFlowSystem P0 D_gen U_flow P_flow) ∧
    (∀ (D_gen U_flow P_flow : ℝ →
        (ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site)),
      IsKatoHastingsFlowSystem P0 D_gen U_flow P_flow →
      (∀ s : ℝ, (U_flow s)† * U_flow s = 1 ∧ U_flow s * (U_flow s)† = 1) ∧
      (∀ s : ℝ, (U_flow s)† * P_flow s * U_flow s = P0) ∧
      (∀ (s : ℝ) (H_s : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site),
        Commute H_s (P_flow s) → Commute ((U_flow s)† * H_s * U_flow s) P0) ∧
      (∀ (O : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site)
        (s ε_comm : ℝ), 0 ≤ s →
        (∀ τ ∈ Set.Icc 0 s, ‖O * D_gen τ - D_gen τ * O‖ ≤ ε_comm) →
        ‖(U_flow s)† * O * U_flow s - O‖ ≤ s * ε_comm)) := by
  refine ⟨?_, ?_⟩
  · intro D0 hD0
    refine ⟨fun _ => D0, fun s => timeEvolutionOp D0 s, fun s => heisenbergFlow D0 s P0, rfl, ?_⟩
    exact
      { isSelfAdjoint_D := fun _ => hD0
        U_zero := timeEvolutionOp_zero D0
        P_zero := by dsimp [heisenbergFlow]; rw [neg_zero, timeEvolutionOp_zero, one_mul, mul_one]
        hasDerivAt_U := fun s => hasDerivAt_timeEvolutionOp D0 s
        hasDerivAt_P := fun s => hasDerivAt_heisenbergFlow D0 P0 s }
  · intro D_gen U_flow P_flow hFlow
    have h_ode := kato_hastings_ode_flow P0 D_gen U_flow P_flow hFlow
    exact ⟨h_ode.1, h_ode.2.1, h_ode.2.2,
      fun O s ε_comm hs h_comm =>
        (duhamel_conjugation_bound P0 D_gen U_flow P_flow hFlow O).2 s ε_comm hs h_comm⟩

/-!
## 2. Direct Enclosing-Cube Multiplicity and Quadratic Form Bounds on `IndexedCommutingProjectorHamiltonian`
-/

/-- An operator supported on the empty finset `∅` is a scalar multiple of the identity operator. -/
lemma isSupportedOn_empty_eq_smul_one_bhm {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    {O : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site}
    (hO : IsSupportedOn Site (∅ : Finset (BoxD D L)) O) :
    ∃ c : ℂ, O = c • (1 : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site) := by
  rcases hO with ⟨O_loc, rfl⟩
  let α₀ : LocalConfig Site (∅ : Finset (BoxD D L)) := fun x => False.elim (Finset.notMem_empty x.1 x.2)
  let v₀ : LocalHilbertSpace Site (∅ : Finset (BoxD D L)) := WithLp.toLp 2 (fun _ => (1 : ℂ))
  refine ⟨(O_loc v₀).ofLp α₀, ?_⟩
  ext ψ σ
  have h_splice : ∀ α : LocalConfig Site (∅ : Finset (BoxD D L)), spliceConfig ∅ α σ = σ := by
    intro α; funext x; simp [spliceConfig]
  have h_vec : WithLp.toLp 2 (fun α : LocalConfig Site ∅ => ψ.ofLp (spliceConfig ∅ α σ)) =
      (ψ.ofLp σ) • v₀ := by ext α; simp [v₀, h_splice]
  have h_rest : restrictConfig (∅ : Finset (BoxD D L)) σ = α₀ := by
    funext x; exact False.elim (Finset.notMem_empty x.1 x.2)
  change (O_loc (WithLp.toLp 2 (fun α : LocalConfig Site ∅ =>
      ψ.ofLp (spliceConfig ∅ α σ)))).ofLp (restrictConfig ∅ σ) = (O_loc v₀).ofLp α₀ * ψ.ofLp σ
  rw [h_vec, h_rest, map_smul]
  change ψ.ofLp σ * (O_loc v₀).ofLp α₀ = (O_loc v₀).ofLp α₀ * ψ.ofLp σ
  ring

/-- Every check $Q_i$ of an `IndexedCommutingProjectorHamiltonian` is annihilated on the right by `sys.P0`. -/
lemma IndexedCommutingProjectorHamiltonian.checkProj_mul_P0_eq_zero {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (sys : IndexedCommutingProjectorHamiltonian D L Site ι) (i : ι) :
    sys.checkProj i * sys.P0 = 0 := by
  rw [← sys.localProj_univ_eq_proj0]
  exact sys.checkProj_mul_P_loc_eq_zero i Finset.univ (Finset.subset_univ _)

/-- In an abstract inner product space, `c • P = 0` with `P ≠ 0` implies `c = 0`. -/
lemma eq_zero_of_smul_eq_zero_bhm {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] {P : E →L[ℂ] E} {c : ℂ} (hP : P ≠ 0) (h : c • P = 0) :
    c = 0 :=
  (smul_eq_zero.mp h).resolve_right hP

/-- Any check of an `IndexedCommutingProjectorHamiltonian` with empty support is identically zero. -/
lemma IndexedCommutingProjectorHamiltonian.checkProj_eq_zero_of_support_empty {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (sys : IndexedCommutingProjectorHamiltonian D L Site ι) {i : ι}
    (h_empty : sys.support i = ∅) :
    sys.checkProj i = 0 := by
  have h_supp : IsSupportedOn Site (∅ : Finset (BoxD D L)) (sys.checkProj i) := by
    rw [← h_empty]; exact sys.is_supported i
  rcases isSupportedOn_empty_eq_smul_one_bhm h_supp with ⟨c, hc⟩
  have h_mul_P0 : sys.checkProj i * sys.P0 = 0 := sys.checkProj_mul_P0_eq_zero i
  rw [hc, smul_mul_assoc, one_mul] at h_mul_P0
  have hc0 : c = 0 := eq_zero_of_smul_eq_zero_bhm sys.frustration_free h_mul_P0
  rw [hc, hc0]; ext x; simp

/-- Any lattice site $y_0 \in \mathrm{BoxD}\ D\ L$ belongs to at most $(2 R)^D$ enclosing cubes
    $\mathrm{enclosingBoxCube}(\mathrm{anchorOfCube}(r, A), r, R)$ as $A$ ranges over $\mathrm{BoxCubes}\ D\ L\ r$. -/
lemma card_filter_mem_enclosingBoxCube_le_pow {D L : ℕ} [NeZero D] [NeZero L]
    (r R : ℕ) (y0 : BoxD D L) :
    ((boxCubes D L r).filter (fun A => y0 ∈ enclosingBoxCube (anchorOfCube r A) r R)).card ≤
      (2 * R) ^ D := by
  by_cases hR : R = 0
  · subst hR
    have h_empty :
        (boxCubes D L r).filter (fun A => y0 ∈ enclosingBoxCube (anchorOfCube r A) r 0) = ∅ := by
      rw [Finset.filter_eq_empty_iff]
      intro A _ hy0_mem
      rw [enclosingBoxCube, mem_boxCube] at hy0_mem
      have hi0 := hy0_mem ⟨0, NeZero.pos D⟩; omega
    rw [h_empty, Finset.card_empty]; exact Nat.zero_le _
  · let d : ℕ := (R - r) / 2
    have hd_le_R : d ≤ R := by dsimp [d]; omega
    have hL_pos : 0 < L := NeZero.pos L
    let g : (Fin D → Fin (2 * R)) → Finset (BoxD D L) := fun k =>
      boxCube (fun i => ⟨min (L - 1) ((y0 i).val + d - (k i).val),
        Nat.lt_of_le_of_lt (Nat.min_le_left _ _) (Nat.sub_lt hL_pos zero_lt_one)⟩) r
    have h_sub :
        (boxCubes D L r).filter (fun A => y0 ∈ enclosingBoxCube (anchorOfCube r A) r R) ⊆
          Finset.univ.image g := by
      intro A hA
      rcases Finset.mem_filter.mp hA with ⟨hA_mem, hy0_encl⟩
      simp only [enclosingBoxCube, mem_boxCube] at hy0_encl
      let xA := anchorOfCube r A
      have hk_lt : ∀ i : Fin D, (y0 i).val + d - (xA i).val < 2 * R := by
        intro i
        have hi : (xA i).val - d ≤ (y0 i).val ∧ (y0 i).val < (xA i).val - d + R := hy0_encl i
        omega
      let k : Fin D → Fin (2 * R) := fun i => ⟨(y0 i).val + d - (xA i).val, hk_lt i⟩
      have h_anchor : (fun i : Fin D => (⟨min (L - 1) ((y0 i).val + d - (k i).val),
          Nat.lt_of_le_of_lt (Nat.min_le_left _ _) (Nat.sub_lt hL_pos zero_lt_one)⟩ : Fin L)) = xA := by
        funext i; apply Fin.ext
        have hi : (xA i).val - d ≤ (y0 i).val ∧ (y0 i).val < (xA i).val - d + R := hy0_encl i
        have hxA_lt : (xA i).val < L := (xA i).isLt
        change min (L - 1) ((y0 i).val + d - ((y0 i).val + d - (xA i).val)) = (xA i).val
        omega
      rw [Finset.mem_image]
      refine ⟨k, Finset.mem_univ k, ?_⟩
      dsimp [g]; rw [h_anchor, boxCube_anchorOfCube hA_mem]
    calc ((boxCubes D L r).filter (fun A => y0 ∈ enclosingBoxCube (anchorOfCube r A) r R)).card
      _ ≤ (Finset.univ.image g).card := Finset.card_le_card h_sub
      _ ≤ (Finset.univ : Finset (Fin D → Fin (2 * R))).card := Finset.card_image_le
      _ = (2 * R) ^ D := by rw [Finset.card_univ, Fintype.card_fun, Fintype.card_fin, Fintype.card_fin]

/-- For any `IndexedCommutingProjectorHamiltonian sys` and region $B$,
    $\|(1 - \mathrm{sys.P\_loc}\ B)\psi\|^2 \le \sum_{i : \mathrm{supp}(Q_i) \subseteq B} \|Q_i \psi\|^2$. -/
lemma IndexedCommutingProjectorHamiltonian.norm_one_sub_P_loc_sq_le_sum {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (sys : IndexedCommutingProjectorHamiltonian D L Site ι)
    (B : Finset (BoxD D L)) (ψ : ManyBodyHilbertSpace Site) :
    ‖(1 - sys.localGroundProj B) ψ‖ ^ 2 ≤
      ∑ i ∈ Finset.univ.filter (fun i : ι => sys.support i ⊆ B), ‖sys.checkProj i ψ‖ ^ 2 := by
  dsimp [IndexedCommutingProjectorHamiltonian.localGroundProj,
    IndexedCommutingProjectorHamiltonian.localGroundProj]
  set S := (Finset.univ : Finset ι).filter (fun i : ι => sys.support i ⊆ B)
  set l := S.toList
  have h_proj : ∀ p ∈ l.map (fun i : ι => 1 - sys.checkProj i), IsStarProjection p := by
    intro p hp
    rcases List.mem_map.mp hp with ⟨i, _, rfl⟩
    exact (sys.is_projector i).one_sub
  have h_comm : (l.map (fun i : ι => 1 - sys.checkProj i)).Pairwise Commute := by
    rw [List.pairwise_map]
    refine List.Pairwise.imp_of_mem ?_ S.nodup_toList
    intro i j _ _ _
    exact commute_one_sub_right_bhm (commute_one_sub_left_bhm (sys.pairwise_commute i j))
  have h_sum_le := norm_one_sub_list_prod_sq_le_sum (l.map (fun i : ι => 1 - sys.checkProj i))
    h_proj h_comm ψ
  rw [List.map_map] at h_sum_le
  have h_comp : ((fun p => ‖(1 - p) ψ‖ ^ 2) ∘ fun i : ι => 1 - sys.checkProj i) =
      (fun i : ι => ‖sys.checkProj i ψ‖ ^ 2) := by
    funext i
    change ‖(1 - (1 - sys.checkProj i)) ψ‖ ^ 2 = ‖sys.checkProj i ψ‖ ^ 2
    rw [sub_sub_cancel]
  rw [h_comp, Finset.sum_map_toList] at h_sum_le
  exact h_sum_le

/-- For any `IndexedCommutingProjectorHamiltonian sys` with `∀ i : ι, 1 ≤ sys.weight i`,
    $\sum_{i : \iota} \|\mathrm{sys.checkProj}\ i\ \psi\|^2 \le \mathrm{re}\langle \psi, \mathrm{sys.H0}\ \psi \rangle$. -/
lemma IndexedCommutingProjectorHamiltonian.sum_norm_checkProj_sq_le_re_inner_H0 {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (sys : IndexedCommutingProjectorHamiltonian D L Site ι)
    (h_weight : ∀ i : ι, 1 ≤ sys.weight i)
    (ψ : ManyBodyHilbertSpace Site) :
    ∑ i : ι, ‖sys.checkProj i ψ‖ ^ 2 ≤ RCLike.re (inner ℂ ψ (sys.H0 ψ)) := by
  dsimp [IndexedCommutingProjectorHamiltonian.H0]
  rw [ContinuousLinearMap.sum_apply, inner_sum, Complex.re_sum]
  refine Finset.sum_le_sum fun i _ => ?_
  rw [ContinuousLinearMap.smul_apply, inner_smul_right, Complex.re_ofReal_mul]
  change ‖sys.checkProj i ψ‖ ^ 2 ≤ sys.weight i * RCLike.re (inner ℂ ψ (sys.checkProj i ψ))
  rw [isStarProjection_re_inner_eq_norm_sq_bhm (sys.is_projector i) ψ]
  calc ‖sys.checkProj i ψ‖ ^ 2
    _ = 1 * ‖sys.checkProj i ψ‖ ^ 2 := (one_mul _).symm
    _ ≤ sys.weight i * ‖sys.checkProj i ψ‖ ^ 2 :=
      mul_le_mul_of_nonneg_right (h_weight i) (sq_nonneg _)

/-- Double-sum counting bound on `IndexedCommutingProjectorHamiltonian`:
    summing $\sum_{i : \mathrm{supp}(Q_i) \subseteq B(A, R)} \|Q_i \psi\|^2$ over all $A \in \mathrm{BoxCubes}\ D\ L\ r$
    is bounded by $(2 R)^D \, \mathrm{re}\langle \psi, \mathrm{sys.H0}\ \psi \rangle$. -/
lemma IndexedCommutingProjectorHamiltonian.sum_filter_enclosingBoxCube_le_pow_mul_re_inner_H0
    {D L : ℕ} [NeZero D] [NeZero L]
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (sys : IndexedCommutingProjectorHamiltonian D L Site ι)
    (h_weight : ∀ i : ι, 1 ≤ sys.weight i)
    (r R : ℕ) (ψ : ManyBodyHilbertSpace Site) :
    ∑ A ∈ boxCubes D L r,
      ∑ i ∈ Finset.univ.filter
          (fun i : ι => sys.support i ⊆ enclosingBoxCube (anchorOfCube r A) r R),
        ‖sys.checkProj i ψ‖ ^ 2 ≤
      (((2 * R : ℕ) : ℝ) ^ D) * RCLike.re (inner ℂ ψ (sys.H0 ψ)) := by
  let B : Finset (BoxD D L) → Finset (BoxD D L) :=
    fun A => enclosingBoxCube (anchorOfCube r A) r R
  have h_swap :
      ∑ A ∈ boxCubes D L r,
        ∑ i ∈ Finset.univ.filter (fun i : ι => sys.support i ⊆ B A), ‖sys.checkProj i ψ‖ ^ 2 =
      ∑ i : ι,
        (((boxCubes D L r).filter (fun A => sys.support i ⊆ B A)).card : ℝ) *
          ‖sys.checkProj i ψ‖ ^ 2 := by
    simp_rw [Finset.sum_filter]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
  rw [h_swap]
  have h_each : ∀ i : ι,
      (((boxCubes D L r).filter (fun A => sys.support i ⊆ B A)).card : ℝ) *
        ‖sys.checkProj i ψ‖ ^ 2 ≤
      (((2 * R : ℕ) : ℝ) ^ D) * ‖sys.checkProj i ψ‖ ^ 2 := by
    intro i
    by_cases h_ne : (sys.support i).Nonempty
    · let y0 := h_ne.choose
      have hy0_mem : y0 ∈ sys.support i := h_ne.choose_spec
      have h_sub :
          (boxCubes D L r).filter (fun A => sys.support i ⊆ B A) ⊆
          (boxCubes D L r).filter (fun A => y0 ∈ B A) := by
        intro A hA
        rcases Finset.mem_filter.mp hA with ⟨hA_mem, hi_sub⟩
        exact Finset.mem_filter.mpr ⟨hA_mem, hi_sub hy0_mem⟩
      have h_card :
          ((boxCubes D L r).filter (fun A => sys.support i ⊆ B A)).card ≤ (2 * R) ^ D :=
        le_trans (Finset.card_le_card h_sub) (card_filter_mem_enclosingBoxCube_le_pow r R y0)
      apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
      exact_mod_cast h_card
    · have h_empty : sys.support i = ∅ := Finset.not_nonempty_iff_eq_empty.mp h_ne
      have hQ_zero : sys.checkProj i = 0 := sys.checkProj_eq_zero_of_support_empty h_empty
      rw [hQ_zero, ContinuousLinearMap.zero_apply, norm_zero, sq, mul_zero, mul_zero, mul_zero]
  calc ∑ i : ι,
        (((boxCubes D L r).filter (fun A => sys.support i ⊆ B A)).card : ℝ) *
          ‖sys.checkProj i ψ‖ ^ 2
    _ ≤ ∑ i : ι, (((2 * R : ℕ) : ℝ) ^ D) * ‖sys.checkProj i ψ‖ ^ 2 :=
      Finset.sum_le_sum (fun i _ => h_each i)
    _ = (((2 * R : ℕ) : ℝ) ^ D) * ∑ i : ι, ‖sys.checkProj i ψ‖ ^ 2 := by
      rw [← Finset.mul_sum]
    _ ≤ (((2 * R : ℕ) : ℝ) ^ D) * RCLike.re (inner ℂ ψ (sys.H0 ψ)) :=
      mul_le_mul_of_nonneg_left (sys.sum_norm_checkProj_sq_le_re_inner_H0 h_weight ψ)
        (pow_nonneg (Nat.cast_nonneg _) D)

/-- Every check commutes with `sys.P_loc B` and every check in $B$ commutes with `Pi_sec`, so
    `sys.P_loc B` commutes with `Pi_sec`. -/
lemma IndexedCommutingProjectorHamiltonian.commute_P_loc_Pi_sec {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (sys : IndexedCommutingProjectorHamiltonian D L Site ι)
    {Pi_sec : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site}
    (h_comm : ∀ i : ι, Commute (sys.checkProj i) Pi_sec)
    (B : Finset (BoxD D L)) :
    Commute (sys.localGroundProj B) Pi_sec := by
  dsimp [IndexedCommutingProjectorHamiltonian.localGroundProj,
    IndexedCommutingProjectorHamiltonian.localGroundProj]
  apply Commute.list_prod_left
  intro p hp
  rcases List.mem_map.mp hp with ⟨i, _, rfl⟩
  exact commute_one_sub_left_bhm (h_comm i)

/-!
## 3. Canonical Locally Block-Diagonal Perturbation & Sector-Filtered Scale-$r$ Form Bounds
-/

/-- **Canonical Locally Block-Diagonal Projection (`indexedLocalBlockDiagonalProjection`)**:
    Given `sys : IndexedCommutingProjectorHamiltonian D L Site ι` and `V : QuasiLocalPerturbation D L Site`,
    projects each local term `V.term r A` onto the local excited subspace of cube $A$:
    $$\widetilde{V}_{r, A} := (1 - \mathrm{sys.P\_loc}\ A) \, V_{r, A} \, (1 - \mathrm{sys.P\_loc}\ A).$$ -/
def indexedLocalBlockDiagonalProjection {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (sys : IndexedCommutingProjectorHamiltonian D L Site ι)
    (V : QuasiLocalPerturbation D L Site) :
    QuasiLocalPerturbation D L Site where
  term r A := (1 - sys.localGroundProj A) * V.term r A * (1 - sys.localGroundProj A)
  is_selfAdjoint r A := by
    rw [isSelfAdjoint_iff]
    have h1 : star (1 - sys.localGroundProj A) = 1 - sys.localGroundProj A :=
      (sys.isStarProjection_P_loc_bhm A).one_sub.isSelfAdjoint.star_eq
    rw [star_mul, star_mul, h1, (V.is_selfAdjoint r A).star_eq, mul_assoc]
  is_supported r hr A hA := by
    have h1PA : IsSupportedOn Site A (1 - sys.localGroundProj A) :=
      isSupportedOn_sub A (isSupportedOn_one A) (sys.isSupportedOn_P_loc A)
    exact isSupportedOn_mul A (isSupportedOn_mul A h1PA (V.is_supported r hr A hA)) h1PA

/-- `indexedLocalBlockDiagonalProjection sys V` preserves `SatisfiesDecayBound J f` and commutes
    termwise with `sys.P0`. -/
lemma indexedLocalBlockDiagonalProjection_properties {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (sys : IndexedCommutingProjectorHamiltonian D L Site ι)
    (V : QuasiLocalPerturbation D L Site)
    {J : ℝ} {f : ℕ → ℝ} (hV : V.SatisfiesDecayBound J f) :
    (indexedLocalBlockDiagonalProjection sys V).SatisfiesDecayBound J f ∧
    (∀ r : ℕ, ∀ A : Finset (BoxD D L),
      Commute ((indexedLocalBlockDiagonalProjection sys V).term r A) sys.P0) := by
  refine ⟨?_, ?_⟩
  · intro r hr A hA
    dsimp [indexedLocalBlockDiagonalProjection]
    have h_norm1 : ‖1 - sys.localGroundProj A‖ ≤ 1 :=
      isStarProjection_norm_le_one_bhm (sys.isStarProjection_P_loc_bhm A).one_sub
    exact le_trans (norm_sandwich_le_of_norm_le_one h_norm1 h_norm1) (hV r hr A hA)
  · intro r A
    dsimp [indexedLocalBlockDiagonalProjection]
    have hR : (1 - sys.localGroundProj A) * sys.P0 = 0 := by
      rw [sub_mul, one_mul, (sys.localProj_mul_proj0_eq_proj0 A).1, sub_self]
    have hL : sys.P0 * (1 - sys.localGroundProj A) = 0 := by
      rw [mul_sub, mul_one, (sys.localProj_mul_proj0_eq_proj0 A).2, sub_self]
    rw [commute_iff_eq]
    calc (1 - sys.localGroundProj A) * V.term r A * (1 - sys.localGroundProj A) * sys.P0
      _ = (1 - sys.localGroundProj A) * V.term r A * ((1 - sys.localGroundProj A) * sys.P0) := by rw [mul_assoc]
      _ = 0 := by rw [hR, mul_zero]
      _ = (sys.P0 * (1 - sys.localGroundProj A)) * V.term r A * (1 - sys.localGroundProj A) := by
        rw [hL, zero_mul, zero_mul]
      _ = sys.P0 * ((1 - sys.localGroundProj A) * V.term r A * (1 - sys.localGroundProj A)) := by
        simp only [mul_assoc]

/-- Quadratic form bound for a self-adjoint operator $M$ that annihilates $\mathrm{sys.P\_loc}\ B$
    on the right ($M \cdot \mathrm{sys.P\_loc}\ B = 0$). -/
lemma abs_re_inner_le_of_mul_P_loc_eq_zero {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (sys : IndexedCommutingProjectorHamiltonian D L Site ι)
    (B : Finset (BoxD D L))
    {M : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site}
    (hM_sa : IsSelfAdjoint M)
    (hM_P : M * sys.localGroundProj B = 0)
    (ϕ : ManyBodyHilbertSpace Site) :
    |RCLike.re (inner ℂ ϕ (M ϕ))| ≤
      ‖M‖ * ∑ i ∈ Finset.univ.filter (fun i : ι => sys.support i ⊆ B), ‖sys.checkProj i ϕ‖ ^ 2 := by
  let Q_B := 1 - sys.localGroundProj B
  have hP_M : sys.localGroundProj B * M = 0 := by
    have h1 := eq_zero_of_mul_eq_zero_of_isSelfAdjoint_bhm
      (sys.isStarProjection_P_loc_bhm B).isSelfAdjoint hM_sa 0
      (by simpa using hM_P)
    simpa using h1
  have h_sandwich : Q_B * M * Q_B = M := by
    dsimp [Q_B]
    calc (1 - sys.localGroundProj B) * M * (1 - sys.localGroundProj B)
      _ = (M - sys.localGroundProj B * M) * (1 - sys.localGroundProj B) := by rw [sub_mul, one_mul]
      _ = M * (1 - sys.localGroundProj B) := by rw [hP_M, sub_zero]
      _ = M - M * sys.localGroundProj B := by rw [mul_sub, mul_one]
      _ = M := by rw [hM_P, sub_zero]
  have hQ_sa : IsSelfAdjoint Q_B := (sys.isStarProjection_P_loc_bhm B).one_sub.isSelfAdjoint
  have hQ_adj : Q_B† = Q_B := ContinuousLinearMap.isSelfAdjoint_iff'.mp hQ_sa
  have h_inner : inner ℂ ϕ (M ϕ) = inner ℂ (Q_B ϕ) (M (Q_B ϕ)) := by
    conv_lhs => rw [← h_sandwich]
    change inner ℂ ϕ (Q_B (M (Q_B ϕ))) = inner ℂ (Q_B ϕ) (M (Q_B ϕ))
    rw [← ContinuousLinearMap.adjoint_inner_left, hQ_adj]
  rw [h_inner]
  calc |RCLike.re (inner ℂ (Q_B ϕ) (M (Q_B ϕ)))|
    _ ≤ ‖M‖ * ‖Q_B ϕ‖ ^ 2 := abs_re_inner_le_opNorm_mul_norm_sq M (Q_B ϕ)
    _ ≤ ‖M‖ * ∑ i ∈ Finset.univ.filter (fun i : ι => sys.support i ⊆ B), ‖sys.checkProj i ϕ‖ ^ 2 :=
      mul_le_mul_of_nonneg_left (sys.norm_one_sub_P_loc_sq_le_sum B ϕ) (norm_nonneg M)

/-- **Sector-Filtered Local Sandwich Decomposition (`exists_indexed_sector_sandwich_of_tqo_bhm`)**:
    Under `SatisfiesSectorFilteredLinearTQO2 sys Pi_sec L_star C`, for any $1 \le r \le L^*$,
    anchor $x_0 \in \mathrm{BoxD}\ D\ L$, and self-adjoint operator $O$ supported on
    $A = \mathrm{boxCube}(x_0, r)$ that commutes with `sys.P0`, there exists a real scalar
    $c \in \mathbb{R}$ with $|c| \le \|O\|$ such that $M := O - c \cdot 1$ satisfies
    $\|M\| \le 2 \|O\|$ and $M \cdot \Pi_{\mathrm{sec}} \cdot \mathrm{sys.P\_loc}(B) = 0$
    for $B = \mathrm{enclosingBoxCube}(x_0, r, \mathrm{linearExpansionRadius}\ C\ r)$. -/
lemma exists_indexed_sector_sandwich_of_tqo_bhm {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (sys : IndexedCommutingProjectorHamiltonian D L Site ι)
    {Pi_sec : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site}
    {L_star : ℕ} {C : ℝ}
    (h_tqo : SatisfiesSectorFilteredLinearTQO2 sys Pi_sec L_star C)
    {r : ℕ} (hr1 : 1 ≤ r) (hrL : r ≤ L_star)
    (x0 : BoxD D L)
    (O : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site)
    (hO_sa : IsSelfAdjoint O)
    (hO_supp : IsSupportedOn Site (boxCube x0 r) O)
    (hO_comm : Commute O sys.P0) :
    ∃ c : ℝ,
      |c| ≤ ‖O‖ ∧
      ‖O - (c : ℂ) • (1 : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site)‖ ≤ 2 * ‖O‖ ∧
      (O - (c : ℂ) • (1 : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site)) *
        Pi_sec * sys.localGroundProj (enclosingBoxCube x0 r (linearExpansionRadius C r)) = 0 := by
  rcases h_tqo with ⟨_hPi_proj, _hPi_comm, _hP0_Pi, hTQO1, hTQO2_sec⟩
  rcases hTQO1 r hr1 hrL x0 O hO_supp with ⟨c_C, hc_C⟩
  have hP_idem : sys.P0 * sys.P0 = sys.P0 := sys.isStarProjection_P0.isIdempotentElem.eq
  have hOP : O * sys.P0 = c_C • sys.P0 := by
    calc O * sys.P0
      _ = O * (sys.P0 * sys.P0) := by rw [hP_idem]
      _ = (O * sys.P0) * sys.P0 := by rw [mul_assoc]
      _ = (sys.P0 * O) * sys.P0 := by rw [hO_comm.eq]
      _ = sys.P0 * O * sys.P0 := rfl
      _ = c_C • sys.P0 := hc_C
  rcases tqo1_scalar_abs_le_norm_bhm sys.isStarProjection_P0 sys.frustration_free hc_C with
    ⟨hc_C_norm, hc_C_im⟩
  have hc_im : c_C.im = 0 := hc_C_im hO_sa
  let c : ℝ := c_C.re
  have hc_eq : (c : ℂ) = c_C := Complex.ext rfl hc_im.symm
  have hc_norm : |c| ≤ ‖O‖ := by
    have h1 : ‖(c : ℂ)‖ = ‖c_C‖ := by rw [hc_eq]
    rw [Complex.norm_real, Real.norm_eq_abs] at h1
    linarith
  let M := O - (c : ℂ) • (1 : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site)
  have hM_norm : ‖M‖ ≤ 2 * ‖O‖ := by
    calc ‖M‖
      _ ≤ ‖O‖ + ‖(c : ℂ) • (1 : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site)‖ :=
        norm_sub_le O _
      _ = ‖O‖ + |c| * ‖(1 : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site)‖ := by
        rw [norm_smul, Complex.norm_real, Real.norm_eq_abs]
      _ ≤ ‖O‖ + |c| * 1 := by
        gcongr
        exact ContinuousLinearMap.norm_id_le
      _ ≤ ‖O‖ + ‖O‖ * 1 := by gcongr
      _ = 2 * ‖O‖ := by ring
  have hMP : M * sys.P0 = 0 := by
    apply ContinuousLinearMap.ext
    intro ψ
    change (O - (c : ℂ) • 1) (sys.P0 ψ) = 0
    rw [ContinuousLinearMap.sub_apply, ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.one_apply, ← ContinuousLinearMap.mul_apply, hOP,
      ContinuousLinearMap.smul_apply, hc_eq, sub_self]
  have hM_supp : IsSupportedOn Site (boxCube x0 r) M :=
    isSupportedOn_sub_smul_one hO_supp (c : ℂ)
  have hMP_loc : M * Pi_sec * sys.localGroundProj (enclosingBoxCube x0 r (linearExpansionRadius C r)) = 0 :=
    (hTQO2_sec r hr1 hrL x0 M hM_supp).mp hMP
  exact ⟨c, hc_norm, hM_norm, hMP_loc⟩

/-- **Indexed Scale-$r$ Relative Form Bound for `indexedLocalBlockDiagonalProjection`
    (`localBlockDiagonal_scale_r_form_bound`)**:
    For every scale $1 \le r \le L$ and $C \ge 1$, the scale-$r$ sum of
    `indexedLocalBlockDiagonalProjection sys V` is form-bounded by
    $(2 J ((2 R_C(r))^D) f(r)) \mathrm{re}\langle \phi, \mathrm{sys.H0}\ \phi \rangle$. -/
lemma localBlockDiagonal_scale_r_form_bound {D L : ℕ} [NeZero D] [NeZero L]
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (sys : IndexedCommutingProjectorHamiltonian D L Site ι)
    (h_weight : ∀ i : ι, 1 ≤ sys.weight i)
    (V : QuasiLocalPerturbation D L Site)
    {C J : ℝ} {f : ℕ → ℝ} (hC : 1 ≤ C)
    (hJ : 0 ≤ J) (hf_nonneg : ∀ r : ℕ, 0 ≤ f r)
    (hV_decay : V.SatisfiesDecayBound J f)
    {r : ℕ} (hr1 : 1 ≤ r) (hrL : r ≤ L)
    (ϕ : ManyBodyHilbertSpace Site) :
    |RCLike.re (inner ℂ ϕ ((∑ A ∈ boxCubes D L r,
        (indexedLocalBlockDiagonalProjection sys V).term r A) ϕ))| ≤
      (2 * J * (((2 * linearExpansionRadius C r : ℕ) : ℝ) ^ D) * f r) *
        RCLike.re (inner ℂ ϕ (sys.H0 ϕ)) := by
  have hr_mem : r ∈ Finset.Icc 1 L := Finset.mem_Icc.mpr ⟨hr1, hrL⟩
  let R := linearExpansionRadius C r
  let V_loc := indexedLocalBlockDiagonalProjection sys V
  have hV_loc_decay : V_loc.SatisfiesDecayBound J f :=
    (indexedLocalBlockDiagonalProjection_properties sys V hV_decay).1
  rw [re_inner_sum_apply]
  calc |∑ A ∈ boxCubes D L r, RCLike.re (inner ℂ ϕ (V_loc.term r A ϕ))|
    _ ≤ ∑ A ∈ boxCubes D L r, |RCLike.re (inner ℂ ϕ (V_loc.term r A ϕ))| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ A ∈ boxCubes D L r,
        (2 * (J * f r)) *
          ∑ i ∈ Finset.univ.filter
              (fun i : ι => sys.support i ⊆ enclosingBoxCube (anchorOfCube r A) r R),
            ‖sys.checkProj i ϕ‖ ^ 2 := by
      refine Finset.sum_le_sum (fun A hA => ?_)
      let B_A := enclosingBoxCube (anchorOfCube r A) r R
      have hA_sub_B : A ⊆ B_A := by
        have h1 := boxCube_subset_enclosingBoxCube (anchorOfCube r A)
          (self_le_linearExpansionRadius_bhm hC r)
        rw [boxCube_anchorOfCube hA] at h1
        exact h1
      have h_mul_P_loc : V_loc.term r A * sys.localGroundProj B_A = 0 := by
        dsimp [V_loc, indexedLocalBlockDiagonalProjection]
        have h1P_B : (1 - sys.localGroundProj A) * sys.localGroundProj B_A = 0 := by
          rw [sub_mul, one_mul, (sys.localProj_mul_localProj_of_subset_bhm hA_sub_B).1, sub_self]
        rw [mul_assoc, h1P_B, mul_zero]
      have h_norm_le : ‖V_loc.term r A‖ ≤ 2 * (J * f r) := by
        have h1 := hV_loc_decay r hr_mem A hA
        have h_nn : 0 ≤ J * f r := mul_nonneg hJ (hf_nonneg r)
        linarith
      calc |RCLike.re (inner ℂ ϕ (V_loc.term r A ϕ))|
        _ ≤ ‖V_loc.term r A‖ *
            ∑ i ∈ Finset.univ.filter (fun i : ι => sys.support i ⊆ B_A), ‖sys.checkProj i ϕ‖ ^ 2 :=
          abs_re_inner_le_of_mul_P_loc_eq_zero sys B_A (V_loc.is_selfAdjoint r A) h_mul_P_loc ϕ
        _ ≤ (2 * (J * f r)) *
            ∑ i ∈ Finset.univ.filter (fun i : ι => sys.support i ⊆ B_A), ‖sys.checkProj i ϕ‖ ^ 2 :=
          mul_le_mul_of_nonneg_right h_norm_le (Finset.sum_nonneg (fun _ _ => sq_nonneg _))
    _ = (2 * (J * f r)) *
        ∑ A ∈ boxCubes D L r,
          ∑ i ∈ Finset.univ.filter
              (fun i : ι => sys.support i ⊆ enclosingBoxCube (anchorOfCube r A) r R),
            ‖sys.checkProj i ϕ‖ ^ 2 := by
      rw [← Finset.mul_sum]
    _ ≤ (2 * (J * f r)) *
        ((((2 * R : ℕ) : ℝ) ^ D) * RCLike.re (inner ℂ ϕ (sys.H0 ϕ))) := by
      apply mul_le_mul_of_nonneg_left
        (sys.sum_filter_enclosingBoxCube_le_pow_mul_re_inner_H0 h_weight r R ϕ)
      exact mul_nonneg (by norm_num) (mul_nonneg hJ (hf_nonneg r))
    _ = (2 * J * (((2 * R : ℕ) : ℝ) ^ D) * f r) * RCLike.re (inner ℂ ϕ (sys.H0 ϕ)) := by ring

/-- Self-adjointness of $O - c \cdot 1$ for self-adjoint $O$ and real $c$. -/
lemma isSelfAdjoint_sub_real_smul_one_bhm {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] [CompleteSpace E]
    {O : E →L[ℂ] E} (hO : IsSelfAdjoint O) (c : ℝ) :
    IsSelfAdjoint (O - (c : ℂ) • (1 : E →L[ℂ] E)) := by
  have h1 : IsSelfAdjoint ((c : ℂ) • (1 : E →L[ℂ] E)) := by
    rw [IsSelfAdjoint, star_smul, star_one, RCLike.star_def, Complex.conj_ofReal]
  exact hO.sub h1

/-- **Indexed Sector-Filtered Scale-$r$ Relative Form Bound (`indexed_sector_scale_r_form_bound`)**:
    Under `SatisfiesSectorFilteredLinearTQO2 sys Pi_sec L_star C`, for every scale $1 \le r \le L^*$
    and any perturbation $V$ whose scale-$r$ terms commute with `sys.P0`, there exists a real scalar
    $c_r \in \mathbb{R}$ such that on every in-sector state $\phi$ ($\Pi_{\mathrm{sec}} \phi = \phi$),
    $$\left|\mathrm{re}\langle \phi, \Big(\sum_{A \in \mathcal{S}(r)} V_{r, A}\Big)\phi \rangle - c_r \|\phi\|^2\right|
      \le (2 J ((2 R_C(r))^D) f(r)) \, \mathrm{re}\langle \phi, \mathrm{sys.H0}\ \phi \rangle.$$ -/
lemma indexed_sector_scale_r_form_bound {D L : ℕ} [NeZero D] [NeZero L]
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (sys : IndexedCommutingProjectorHamiltonian D L Site ι)
    (h_weight : ∀ i : ι, 1 ≤ sys.weight i)
    {Pi_sec : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site}
    {L_star : ℕ} {C J : ℝ} {f : ℕ → ℝ}
    (hJ : 0 ≤ J) (hf_nonneg : ∀ r : ℕ, 0 ≤ f r)
    (h_tqo : SatisfiesSectorFilteredLinearTQO2 sys Pi_sec L_star C)
    (V : QuasiLocalPerturbation D L Site)
    (hV_decay : V.SatisfiesDecayBound J f)
    {r : ℕ} (hr1 : 1 ≤ r) (hrL_star : r ≤ L_star) (hrL : r ≤ L)
    (h_comm : ∀ A ∈ boxCubes D L r, Commute (V.term r A) sys.P0) :
    ∃ c_r : ℝ, ∀ ϕ : ManyBodyHilbertSpace Site, Pi_sec ϕ = ϕ →
      |RCLike.re (inner ℂ ϕ ((∑ A ∈ boxCubes D L r, V.term r A) ϕ)) - c_r * ‖ϕ‖ ^ 2| ≤
        (2 * J * (((2 * linearExpansionRadius C r : ℕ) : ℝ) ^ D) * f r) *
          RCLike.re (inner ℂ ϕ (sys.H0 ϕ)) := by
  have hr_mem : r ∈ Finset.Icc 1 L := Finset.mem_Icc.mpr ⟨hr1, hrL⟩
  let R := linearExpansionRadius C r
  have h_exists_A : ∀ A : Finset (BoxD D L),
      ∃ c_A : ℝ, A ∈ boxCubes D L r →
        ‖V.term r A - (c_A : ℂ) • (1 : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site)‖ ≤
          2 * (J * f r) ∧
        (V.term r A - (c_A : ℂ) • (1 : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site)) *
          Pi_sec * sys.localGroundProj (enclosingBoxCube (anchorOfCube r A) r R) = 0 := by
    intro A
    by_cases hA : A ∈ boxCubes D L r
    · have h_supp : IsSupportedOn Site (boxCube (anchorOfCube r A) r) (V.term r A) := by
        rw [boxCube_anchorOfCube hA]
        exact V.is_supported r hr_mem A hA
      rcases exists_indexed_sector_sandwich_of_tqo_bhm sys h_tqo hr1 hrL_star
        (anchorOfCube r A) (V.term r A) (V.is_selfAdjoint r A) h_supp (h_comm A hA) with
        ⟨c_A, _, hM_norm, hMP_loc⟩
      refine ⟨c_A, fun _ => ⟨?_, hMP_loc⟩⟩
      exact le_trans hM_norm (mul_le_mul_of_nonneg_left (hV_decay r hr_mem A hA) (by norm_num))
    · exact ⟨0, fun h => False.elim (hA h)⟩
  choose c_fn hc_fn using h_exists_A
  refine ⟨∑ A ∈ boxCubes D L r, c_fn A, fun ϕ hϕ_sec => ?_⟩
  rw [re_inner_sum_apply, Finset.sum_mul, ← Finset.sum_sub_distrib]
  calc |∑ A ∈ boxCubes D L r, (RCLike.re (inner ℂ ϕ (V.term r A ϕ)) - c_fn A * ‖ϕ‖ ^ 2)|
    _ ≤ ∑ A ∈ boxCubes D L r, |RCLike.re (inner ℂ ϕ (V.term r A ϕ)) - c_fn A * ‖ϕ‖ ^ 2| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ A ∈ boxCubes D L r,
        (2 * (J * f r)) *
          ∑ i ∈ Finset.univ.filter
              (fun i : ι => sys.support i ⊆ enclosingBoxCube (anchorOfCube r A) r R),
            ‖sys.checkProj i ϕ‖ ^ 2 := by
      refine Finset.sum_le_sum (fun A hA => ?_)
      rcases hc_fn A hA with ⟨hM_norm, hMP_loc⟩
      let M_A := V.term r A - (c_fn A : ℂ) • (1 : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site)
      let B_A := enclosingBoxCube (anchorOfCube r A) r R
      have hM_sa : IsSelfAdjoint M_A :=
        isSelfAdjoint_sub_real_smul_one_bhm (V.is_selfAdjoint r A) (c_fn A)
      have hM_adj : M_A† = M_A := ContinuousLinearMap.isSelfAdjoint_iff'.mp hM_sa
      have h_diff : RCLike.re (inner ℂ ϕ (V.term r A ϕ)) - c_fn A * ‖ϕ‖ ^ 2 =
          RCLike.re (inner ℂ ϕ (M_A ϕ)) := by
        change RCLike.re (inner ℂ ϕ (V.term r A ϕ)) - c_fn A * ‖ϕ‖ ^ 2 =
          RCLike.re (inner ℂ ϕ ((V.term r A - (c_fn A : ℂ) • 1) ϕ))
        rw [ContinuousLinearMap.sub_apply, inner_sub_right, map_sub, re_inner_smul_one]
      rw [h_diff]
      let ϕ0 := sys.localGroundProj B_A ϕ
      let ϕ1 := (1 - sys.localGroundProj B_A) ϕ
      have hϕ_decomp : ϕ = ϕ0 + ϕ1 := by
        change ϕ = sys.localGroundProj B_A ϕ + (1 - sys.localGroundProj B_A) ϕ
        rw [ContinuousLinearMap.sub_apply, ContinuousLinearMap.one_apply, add_sub_cancel]
      have h_comm_PB_Pi : Commute (sys.localGroundProj B_A) Pi_sec :=
        sys.commute_P_loc_Pi_sec h_tqo.2.1 B_A
      have hM_ϕ0 : M_A ϕ0 = 0 := by
        calc M_A ϕ0
          _ = M_A (sys.localGroundProj B_A (Pi_sec ϕ)) := by
            change M_A (sys.localGroundProj B_A ϕ) = M_A (sys.localGroundProj B_A (Pi_sec ϕ))
            rw [hϕ_sec]
          _ = M_A ((sys.localGroundProj B_A * Pi_sec) ϕ) := rfl
          _ = M_A ((Pi_sec * sys.localGroundProj B_A) ϕ) := by rw [h_comm_PB_Pi.eq]
          _ = (M_A * Pi_sec * sys.localGroundProj B_A) ϕ := by simp only [ContinuousLinearMap.mul_apply]
          _ = 0 := by rw [hMP_loc, ContinuousLinearMap.zero_apply]
      have h_inner_eq : inner ℂ ϕ (M_A ϕ) = inner ℂ ϕ1 (M_A ϕ1) := by
        conv_lhs => rw [hϕ_decomp]
        rw [map_add, hM_ϕ0, zero_add, inner_add_left]
        have h_orth : inner ℂ ϕ0 (M_A ϕ1) = 0 := by
          rw [← ContinuousLinearMap.adjoint_inner_left, hM_adj, hM_ϕ0, inner_zero_left]
        rw [h_orth, zero_add]
      rw [h_inner_eq]
      calc |RCLike.re (inner ℂ ϕ1 (M_A ϕ1))|
        _ ≤ ‖M_A‖ * ‖ϕ1‖ ^ 2 := abs_re_inner_le_opNorm_mul_norm_sq M_A ϕ1
        _ ≤ ‖M_A‖ * ∑ i ∈ Finset.univ.filter (fun i : ι => sys.support i ⊆ B_A), ‖sys.checkProj i ϕ‖ ^ 2 :=
          mul_le_mul_of_nonneg_left (sys.norm_one_sub_P_loc_sq_le_sum B_A ϕ) (norm_nonneg M_A)
        _ ≤ (2 * (J * f r)) * ∑ i ∈ Finset.univ.filter (fun i : ι => sys.support i ⊆ B_A), ‖sys.checkProj i ϕ‖ ^ 2 :=
          mul_le_mul_of_nonneg_right hM_norm (Finset.sum_nonneg (fun _ _ => sq_nonneg _))
    _ = (2 * (J * f r)) * ∑ A ∈ boxCubes D L r,
          ∑ i ∈ Finset.univ.filter (fun i : ι => sys.support i ⊆ enclosingBoxCube (anchorOfCube r A) r R),
            ‖sys.checkProj i ϕ‖ ^ 2 := by rw [← Finset.mul_sum]
    _ ≤ (2 * (J * f r)) * ((((2 * R : ℕ) : ℝ) ^ D) * RCLike.re (inner ℂ ϕ (sys.H0 ϕ))) := by
      apply mul_le_mul_of_nonneg_left
        (sys.sum_filter_enclosingBoxCube_le_pow_mul_re_inner_H0 h_weight r R ϕ)
      exact mul_nonneg (by norm_num) (mul_nonneg hJ (hf_nonneg r))
    _ = (2 * J * (((2 * R : ℕ) : ℝ) ^ D) * f r) * RCLike.re (inner ℂ ϕ (sys.H0 ϕ)) := by ring

/-- `sys.H0` commutes with `sys.P0` for any `IndexedCommutingProjectorHamiltonian`. -/
lemma IndexedCommutingProjectorHamiltonian.commute_H0_P0 {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (sys : IndexedCommutingProjectorHamiltonian D L Site ι) :
    Commute sys.H0 sys.P0 := by
  dsimp [IndexedCommutingProjectorHamiltonian.H0]
  apply Commute.sum_left; intro i _; apply Commute.smul_left
  have hR : sys.checkProj i * sys.P0 = 0 := sys.checkProj_mul_P0_eq_zero i
  have hL : sys.P0 * sys.checkProj i = 0 := by
    simpa using eq_zero_of_mul_eq_zero_of_isSelfAdjoint_bhm
      sys.isStarProjection_P0.isSelfAdjoint (sys.is_projector i).isSelfAdjoint 0 (by simpa using hR)
  rw [commute_iff_eq, hR, hL]

/-- If every term `V.term r A` ($1 \le r \le L$, $A \in \mathrm{BoxCubes}\ D\ L\ r$) commutes with `sys.P0`,
    then `sys.H0 + V.V_tot` commutes with `sys.P0`. -/
lemma commute_H0_add_V_tot_P0_of_commute_terms {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (sys : IndexedCommutingProjectorHamiltonian D L Site ι)
    (V : QuasiLocalPerturbation D L Site)
    (h_comm : ∀ r ∈ Finset.Icc 1 L, ∀ A ∈ boxCubes D L r, Commute (V.term r A) sys.P0) :
    Commute (sys.H0 + V.totalPerturbation) sys.P0 := by
  refine sys.commute_H0_P0.add_left ?_
  dsimp [QuasiLocalPerturbation.totalPerturbation]
  exact Commute.sum_left _ _ _ (fun r hr => Commute.sum_left _ _ _ (fun A hA => h_comm r hr A hA))

end
