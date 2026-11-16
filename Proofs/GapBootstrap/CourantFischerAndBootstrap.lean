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
import Proofs.CubeTelescoping.ChromaticSubgridFormBound
import Proofs.GapBootstrap.CourantFischerTrialSubspace
import Proofs.LiebRobinson.SuperpolyDecayClosure

/-!
# Continuous Gap Bootstrap, Enclosing-Cube Multiplicities, and Superpolynomial Tail Sums

Proves the open-closed continuous spectral gap bootstrap on $[0, 1]$ (`continuous_gap_bootstrap_Icc_zero_one`), bounds enclosing-cube filter multiplicities against `H0` (`card_filter_enclosingBoxCube_le_pow`, `sum_filter_BoxCubes_two_le_pow_mul_re_inner_H0`), and establishes polynomial-weighted superpolynomial tail summability (`summable_two_mul_linearExpansionRadius_pow_mul`, `sum_tail_le_fTilde`).

## References

* Part I, Section 6.1 (`subsec:dsuper-banach`), Lemma 6.2 (`lem:dsuper-closure`)
* Part I, Section 7.1 (`subsec:single-cube-telescoping`), Proposition 7.2 (`prop:single-cube-telescoping`)
* Part I, Section 7.2 (`subsec:gap-bootstrap`), Theorem 7.3 (`thm:gap-bootstrap`)
* Bravyi, Hastings, and Michalakis (2010), J. Math. Phys. 51, 093512
* Bravyi and Hastings (2011), Commun. Math. Phys. 307, 609–627
-/

noncomputable section

open scoped Classical InnerProduct ComplexConjugate BigOperators
open Filter Topology Asymptotics ContinuousLinearMap

/-!
## 1. Continuous Open–Closed Spectral Gap Bootstrap on $s \in [0, 1]$
-/

/-- **Open–Closed Connectedness Gap Bootstrap on $[0, 1]$ (`continuous_gap_bootstrap_Icc_zero_one`)**:
    Let $\Delta : \mathbb{R} \to \mathbb{R}$ be a continuous function on $[0, 1]$ (such as the spectral gap
    $\mu_{d_{\mathrm{gs}}}(H(s)) - \mu_{d_{\mathrm{gs}}-1}(H(s))$) satisfying:
    1. Initial gap: $\Delta(0) \ge 1$;
    2. Conditional a priori boost: for every $s \in [0, 1]$, if $\Delta(\tau) \ge 1/2$ for all
       $\tau \in [0, s]$, then $\Delta(s) \ge 3/4 > 1/2$.
    Then $\Delta(s) \ge 3/4$ (and in particular $\Delta(s) \ge 1/2$) for all $s \in [0, 1]$. -/
theorem continuous_gap_bootstrap_Icc_zero_one
    (Δ : ℝ → ℝ)
    (h_cont : ContinuousOn Δ (Set.Icc 0 1))
    (h_zero : 1 ≤ Δ 0)
    (h_boost : ∀ s ∈ Set.Icc (0 : ℝ) 1,
      (∀ τ ∈ Set.Icc 0 s, bhmPerturbedGap ≤ Δ τ) → bhmBootstrapGap ≤ Δ s) :
    ∀ s ∈ Set.Icc (0 : ℝ) 1, bhmBootstrapGap ≤ Δ s := by
  have h_all : ∀ u ∈ Set.Icc (0 : ℝ) 1, bhmPerturbedGap ≤ Δ u := by
    by_contra h_not
    push_neg at h_not
    rcases h_not with ⟨u₁, hu₁_Icc, hu₁_lt⟩
    let B : Set ℝ := Set.Icc (0 : ℝ) 1 ∩ Δ ⁻¹' Set.Iic bhmPerturbedGap
    have hB_closed : IsClosed B :=
      h_cont.preimage_isClosed_of_isClosed isClosed_Icc isClosed_Iic
    have hB_ne : B.Nonempty := ⟨u₁, hu₁_Icc, le_of_lt hu₁_lt⟩
    have hB_bdd : BddBelow B := ⟨0, fun x hx => hx.1.1⟩
    set s_star := sInf B
    have hs_mem : s_star ∈ B := hB_closed.csInf_mem hB_ne hB_bdd
    have hs_Icc : s_star ∈ Set.Icc (0 : ℝ) 1 := hs_mem.1
    have hs_le : Δ s_star ≤ bhmPerturbedGap := hs_mem.2
    let m : ℝ := (bhmPerturbedGap + bhmBootstrapGap) / 2
    have hm_mem : m ∈ Set.Icc (Δ s_star) (Δ 0) := by
      dsimp [m, bhmPerturbedGap, bhmBootstrapGap] at *
      refine ⟨?_, ?_⟩ <;> linarith
    have h_ivt := intermediate_value_Icc' hs_Icc.1
      (h_cont.mono (Set.Icc_subset_Icc_right hs_Icc.2)) hm_mem
    rcases h_ivt with ⟨c, hc_Icc, hΔc⟩
    have hc_ne_s : c ≠ s_star := by
      intro h_eq
      rw [h_eq] at hΔc
      dsimp [m, bhmPerturbedGap, bhmBootstrapGap] at *
      linarith
    have hc_lt_s : c < s_star := lt_of_le_of_ne hc_Icc.2 hc_ne_s
    have hc_in_01 : c ∈ Set.Icc (0 : ℝ) 1 := ⟨hc_Icc.1, le_trans hc_Icc.2 hs_Icc.2⟩
    have hc_sub : ∀ u ∈ Set.Icc (0 : ℝ) c, bhmPerturbedGap ≤ Δ u := by
      intro u hu
      have hu_lt_s : u < s_star := lt_of_le_of_lt hu.2 hc_lt_s
      have hu_in_01 : u ∈ Set.Icc (0 : ℝ) 1 := ⟨hu.1, le_trans hu.2 hc_in_01.2⟩
      by_contra h_lt
      push_neg at h_lt
      have hu_mem_B : u ∈ B := ⟨hu_in_01, le_of_lt h_lt⟩
      have hs_le_u : s_star ≤ u := csInf_le hB_bdd hu_mem_B
      linarith
    have h_boot_c : bhmBootstrapGap ≤ Δ c := h_boost c hc_in_01 hc_sub
    dsimp [m, bhmPerturbedGap, bhmBootstrapGap] at *
    linarith
  intro s hs
  exact h_boost s hs (fun τ hτ => h_all τ ⟨hτ.1, le_trans hτ.2 hs.2⟩)

/-!
## 2. Enclosing Box-Cube Overlap Multiplicity and Scale-$r$ Relative Form Bounds
-/

/-- Membership in `boxCube x0 r` is equivalent to coordinate-wise bounds `(x0 i).val ≤ (x i).val < (x0 i).val + r`. -/
lemma mem_boxCube {D L : ℕ} {x x0 : BoxD D L} {r : ℕ} :
    x ∈ boxCube x0 r ↔ ∀ i : Fin D, (x0 i).val ≤ (x i).val ∧ (x i).val < (x0 i).val + r := by
  simp [boxCube]

/-- The anchor vertex $x_0$ belongs to $\mathrm{boxCube}(x_0, r)$ whenever $r > 0$. -/
lemma self_mem_boxCube {D L : ℕ} (x0 : BoxD D L) {r : ℕ} (hr : 0 < r) :
    x0 ∈ boxCube x0 r := by
  rw [mem_boxCube]
  exact fun i => ⟨le_rfl, Nat.lt_add_of_pos_right hr⟩

/-- For every cube $A \in \mathrm{BoxCubes}\ D\ L\ r$, $\mathrm{boxCube}(\mathrm{anchorOfCube}(r, A), r) = A$. -/
lemma boxCube_anchorOfCube {D L : ℕ} [NeZero L] {r : ℕ} {A : Finset (BoxD D L)}
    (hA : A ∈ boxCubes D L r) :
    boxCube (anchorOfCube r A) r = A := by
  dsimp [anchorOfCube]
  rw [dif_pos hA]
  exact (Finset.mem_image.mp hA).choose_spec.2

/-- Any elementary cube $K \in \mathrm{BoxCubes}\ D\ L\ 2$ is contained in at most $(2R)^D$ enclosing cubes
    $\mathrm{enclosingBoxCube}(\mathrm{anchorOfCube}(r, A), r, R)$ as $A$ ranges over $\mathrm{BoxCubes}\ D\ L\ r$. -/
lemma card_filter_enclosingBoxCube_le_pow {D L : ℕ} [NeZero D] [NeZero L]
    (r R : ℕ) {K : Finset (BoxD D L)} (hK : K ∈ boxCubes D L 2) :
    ((boxCubes D L r).filter (fun A => K ⊆ enclosingBoxCube (anchorOfCube r A) r R)).card ≤
      (2 * R) ^ D := by
  rcases Finset.mem_image.mp hK with ⟨y0, _, rfl⟩
  have hy0 : y0 ∈ boxCube y0 2 := self_mem_boxCube y0 (by decide)
  by_cases hR : R = 0
  · subst hR
    have h_empty :
        (boxCubes D L r).filter (fun A => boxCube y0 2 ⊆ enclosingBoxCube (anchorOfCube r A) r 0) = ∅ := by
      rw [Finset.filter_eq_empty_iff]
      intro A _ h_sub
      have hy0_mem := h_sub hy0
      rw [enclosingBoxCube, mem_boxCube] at hy0_mem
      have hi0 := hy0_mem ⟨0, NeZero.pos D⟩
      omega
    rw [h_empty, Finset.card_empty]
    exact Nat.zero_le _
  · have h2R_pos : 0 < 2 * R := by omega
    let d : ℕ := (R - r) / 2
    have hd_le_R : d ≤ R := by dsimp [d]; omega
    have hL_pos : 0 < L := NeZero.pos L
    let g : (Fin D → Fin (2 * R)) → Finset (BoxD D L) := fun k =>
      boxCube (fun i => ⟨min (L - 1) ((y0 i).val + d - (k i).val),
        Nat.lt_of_le_of_lt (Nat.min_le_left _ _) (Nat.sub_lt hL_pos zero_lt_one)⟩) r
    have h_sub :
        (boxCubes D L r).filter (fun A => boxCube y0 2 ⊆ enclosingBoxCube (anchorOfCube r A) r R) ⊆
          Finset.univ.image g := by
      intro A hA
      rcases Finset.mem_filter.mp hA with ⟨hA_mem, hK_sub⟩
      have hy0_encl : y0 ∈ enclosingBoxCube (anchorOfCube r A) r R := hK_sub hy0
      simp only [enclosingBoxCube, mem_boxCube] at hy0_encl
      let xA := anchorOfCube r A
      have hk_lt : ∀ i : Fin D, (y0 i).val + d - (xA i).val < 2 * R := by
        intro i
        have hi : (xA i).val - d ≤ (y0 i).val ∧ (y0 i).val < (xA i).val - d + R := hy0_encl i
        omega
      let k : Fin D → Fin (2 * R) := fun i => ⟨(y0 i).val + d - (xA i).val, hk_lt i⟩
      have h_anchor : (fun i : Fin D => (⟨min (L - 1) ((y0 i).val + d - (k i).val),
          Nat.lt_of_le_of_lt (Nat.min_le_left _ _) (Nat.sub_lt hL_pos zero_lt_one)⟩ : Fin L)) = xA := by
        funext i
        apply Fin.ext
        have hi : (xA i).val - d ≤ (y0 i).val ∧ (y0 i).val < (xA i).val - d + R := hy0_encl i
        have hxA_lt : (xA i).val < L := (xA i).isLt
        change min (L - 1) ((y0 i).val + d - ((y0 i).val + d - (xA i).val)) = (xA i).val
        omega
      rw [Finset.mem_image]
      refine ⟨k, Finset.mem_univ k, ?_⟩
      dsimp [g]
      rw [h_anchor, boxCube_anchorOfCube hA_mem]
    calc ((boxCubes D L r).filter (fun A => boxCube y0 2 ⊆ enclosingBoxCube (anchorOfCube r A) r R)).card
      _ ≤ (Finset.univ.image g).card := Finset.card_le_card h_sub
      _ ≤ (Finset.univ : Finset (Fin D → Fin (2 * R))).card := Finset.card_image_le
      _ = (2 * R) ^ D := by
        rw [Finset.card_univ, Fintype.card_fun, Fintype.card_fin, Fintype.card_fin]

/-- Double-sum counting bound: summing $\sum_{K \subseteq B(A, R)} \|Q_K \psi\|^2$ over all cubes
    $A \in \mathrm{BoxCubes}\ D\ L\ r$ is bounded by $(2 R)^D \, \mathrm{re}\langle \psi, H_0 \psi \rangle$. -/
lemma sum_filter_BoxCubes_two_le_pow_mul_re_inner_H0 {D L : ℕ} [NeZero D] [NeZero L]
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    (sys : CommutingProjectorHamiltonian D L Site)
    (r R : ℕ) (ψ : ManyBodyHilbertSpace Site) :
    ∑ A ∈ boxCubes D L r,
      ∑ K ∈ (boxCubes D L 2).filter (fun K => K ⊆ enclosingBoxCube (anchorOfCube r A) r R),
        ‖sys.Q K ψ‖ ^ 2 ≤
      (((2 * R : ℕ) : ℝ) ^ D) * RCLike.re (inner ℂ ψ (sys.H0 ψ)) := by
  let B : Finset (BoxD D L) → Finset (BoxD D L) :=
    fun A => enclosingBoxCube (anchorOfCube r A) r R
  have h_swap :
      ∑ A ∈ boxCubes D L r, ∑ K ∈ (boxCubes D L 2).filter (fun K => K ⊆ B A), ‖sys.Q K ψ‖ ^ 2 =
      ∑ K ∈ boxCubes D L 2,
        (((boxCubes D L r).filter (fun A => K ⊆ B A)).card : ℝ) * ‖sys.Q K ψ‖ ^ 2 := by
    simp_rw [Finset.sum_filter]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun K _ => ?_)
    rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
  rw [h_swap, sys.re_inner_H0_eq_sum_norm_sq ψ, Finset.mul_sum]
  refine Finset.sum_le_sum (fun K hK => ?_)
  apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
  exact_mod_cast card_filter_enclosingBoxCube_le_pow r R hK

/-- Linearity of $\mathrm{re}\langle \psi, (\sum_{i \in s} T_i) \psi \rangle$. -/
lemma re_inner_sum_apply {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    {ι : Type*} (s : Finset ι) (T : ι → (E →L[ℂ] E)) (ψ : E) :
    RCLike.re (inner ℂ ψ ((∑ i ∈ s, T i) ψ)) =
      ∑ i ∈ s, RCLike.re (inner ℂ ψ (T i ψ)) := by
  rw [ContinuousLinearMap.sum_apply, inner_sum, map_sum]

/-- Quadratic form of a real scalar multiple of the identity: $\mathrm{re}\langle \psi, (c \cdot I)\psi \rangle = c \|\psi\|^2$. -/
lemma re_inner_smul_one {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (c : ℝ) (ψ : E) :
    RCLike.re (inner ℂ ψ (((c : ℂ) • (1 : E →L[ℂ] E)) ψ)) = c * ‖ψ‖ ^ 2 := by
  have h : inner ℂ ψ (((c : ℂ) • (1 : E →L[ℂ] E)) ψ) = ((c * ‖ψ‖ ^ 2 : ℝ) : ℂ) := by
    rw [ContinuousLinearMap.smul_apply, ContinuousLinearMap.one_apply, inner_smul_right,
      inner_self_eq_norm_sq_to_K]
    push_cast
    rfl
  rw [h]
  rfl

/-- **Scale-$r$ Relative Form Bound (`scale_r_form_bound`)**: -/
lemma scale_r_form_bound {D L : ℕ} [NeZero D] [NeZero L]
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    (sys : CommutingProjectorHamiltonian D L Site)
    (V : QuasiLocalPerturbation D L Site)
    {L_star : ℕ} {C J : ℝ} {f : ℕ → ℝ}
    (hJ : 0 ≤ J) (hf_nonneg : ∀ r : ℕ, 0 ≤ f r)
    (hTQO1 : sys.SatisfiesTQO1 L_star)
    (hTQO2 : sys.SatisfiesLinearTQO2 L_star C)
    (hV_decay : V.SatisfiesDecayBound J f)
    {r : ℕ} (hr1 : 1 ≤ r) (hrL_star : r ≤ L_star) (hrL : r ≤ L)
    (h_comm : ∀ A ∈ boxCubes D L r, Commute (V.term r A) sys.P) :
    ∃ c_r : ℝ, ∀ ϕ : ManyBodyHilbertSpace Site,
      |RCLike.re (inner ℂ ϕ ((∑ A ∈ boxCubes D L r, V.term r A) ϕ)) - c_r * ‖ϕ‖ ^ 2| ≤
        (2 * J * (((2 * linearExpansionRadius C r : ℕ) : ℝ) ^ D) * f r) *
          RCLike.re (inner ℂ ϕ (sys.H0 ϕ)) := by
  have hr_mem : r ∈ Finset.Icc 1 L := Finset.mem_Icc.mpr ⟨hr1, hrL⟩
  let R := linearExpansionRadius C r
  have h_exists_A : ∀ A : Finset (BoxD D L),
      ∃ c_A : ℝ, A ∈ boxCubes D L r →
        ‖V.term r A - (c_A : ℂ) • (1 : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site)‖ ≤
          2 * (J * f r) ∧
        V.term r A = (c_A : ℂ) • (1 : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site) +
          (1 - sys.localGroundProj (enclosingBoxCube (anchorOfCube r A) r R)) *
            (V.term r A - (c_A : ℂ) • (1 : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site)) *
            (1 - sys.localGroundProj (enclosingBoxCube (anchorOfCube r A) r R)) := by
    intro A
    by_cases hA : A ∈ boxCubes D L r
    · have h_supp : IsSupportedOn Site (boxCube (anchorOfCube r A) r) (V.term r A) := by
        rw [boxCube_anchorOfCube hA]
        exact V.is_supported r hr_mem A hA
      rcases exists_local_sandwich_of_tqo_bhm sys hTQO1 hTQO2 hr1 hrL_star
        (anchorOfCube r A) (V.term r A) (V.is_selfAdjoint r A) h_supp (h_comm A hA) with
        ⟨c_A, _, hM_norm, h_eq⟩
      refine ⟨c_A, fun _ => ⟨?_, h_eq⟩⟩
      exact le_trans hM_norm (mul_le_mul_of_nonneg_left (hV_decay r hr_mem A hA) (by norm_num))
    · exact ⟨0, fun h => False.elim (hA h)⟩
  choose c_fn hc_fn using h_exists_A
  refine ⟨∑ A ∈ boxCubes D L r, c_fn A, fun ϕ => ?_⟩
  rw [re_inner_sum_apply, Finset.sum_mul, ← Finset.sum_sub_distrib]
  calc |∑ A ∈ boxCubes D L r, (RCLike.re (inner ℂ ϕ (V.term r A ϕ)) - c_fn A * ‖ϕ‖ ^ 2)|
    _ ≤ ∑ A ∈ boxCubes D L r, |RCLike.re (inner ℂ ϕ (V.term r A ϕ)) - c_fn A * ‖ϕ‖ ^ 2| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ A ∈ boxCubes D L r,
        (2 * (J * f r)) *
          ∑ K ∈ (boxCubes D L 2).filter (fun K => K ⊆ enclosingBoxCube (anchorOfCube r A) r R),
            ‖sys.Q K ϕ‖ ^ 2 := by
      refine Finset.sum_le_sum (fun A hA => ?_)
      rcases hc_fn A hA with ⟨hM_norm, h_decomp⟩
      let M_A := V.term r A - (c_fn A : ℂ) • (1 : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site)
      let B_A := enclosingBoxCube (anchorOfCube r A) r R
      have h_diff : RCLike.re (inner ℂ ϕ (V.term r A ϕ)) - c_fn A * ‖ϕ‖ ^ 2 =
          RCLike.re (inner ℂ ϕ (((1 - sys.localGroundProj B_A) * M_A * (1 - sys.localGroundProj B_A)) ϕ)) := by
        conv_lhs => rw [h_decomp]
        rw [ContinuousLinearMap.add_apply, inner_add_right, map_add, re_inner_smul_one]
        ring
      rw [h_diff]
      calc |RCLike.re (inner ℂ ϕ (((1 - sys.localGroundProj B_A) * M_A * (1 - sys.localGroundProj B_A)) ϕ))|
        _ ≤ ‖M_A‖ * ∑ K ∈ (boxCubes D L 2).filter (fun K => K ⊆ B_A), ‖sys.Q K ϕ‖ ^ 2 :=
          abs_re_inner_sandwich_one_sub_P_loc_le sys B_A M_A ϕ
        _ ≤ (2 * (J * f r)) * ∑ K ∈ (boxCubes D L 2).filter (fun K => K ⊆ B_A), ‖sys.Q K ϕ‖ ^ 2 := by
          apply mul_le_mul_of_nonneg_right hM_norm
          exact Finset.sum_nonneg (fun _ _ => sq_nonneg _)
    _ = (2 * (J * f r)) *
        ∑ A ∈ boxCubes D L r,
          ∑ K ∈ (boxCubes D L 2).filter (fun K => K ⊆ enclosingBoxCube (anchorOfCube r A) r R),
            ‖sys.Q K ϕ‖ ^ 2 := by
      rw [← Finset.mul_sum]
    _ ≤ (2 * (J * f r)) * ((((2 * R : ℕ) : ℝ) ^ D) * RCLike.re (inner ℂ ϕ (sys.H0 ϕ))) := by
      apply mul_le_mul_of_nonneg_left (sum_filter_BoxCubes_two_le_pow_mul_re_inner_H0 sys r R ϕ)
      exact mul_nonneg (by norm_num) (mul_nonneg hJ (hf_nonneg r))
    _ = (2 * J * (((2 * R : ℕ) : ℝ) ^ D) * f r) * RCLike.re (inner ℂ ϕ (sys.H0 ϕ)) := by ring

/-- High-scale ($r > L^*$) volume-weighted form bound on `BoxD D L`. -/
lemma tail_scale_r_form_bound {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    (V : QuasiLocalPerturbation D L Site)
    {J : ℝ} {f : ℕ → ℝ}
    (hJ : 0 ≤ J) (hf_nonneg : ∀ r : ℕ, 0 ≤ f r)
    (hV_decay : V.SatisfiesDecayBound J f)
    {r : ℕ} (hr : r ∈ Finset.Icc 1 L) (ϕ : ManyBodyHilbertSpace Site) :
    |RCLike.re (inner ℂ ϕ ((∑ A ∈ boxCubes D L r, V.term r A) ϕ))| ≤
      (J * ((L : ℝ) ^ D) * f r) * ‖ϕ‖ ^ 2 := by
  have h_card : ((boxCubes D L r).card : ℝ) ≤ (L : ℝ) ^ D := by
    have h1 : (boxCubes D L r).card ≤ (Finset.univ : Finset (BoxD D L)).card :=
      Finset.card_image_le
    have h2 : (Finset.univ : Finset (BoxD D L)).card = L ^ D := by
      rw [Finset.card_univ, Fintype.card_fun, Fintype.card_fin, Fintype.card_fin]
    rw [h2] at h1
    exact_mod_cast h1
  rw [re_inner_sum_apply]
  calc |∑ A ∈ boxCubes D L r, RCLike.re (inner ℂ ϕ (V.term r A ϕ))|
    _ ≤ ∑ A ∈ boxCubes D L r, |RCLike.re (inner ℂ ϕ (V.term r A ϕ))| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _A ∈ boxCubes D L r, (J * f r) * ‖ϕ‖ ^ 2 := by
      refine Finset.sum_le_sum (fun A hA => ?_)
      calc |RCLike.re (inner ℂ ϕ (V.term r A ϕ))|
        _ ≤ ‖V.term r A‖ * ‖ϕ‖ ^ 2 := abs_re_inner_le_opNorm_mul_norm_sq (V.term r A) ϕ
        _ ≤ (J * f r) * ‖ϕ‖ ^ 2 :=
          mul_le_mul_of_nonneg_right (hV_decay r hr A hA) (sq_nonneg _)
    _ = ((boxCubes D L r).card : ℝ) * ((J * f r) * ‖ϕ‖ ^ 2) := by
      rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ ((L : ℝ) ^ D) * ((J * f r) * ‖ϕ‖ ^ 2) := by
      apply mul_le_mul_of_nonneg_right h_card
      exact mul_nonneg (mul_nonneg hJ (hf_nonneg r)) (sq_nonneg _)
    _ = (J * ((L : ℝ) ^ D) * f r) * ‖ϕ‖ ^ 2 := by ring

/-- High-scale tail sum bound $\sum_{r = L^* + 1}^L f(r) \le \tilde{f}(L^*)$ for $C \ge 1$ and $L^* \ge 1$. -/
lemma sum_tail_le_fTilde (C : ℝ) (hC : 1 ≤ C)
    {f : ℕ → ℝ} (hf : IsSuperpolynomialDecay f)
    (L L_star : ℕ) (hL_star : 1 ≤ L_star) :
    ∑ r ∈ Finset.Icc (L_star + 1) L, f r ≤ fTilde C f L_star := by
  let g_tail : ℕ → ℝ := fun q =>
    if (q : ℝ) > ((L_star : ℝ) - 3) / (2 * C) - 3 then f q else 0
  have hf_sum : Summable f := summable_of_isSuperpolynomialDecay hf
  have hg_nonneg : ∀ q : ℕ, 0 ≤ g_tail q := fun q => by
    dsimp [g_tail]; split_ifs <;> [exact hf.1 q; exact le_rfl]
  have hg_le : ∀ q : ℕ, g_tail q ≤ f q := fun q => by
    dsimp [g_tail]; split_ifs <;> [exact le_rfl; exact hf.1 q]
  have hg_sum : Summable g_tail := Summable.of_nonneg_of_le hg_nonneg hg_le hf_sum
  have h_eq_on : ∀ r ∈ Finset.Icc (L_star + 1) L, f r = g_tail r := by
    intro r hr
    have hr_ge : L_star + 1 ≤ r := (Finset.mem_Icc.mp hr).1
    have hr_cast : (L_star : ℝ) + 1 ≤ (r : ℝ) := by exact_mod_cast hr_ge
    have h2C_pos : (0 : ℝ) < 2 * C := by linarith
    have hL_nonneg : (0 : ℝ) ≤ (L_star : ℝ) := Nat.cast_nonneg L_star
    have h_div_le : ((L_star : ℝ) - 3) / (2 * C) ≤ (L_star : ℝ) := by
      rw [div_le_iff₀ h2C_pos]; nlinarith
    have h_gt : (r : ℝ) > ((L_star : ℝ) - 3) / (2 * C) - 3 := by linarith
    dsimp [g_tail]; rw [if_pos h_gt]
  have h_sum_le : ∑ r ∈ Finset.Icc (L_star + 1) L, f r ≤ ∑' q : ℕ, g_tail q := by
    rw [Finset.sum_congr rfl h_eq_on]
    exact hg_sum.sum_le_tsum (Finset.Icc (L_star + 1) L) (fun q _ => hg_nonneg q)
  have h_tsum_nonneg : 0 ≤ ∑' q : ℕ, g_tail q := tsum_nonneg hg_nonneg
  have hL_ge_one : (1 : ℝ) ≤ (L_star : ℝ) := Nat.one_le_cast.mpr hL_star
  calc ∑ r ∈ Finset.Icc (L_star + 1) L, f r
    _ ≤ 1 * ∑' q : ℕ, g_tail q := by linarith
    _ ≤ (L_star : ℝ) * ∑' q : ℕ, g_tail q := mul_le_mul_of_nonneg_right hL_ge_one h_tsum_nonneg
    _ = fTilde C f L_star := rfl

/-- For $C \ge 1$ and $r \ge 1$, $\lceil C r \rceil \le (C + 1) r$. -/
lemma linearExpansionRadius_le_mul_bhm (C : ℝ) (hC : 1 ≤ C) {r : ℕ} (hr : 1 ≤ r) :
    (linearExpansionRadius C r : ℝ) ≤ (C + 1) * (r : ℝ) := by
  dsimp [linearExpansionRadius]
  have hCr_nonneg : 0 ≤ C * (r : ℝ) := mul_nonneg (by linarith) (Nat.cast_nonneg r)
  have h_ceil : (Nat.ceil (C * (r : ℝ)) : ℝ) < C * (r : ℝ) + 1 :=
    Nat.ceil_lt_add_one hCr_nonneg
  have hr_ge_one : (1 : ℝ) ≤ (r : ℝ) := Nat.one_le_cast.mpr hr
  linarith

/-- Summability of $((2 R_C(r))^D) f(r)$ for $f \in \mathcal{D}_{\mathrm{super}}$ and $C \ge 1$. -/
lemma summable_two_mul_linearExpansionRadius_pow_mul (D : ℕ) (C : ℝ) (hC : 1 ≤ C)
    {f : ℕ → ℝ} (hf : IsSuperpolynomialDecay f) :
    Summable (fun r : ℕ => (((2 * linearExpansionRadius C r : ℕ) : ℝ) ^ D) * f r) := by
  have h_base := (summable_pow_mul_of_isSuperpolynomialDecay hf D).mul_left ((2 * (C + 1)) ^ D)
  refine Summable.of_norm_bounded_eventually_nat h_base ?_
  filter_upwards [eventually_ge_atTop 1] with r hr
  have h_nonneg : 0 ≤ (((2 * linearExpansionRadius C r : ℕ) : ℝ) ^ D) * f r :=
    mul_nonneg (pow_nonneg (Nat.cast_nonneg _) D) (hf.1 r)
  rw [Real.norm_of_nonneg h_nonneg]
  have h_le : ((2 * linearExpansionRadius C r : ℕ) : ℝ) ≤ (2 * (C + 1)) * (r : ℝ) := by
    push_cast
    linarith [linearExpansionRadius_le_mul_bhm C hC hr]
  calc (((2 * linearExpansionRadius C r : ℕ) : ℝ) ^ D) * f r
    _ ≤ (((2 * (C + 1)) * (r : ℝ)) ^ D) * f r := by
      apply mul_le_mul_of_nonneg_right _ (hf.1 r)
      exact pow_le_pow_left₀ (Nat.cast_nonneg _) h_le D
    _ = (2 * (C + 1)) ^ D * ((r : ℝ) ^ D * f r) := by rw [mul_pow, mul_assoc]

/-- If $g \in \mathcal{D}_{\mathrm{super}}$ and $c^* > 0$, then $L \mapsto g(\lfloor c^* L \rfloor_+)$
    belongs to $\mathcal{D}_{\mathrm{super}}$. -/
lemma isSuperpolynomialDecay_floor_mul {g : ℕ → ℝ} (hg : IsSuperpolynomialDecay g)
    {c_star : ℝ} (hc : 0 < c_star) :
    IsSuperpolynomialDecay (fun L : ℕ => g ⌊c_star * (L : ℝ)⌋₊) := by
  have h_inv_pos : 0 < 1 / c_star := div_pos one_pos hc
  have h_eq : (fun L : ℕ => ⌊c_star * (L : ℝ)⌋₊) = (fun L : ℕ => ⌊(L : ℝ) / (1 / c_star)⌋₊) := by
    ext L; congr 1; rw [div_div_eq_mul_div, div_one, mul_comm]
  refine ⟨fun L => hg.1 ⌊c_star * (L : ℝ)⌋₊, fun n => ?_⟩
  have h_tendsto_atTop : Tendsto (fun L : ℕ => ⌊c_star * (L : ℝ)⌋₊) atTop atTop := by
    rw [h_eq]; exact tendsto_floor_div_const_atTop h_inv_pos
  have h_zero : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 0) := tendsto_const_nhds
  have h_comp : Tendsto (fun L : ℕ => ((⌊c_star * (L : ℝ)⌋₊ : ℕ) : ℝ) ^ n * g ⌊c_star * (L : ℝ)⌋₊)
      atTop (𝓝 0) := (hg.2 n).comp h_tendsto_atTop
  have h_upper : Tendsto
      (fun L : ℕ => (2 / c_star) ^ n * (((⌊c_star * (L : ℝ)⌋₊ : ℕ) : ℝ) ^ n * g ⌊c_star * (L : ℝ)⌋₊))
      atTop (𝓝 0) := by
    simpa [mul_zero] using h_comp.const_mul ((2 / c_star) ^ n)
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' h_zero h_upper
    (Eventually.of_forall (fun L =>
      mul_nonneg (pow_nonneg (Nat.cast_nonneg L) n) (hg.1 ⌊c_star * (L : ℝ)⌋₊))) ?_
  rw [Filter.eventually_atTop]
  refine ⟨⌈1 / c_star⌉₊, fun L hL => ?_⟩
  have h1_le : 1 / c_star ≤ (L : ℝ) := le_trans (Nat.le_ceil (1 / c_star)) (Nat.cast_le.mpr hL)
  have h_one_le_mul : ((1 : ℕ) : ℝ) ≤ c_star * (L : ℝ) := by
    rw [Nat.cast_one]
    have h_div := (div_le_iff₀ hc).mp h1_le
    linarith
  have hq_ge_one : (1 : ℝ) ≤ (⌊c_star * (L : ℝ)⌋₊ : ℝ) :=
    Nat.one_le_cast.mpr (Nat.le_floor h_one_le_mul)
  have h_lt : c_star * (L : ℝ) ≤ (⌊c_star * (L : ℝ)⌋₊ : ℝ) + 1 :=
    le_of_lt (Nat.lt_floor_add_one (c_star * (L : ℝ)))
  have hL_le : (L : ℝ) ≤ (2 / c_star) * (⌊c_star * (L : ℝ)⌋₊ : ℝ) := by
    rw [div_mul_eq_mul_div, le_div_iff₀ hc]
    linarith
  have h_pow : (L : ℝ) ^ n ≤ ((2 / c_star) * (⌊c_star * (L : ℝ)⌋₊ : ℝ)) ^ n :=
    pow_le_pow_left₀ (Nat.cast_nonneg L) hL_le n
  calc (L : ℝ) ^ n * g ⌊c_star * (L : ℝ)⌋₊
    _ ≤ ((2 / c_star) * (⌊c_star * (L : ℝ)⌋₊ : ℝ)) ^ n * g ⌊c_star * (L : ℝ)⌋₊ :=
      mul_le_mul_of_nonneg_right h_pow (hg.1 _)
    _ = (2 / c_star) ^ n * (((⌊c_star * (L : ℝ)⌋₊ : ℕ) : ℝ) ^ n * g ⌊c_star * (L : ℝ)⌋₊) := by
      rw [mul_pow, mul_assoc]

/-- Partition a sum over `Finset.Icc 1 L` at an intermediate cutoff $1 \le L^* \le L$. -/
lemma sum_Icc_split {M : Type*} [AddCommMonoid M] {L_star L : ℕ}
    (h1 : 1 ≤ L_star) (h2 : L_star ≤ L) (F : ℕ → M) :
    ∑ r ∈ Finset.Icc 1 L, F r =
      (∑ r ∈ Finset.Icc 1 L_star, F r) + (∑ r ∈ Finset.Icc (L_star + 1) L, F r) := by
  have h_union : Finset.Icc 1 L = Finset.Icc 1 L_star ∪ Finset.Icc (L_star + 1) L := by
    ext r; simp only [Finset.mem_Icc, Finset.mem_union]; omega
  have h_disj : Disjoint (Finset.Icc 1 L_star) (Finset.Icc (L_star + 1) L) := by
    rw [Finset.disjoint_left]; intro r hr1 hr2; simp only [Finset.mem_Icc] at hr1 hr2; omega
  rw [h_union, Finset.sum_union h_disj]
