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
import Proofs.SupportAndCondExpLemmas

open scoped Classical InnerProduct ComplexConjugate BigOperators
open Filter Topology Asymptotics ContinuousLinearMap KMSPinchedGibbs

noncomputable section

/-!
# Matrix-Unit Product Telescoping of Dressed Cube Commutators and Cube-Range KMS Dissipation Bounds

Formalizes Part II, Section 6.1, Lemma 6.1(ii)(a)–(b) (`lem:kms-fourth-root`), Section 6.3,
Theorem 6.4 (`thm:main-B`), and Part I, Section 7.3, Theorem 7.4 (`thm:zero-temp-dressed-memory`):
1. Matrix-unit product basis expansion and telescoping of `U_dress† M_W U_dress` across `u ∈ W`
   for any operator `M_W` supported on a cube `W ∈ boxCubes 3 L r` (`r + 2 * R_cut ≤ R_imm`),
   bounding `‖Pi_safe_dress * [M_W, O_dress] * Pi_safe_dress‖` via bare `R_imm`-cube immunity;
2. Closure in `IsSuperpolynomialDecay` of the cube-rescaled splitting envelope
   `fun n => max (9 * δ_0 n) (C_const * g_LR (Nat.sqrt n / Λ_scale ^ 2))`;
3. Bare and QAC-dressed KMS pre-Dirichlet form bounds (`kmsDissipativeForm`) and coherent drift
   bounds (`opKMSNorm H hH β (opCommutator H ...)`) for arbitrary `IsCubeRangeBath` families.

## References

* Part I, Section 7.3 (`subsec:zero-temp-dressed-memory`), Theorem 7.4 (`thm:zero-temp-dressed-memory`)
* Part II, Section 6.1 (`subsec:fourth-root-firewall`), Lemma 6.1(ii)(a)–(b) (`lem:kms-fourth-root`)
* Part II, Section 6.3 (`subsec:main-theorems`), Theorem 6.4 (`thm:main-B`), Theorem 6.5 (`thm:main-D`)
-/

private lemma card_boxCube_three_le {L : ℕ} [NeZero L] (u0 : Box3D L) (r : ℕ) :
    (boxCube u0 r).card ≤ r ^ 3 := by
  let f : {x // x ∈ boxCube u0 r} → (Fin 3 → Fin r) := fun x μ =>
    ⟨(x.1 μ).val - (u0 μ).val, by
      have hx := (Finset.mem_filter.mp x.2).2 μ
      omega⟩
  have hf_inj : Function.Injective f := by
    intro x y hxy
    apply Subtype.ext
    funext μ
    apply Fin.ext
    have hx := (Finset.mem_filter.mp x.2).2 μ
    have hy := (Finset.mem_filter.mp y.2).2 μ
    have hμ : (f x μ).val = (f y μ).val := congrArg Fin.val (congrFun hxy μ)
    dsimp [f] at hμ
    omega
  have hcard := Fintype.card_le_of_injective f hf_inj
  simpa [Fintype.card_coe] using hcard

private lemma exists_enclosing_boxCube_of_boxBall {L r R_cut R_imm : ℕ} [NeZero L]
    (hr_pos : 1 ≤ r) (hr_pad : r + 2 * R_cut ≤ R_imm)
    {W : Finset (Box3D L)} (hW : W ∈ boxCubes 3 L r) :
    ∃ r' ∈ Finset.Icc 1 (min R_imm L), ∃ Q ∈ boxCubes 3 L r',
      ∀ u ∈ W, boxBall u R_cut ⊆ Q := by
  rcases Finset.mem_image.mp hW with ⟨u0, _, rfl⟩
  have hL_pos : 0 < L := NeZero.pos L
  let r' : ℕ := min (r + 2 * R_cut) L
  let v0 : Box3D L := fun μ => ⟨(u0 μ).val - R_cut, Nat.sub_lt_of_lt (u0 μ).isLt⟩
  have hr'_mem : r' ∈ Finset.Icc 1 (min R_imm L) := by
    rw [Finset.mem_Icc]
    dsimp [r']
    omega
  refine ⟨r', hr'_mem, boxCube v0 r', Finset.mem_image_of_mem _ (Finset.mem_univ v0), ?_⟩
  intro u hu y hy
  rw [boxCube, Finset.mem_filter]
  refine ⟨Finset.mem_univ y, fun μ => ?_⟩
  have hu_μ := (Finset.mem_filter.mp hu).2 μ
  have hy_dist : boxDist u y ≤ R_cut := (Finset.mem_filter.mp hy).2
  have hy_μ : coordDist (u μ) (y μ) ≤ R_cut :=
    le_trans (Finset.le_sup (f := fun i : Fin 3 => coordDist (u i) (y i)) (Finset.mem_univ μ))
      hy_dist
  dsimp [coordDist, v0, r'] at hy_μ ⊢
  have hy_lt : (y μ).val < L := (y μ).isLt
  omega

private lemma unitary_opNorm_and_adj_le_one {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] [CompleteSpace E]
    (U : unitary (E →L[ℂ] E)) :
    ‖U.1‖ ≤ 1 ∧ ‖U.1†‖ ≤ 1 :=
  ⟨unitary_norm_le_one U, unitary_star_norm_le_one U⟩

private lemma unitary_conj_list_prod {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] [CompleteSpace E]
    (U : unitary (E →L[ℂ] E)) (l : List (E →L[ℂ] E)) :
    U.1† * l.prod * U.1 = (l.map (fun A => U.1† * A * U.1)).prod := by
  induction l with
  | nil =>
    rw [List.prod_nil, List.map_nil, List.prod_nil, mul_one]
    exact Unitary.coe_star_mul_self U
  | cons A tl ih =>
    rw [List.prod_cons, List.map_cons, List.prod_cons, ← ih]
    have h_uu : U.1 * U.1† = 1 := Unitary.coe_mul_star_self U
    calc U.1† * (A * tl.prod) * U.1
      _ = U.1† * A * 1 * tl.prod * U.1 := by simp only [mul_one, mul_assoc]
      _ = U.1† * A * (U.1 * U.1†) * tl.prod * U.1 := by rw [h_uu]
      _ = (U.1† * A * U.1) * (U.1† * tl.prod * U.1) := by simp only [mul_assoc]

private lemma norm_list_prod_le_one {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] [CompleteSpace E]
    (l : List (E →L[ℂ] E)) (hl : ∀ A ∈ l, ‖A‖ ≤ 1) :
    ‖l.prod‖ ≤ 1 := by
  induction l with
  | nil =>
    rw [List.prod_nil]
    exact ContinuousLinearMap.norm_id_le
  | cons A tl ih =>
    rw [List.prod_cons]
    have hA : ‖A‖ ≤ 1 := hl A List.mem_cons_self
    have htl : ‖tl.prod‖ ≤ 1 := ih (fun B hB => hl B (List.mem_cons_of_mem _ hB))
    calc ‖A * tl.prod‖
      _ ≤ ‖A‖ * ‖tl.prod‖ := norm_mul_le A tl.prod
      _ ≤ 1 * 1 := mul_le_mul hA htl (norm_nonneg _) zero_le_one
      _ = 1 := one_mul 1

private lemma norm_list_prod_sub_le {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] [CompleteSpace E] {α : Type*}
    (l : List α) (f g : α → (E →L[ℂ] E)) {ε : ℝ}
    (hf : ∀ a ∈ l, ‖f a‖ ≤ 1) (hg : ∀ a ∈ l, ‖g a‖ ≤ 1)
    (hdiff : ∀ a ∈ l, ‖f a - g a‖ ≤ ε) :
    ‖(l.map f).prod - (l.map g).prod‖ ≤ (l.length : ℝ) * ε := by
  induction l with
  | nil => simp
  | cons a tl ih =>
    rw [List.map_cons, List.map_cons, List.prod_cons, List.prod_cons, List.length_cons]
    set Pf := (tl.map f).prod
    set Pg := (tl.map g).prod
    have hPf : ‖Pf‖ ≤ 1 := norm_list_prod_le_one (tl.map f) (fun B hB => by
      rcases List.mem_map.mp hB with ⟨x, hx, rfl⟩
      exact hf x (List.mem_cons_of_mem _ hx))
    have hga : ‖g a‖ ≤ 1 := hg a List.mem_cons_self
    have hda : ‖f a - g a‖ ≤ ε := hdiff a List.mem_cons_self
    have hε_nn : 0 ≤ ε := le_trans (norm_nonneg _) hda
    have h_ih : ‖Pf - Pg‖ ≤ (tl.length : ℝ) * ε :=
      ih (fun x hx => hf x (List.mem_cons_of_mem _ hx))
         (fun x hx => hg x (List.mem_cons_of_mem _ hx))
         (fun x hx => hdiff x (List.mem_cons_of_mem _ hx))
    have h_split : f a * Pf - g a * Pg = (f a - g a) * Pf + g a * (Pf - Pg) := by
      rw [sub_mul, mul_sub]; abel
    rw [h_split]
    have h1 : ‖(f a - g a) * Pf‖ ≤ ε := by
      calc ‖(f a - g a) * Pf‖
        _ ≤ ‖f a - g a‖ * ‖Pf‖ := norm_mul_le _ _
        _ ≤ ε * 1 := mul_le_mul hda hPf (norm_nonneg _) hε_nn
        _ = ε := mul_one ε
    have h2 : ‖g a * (Pf - Pg)‖ ≤ (tl.length : ℝ) * ε := by
      calc ‖g a * (Pf - Pg)‖
        _ ≤ ‖g a‖ * ‖Pf - Pg‖ := norm_mul_le _ _
        _ ≤ 1 * ((tl.length : ℝ) * ε) :=
          mul_le_mul hga h_ih (norm_nonneg _) zero_le_one
        _ = (tl.length : ℝ) * ε := one_mul _
    calc ‖(f a - g a) * Pf + g a * (Pf - Pg)‖
      _ ≤ ‖(f a - g a) * Pf‖ + ‖g a * (Pf - Pg)‖ := norm_add_le _ _
      _ ≤ ε + (tl.length : ℝ) * ε := add_le_add h1 h2
      _ = ((tl.length + 1 : ℕ) : ℝ) * ε := by push_cast; ring

private lemma norm_dressed_safe_commutator_le_bare {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] [CompleteSpace E]
    (U : unitary (E →L[ℂ] E)) (Pi_s O_0 M : E →L[ℂ] E) :
    ‖(U.1 * Pi_s * U.1†) * (M * (U.1 * O_0 * U.1†) - (U.1 * O_0 * U.1†) * M) *
        (U.1 * Pi_s * U.1†)‖ ≤
      ‖Pi_s * ((U.1† * M * U.1) * O_0 - O_0 * (U.1† * M * U.1)) * Pi_s‖ := by
  have hu1 : U.1† * U.1 = 1 := Unitary.coe_star_mul_self U
  rcases unitary_opNorm_and_adj_le_one U with ⟨hU, hU_adj⟩
  have h_eq :
      (U.1 * Pi_s * U.1†) * (M * (U.1 * O_0 * U.1†) - (U.1 * O_0 * U.1†) * M) *
          (U.1 * Pi_s * U.1†) =
        U.1 * (Pi_s * ((U.1† * M * U.1) * O_0 - O_0 * (U.1† * M * U.1)) * Pi_s) * U.1† := by
    have ht1 :
        (U.1 * Pi_s * U.1†) * (M * (U.1 * O_0 * U.1†)) * (U.1 * Pi_s * U.1†) =
          U.1 * (Pi_s * ((U.1† * M * U.1) * O_0) * Pi_s) * U.1† := by
      calc (U.1 * Pi_s * U.1†) * (M * (U.1 * O_0 * U.1†)) * (U.1 * Pi_s * U.1†)
        _ = U.1 * Pi_s * U.1† * M * U.1 * O_0 * (U.1† * U.1) * Pi_s * U.1† := by
          simp only [mul_assoc]
        _ = U.1 * (Pi_s * ((U.1† * M * U.1) * O_0) * Pi_s) * U.1† := by
          rw [hu1, mul_one]; simp only [mul_assoc]
    have ht2 :
        (U.1 * Pi_s * U.1†) * ((U.1 * O_0 * U.1†) * M) * (U.1 * Pi_s * U.1†) =
          U.1 * (Pi_s * (O_0 * (U.1† * M * U.1)) * Pi_s) * U.1† := by
      calc (U.1 * Pi_s * U.1†) * ((U.1 * O_0 * U.1†) * M) * (U.1 * Pi_s * U.1†)
        _ = U.1 * Pi_s * (U.1† * U.1) * O_0 * U.1† * M * U.1 * Pi_s * U.1† := by
          simp only [mul_assoc]
        _ = U.1 * (Pi_s * (O_0 * (U.1† * M * U.1)) * Pi_s) * U.1† := by
          rw [hu1, mul_one]; simp only [mul_assoc]
    rw [mul_sub, sub_mul, ht1, ht2]
    rw [mul_sub Pi_s, sub_mul _ _ Pi_s, mul_sub U.1, sub_mul _ _ (U.1†)]
  rw [h_eq]
  set X := Pi_s * ((U.1† * M * U.1) * O_0 - O_0 * (U.1† * M * U.1)) * Pi_s
  calc ‖U.1 * X * U.1†‖
    _ ≤ ‖U.1 * X‖ * ‖U.1†‖ := norm_mul_le _ _
    _ ≤ (‖U.1‖ * ‖X‖) * ‖U.1†‖ := mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _)
    _ ≤ (1 * ‖X‖) * 1 := mul_le_mul (mul_le_mul_of_nonneg_right hU (norm_nonneg X))
        hU_adj (norm_nonneg _) (mul_nonneg zero_le_one (norm_nonneg X))
    _ = ‖X‖ := by ring

private def singleSiteMatrixUnitLoc {L : ℕ} {Site0 : Type} [Fintype Site0] [DecidableEq Site0]
    (u : Box3D L) (i j : Site0) :
    LocalHilbertSpace (UniformSite3D L Site0) {u} →L[ℂ]
      LocalHilbertSpace (UniformSite3D L Site0) {u} :=
  LinearMap.toContinuousLinearMap
    { toFun := fun ψ_u => WithLp.toLp 2 (fun ξ =>
        if ξ ⟨u, Finset.mem_singleton_self u⟩ = i then ψ_u.ofLp (fun _ => j) else 0)
      map_add' := fun ψ₁ ψ₂ => by
        ext ξ
        change (if ξ ⟨u, Finset.mem_singleton_self u⟩ = i then
            ψ₁.ofLp (fun _ => j) + ψ₂.ofLp (fun _ => j) else 0) =
          (if ξ ⟨u, Finset.mem_singleton_self u⟩ = i then ψ₁.ofLp (fun _ => j) else 0) +
          (if ξ ⟨u, Finset.mem_singleton_self u⟩ = i then ψ₂.ofLp (fun _ => j) else 0)
        split_ifs <;> ring
      map_smul' := fun c ψ => by
        ext ξ
        change (if ξ ⟨u, Finset.mem_singleton_self u⟩ = i then
            c * ψ.ofLp (fun _ => j) else 0) =
          c * (if ξ ⟨u, Finset.mem_singleton_self u⟩ = i then ψ.ofLp (fun _ => j) else 0)
        split_ifs <;> ring }

private def singleSiteMatrixUnit {L : ℕ} {Site0 : Type} [Fintype Site0] [DecidableEq Site0]
    (u : Box3D L) (i j : Site0) :
    ManyBodyHilbertSpace (UniformSite3D L Site0) →L[ℂ]
      ManyBodyHilbertSpace (UniformSite3D L Site0) :=
  cylinderOp (UniformSite3D L Site0) {u} (singleSiteMatrixUnitLoc u i j)

private lemma isSupportedOn_singleSiteMatrixUnit {L : ℕ} {Site0 : Type}
    [Fintype Site0] [DecidableEq Site0] (u : Box3D L) (i j : Site0) :
    IsSupportedOn (UniformSite3D L Site0) {u} (singleSiteMatrixUnit u i j) :=
  ⟨singleSiteMatrixUnitLoc u i j, rfl⟩

private lemma singleSiteMatrixUnit_apply_ofLp {L : ℕ} {Site0 : Type}
    [Fintype Site0] [DecidableEq Site0] (u : Box3D L) (i j : Site0)
    (ψ : ManyBodyHilbertSpace (UniformSite3D L Site0))
    (σ : ManyBodyConfig (UniformSite3D L Site0)) :
    (singleSiteMatrixUnit u i j ψ).ofLp σ =
      if σ u = i then ψ.ofLp (Function.update σ u j) else 0 := by
  change (if (restrictConfig ({u} : Finset (Box3D L)) σ) ⟨u, Finset.mem_singleton_self u⟩ = i then
      ψ.ofLp (spliceConfig ({u} : Finset (Box3D L)) (fun _ => j) σ) else 0) =
    if σ u = i then ψ.ofLp (Function.update σ u j) else 0
  have h_rest :
      (restrictConfig ({u} : Finset (Box3D L)) σ) ⟨u, Finset.mem_singleton_self u⟩ = σ u := rfl
  have h_spl :
      spliceConfig ({u} : Finset (Box3D L)) (fun _ => j) σ = Function.update σ u j := by
    ext x
    dsimp [spliceConfig]
    by_cases hx : x = u
    · subst hx; simp
    · simp [hx]
  rw [h_rest, h_spl]

private lemma norm_singleSiteMatrixUnit_le_one {L : ℕ} {Site0 : Type}
    [Fintype Site0] [DecidableEq Site0] (u : Box3D L) (i j : Site0) :
    ‖singleSiteMatrixUnit u i j‖ ≤ 1 := by
  let A : Finset (Box3D L) := {u}
  let α_i : LocalConfig (UniformSite3D L Site0) A := fun _ => i
  let α_j : LocalConfig (UniformSite3D L Site0) A := fun _ => j
  have h_upd : ∀ (α : LocalConfig (UniformSite3D L Site0) A)
      (γ : LocalConfig (UniformSite3D L Site0) (Finset.univ \ A)),
      Function.update (combineConfig A α γ) u j = combineConfig A α_j γ := by
    intro α γ
    ext x
    by_cases hx : x = u
    · subst hx; simp [combineConfig, A, α_j]
    · have hxA : x ∉ A := by simpa [A] using hx
      simp [combineConfig, hx, hxA]
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro ψ
  rw [one_mul]
  have h_lhs : ‖singleSiteMatrixUnit u i j ψ‖ ^ 2 =
      ∑ γ : LocalConfig (UniformSite3D L Site0) (Finset.univ \ A),
        ‖ψ.ofLp (combineConfig A α_j γ)‖ ^ 2 := by
    rw [PiLp.norm_sq_eq_of_L2, ← (_root_.configEquiv (Site := UniformSite3D L Site0) A).sum_comp,
      Fintype.sum_prod_type, Finset.sum_eq_single α_i]
    · refine Finset.sum_congr rfl fun γ _ => ?_
      dsimp [_root_.configEquiv]
      have h_eq_i : (combineConfig A α_i γ) u = i := by simp [combineConfig, A, α_i]
      rw [singleSiteMatrixUnit_apply_ofLp, h_upd α_i γ]
      simp only [h_eq_i, ↓reduceIte]
    · intro α _ hne
      refine Finset.sum_eq_zero fun γ _ => ?_
      dsimp [_root_.configEquiv]
      have hne_val : (combineConfig A α γ) u ≠ i := by
        intro hc
        apply hne
        ext ⟨x, hx⟩
        have hxu : x = u := Finset.mem_singleton.mp hx
        subst hxu
        simpa [combineConfig, A] using hc
      rw [singleSiteMatrixUnit_apply_ofLp]
      simp only [hne_val, ↓reduceIte, norm_zero, sq, zero_mul]
    · intro h_abs; exact False.elim (h_abs (Finset.mem_univ α_i))
  have h_rhs : ‖ψ‖ ^ 2 =
      ∑ α : LocalConfig (UniformSite3D L Site0) A,
        ∑ γ : LocalConfig (UniformSite3D L Site0) (Finset.univ \ A),
          ‖ψ.ofLp (combineConfig A α γ)‖ ^ 2 := by
    rw [PiLp.norm_sq_eq_of_L2, ← (_root_.configEquiv (Site := UniformSite3D L Site0) A).sum_comp,
      Fintype.sum_prod_type]
    rfl
  have h_le_sq : ‖singleSiteMatrixUnit u i j ψ‖ ^ 2 ≤ ‖ψ‖ ^ 2 := by
    rw [h_lhs, h_rhs]
    exact Finset.single_le_sum
      (f := fun α => ∑ γ : LocalConfig (UniformSite3D L Site0) (Finset.univ \ A),
        ‖ψ.ofLp (combineConfig A α γ)‖ ^ 2)
      (fun α _ => Finset.sum_nonneg fun _ _ => sq_nonneg _)
      (Finset.mem_univ α_j)
  nlinarith [norm_nonneg (singleSiteMatrixUnit u i j ψ), norm_nonneg ψ]

private def spliceList {L : ℕ} {Site0 : Type}
    {W : Finset (Box3D L)} (l : List {x // x ∈ W})
    (β : LocalConfig (UniformSite3D L Site0) W)
    (σ : ManyBodyConfig (UniformSite3D L Site0)) :
    ManyBodyConfig (UniformSite3D L Site0) :=
  match l with
  | [] => σ
  | u :: tl => Function.update (spliceList tl β σ) u.1 (β u)

private lemma spliceList_update_comm {L : ℕ} {Site0 : Type}
    {W : Finset (Box3D L)} (l : List {x // x ∈ W})
    (β : LocalConfig (UniformSite3D L Site0) W)
    (σ : ManyBodyConfig (UniformSite3D L Site0))
    (u : {x // x ∈ W}) (hu : u ∉ l) :
    spliceList l β (Function.update σ u.1 (β u)) =
      Function.update (spliceList l β σ) u.1 (β u) := by
  induction l with
  | nil => rfl
  | cons v tl ih =>
    have huv : u ≠ v := List.ne_of_not_mem_cons hu
    have hu_tl : u ∉ tl := List.not_mem_of_not_mem_cons hu
    have hvu_val : u.1 ≠ v.1 := fun h => huv (Subtype.ext h)
    dsimp [spliceList]
    rw [ih hu_tl, Function.update_comm hvu_val]

private lemma spliceList_apply_of_mem {L : ℕ} {Site0 : Type}
    {W : Finset (Box3D L)} (l : List {x // x ∈ W})
    (β : LocalConfig (UniformSite3D L Site0) W)
    (σ : ManyBodyConfig (UniformSite3D L Site0))
    (hl : l.Nodup) {u : {x // x ∈ W}} (hu : u ∈ l) :
    spliceList l β σ u.1 = β u := by
  induction l with
  | nil => cases hu
  | cons v tl ih =>
    rcases List.nodup_cons.mp hl with ⟨_, htl⟩
    dsimp [spliceList]
    by_cases huv : u = v
    · subst huv; simp
    · have hu_tl : u ∈ tl := (List.mem_cons.mp hu).resolve_left huv
      have hne_val : u.1 ≠ v.1 := fun h => huv (Subtype.ext h)
      rw [Function.update_of_ne hne_val, ih htl hu_tl]

private lemma spliceList_apply_of_not_mem {L : ℕ} {Site0 : Type}
    {W : Finset (Box3D L)} (l : List {x // x ∈ W})
    (β : LocalConfig (UniformSite3D L Site0) W)
    (σ : ManyBodyConfig (UniformSite3D L Site0))
    {x : Box3D L} (hx : ∀ u ∈ l, u.1 ≠ x) :
    spliceList l β σ x = σ x := by
  induction l with
  | nil => rfl
  | cons v tl ih =>
    dsimp [spliceList]
    have hxv : x ≠ v.1 := (hx v List.mem_cons_self).symm
    rw [Function.update_of_ne hxv, ih (fun u hu => hx u (List.mem_cons_of_mem _ hu))]

private lemma spliceList_attach_toList_eq {L : ℕ} {Site0 : Type}
    (W : Finset (Box3D L))
    (β : LocalConfig (UniformSite3D L Site0) W)
    (σ : ManyBodyConfig (UniformSite3D L Site0)) :
    spliceList W.attach.toList β σ = spliceConfig W β σ := by
  ext x
  dsimp [spliceConfig]
  split_ifs with hx
  · exact spliceList_apply_of_mem W.attach.toList β σ W.attach.nodup_toList
      (Finset.mem_toList.mpr (Finset.mem_attach W ⟨x, hx⟩))
  · exact spliceList_apply_of_not_mem W.attach.toList β σ (fun u _ h => hx (h ▸ u.2))

private lemma list_prod_singleSiteMatrixUnit_apply_ofLp {L : ℕ} {Site0 : Type}
    [Fintype Site0] [DecidableEq Site0]
    {W : Finset (Box3D L)} (l : List {x // x ∈ W}) (hl : l.Nodup)
    (α β : LocalConfig (UniformSite3D L Site0) W)
    (ψ : ManyBodyHilbertSpace (UniformSite3D L Site0))
    (σ : ManyBodyConfig (UniformSite3D L Site0)) :
    ((l.map (fun u => singleSiteMatrixUnit u.1 (α u) (β u))).prod ψ).ofLp σ =
      if ∀ u ∈ l, σ u.1 = α u then ψ.ofLp (spliceList l β σ) else 0 := by
  induction l generalizing σ with
  | nil =>
    simp [spliceList]
  | cons u tl ih =>
    rcases List.nodup_cons.mp hl with ⟨hu_not_mem, htl_nodup⟩
    rw [List.map_cons, List.prod_cons]
    change (singleSiteMatrixUnit u.1 (α u) (β u)
        ((tl.map (fun u => singleSiteMatrixUnit u.1 (α u) (β u))).prod ψ)).ofLp σ = _
    rw [singleSiteMatrixUnit_apply_ofLp, ih htl_nodup]
    have h_cond :
        (∀ v ∈ tl, (Function.update σ u.1 (β u)) v.1 = α v) ↔
          (∀ v ∈ tl, σ v.1 = α v) := by
      refine forall₂_congr fun v hv => ?_
      have hvu : v.1 ≠ u.1 := fun h => hu_not_mem (Subtype.ext h ▸ hv)
      rw [Function.update_of_ne hvu]
    have h_spl :
        spliceList tl β (Function.update σ u.1 (β u)) = spliceList (u :: tl) β σ :=
      spliceList_update_comm tl β σ u hu_not_mem
    rw [h_spl]
    have h_equiv :
        (σ u.1 = α u ∧ ∀ v ∈ tl, (Function.update σ u.1 (β u)) v.1 = α v) ↔
          ∀ v ∈ u :: tl, σ v.1 = α v := by
      rw [h_cond, List.forall_mem_cons]
    split_ifs <;> tauto

private def regionMatrixUnit {L : ℕ} {Site0 : Type} [Fintype Site0] [DecidableEq Site0]
    (W : Finset (Box3D L))
    (α β : LocalConfig (UniformSite3D L Site0) W) :
    ManyBodyHilbertSpace (UniformSite3D L Site0) →L[ℂ]
      ManyBodyHilbertSpace (UniformSite3D L Site0) :=
  (W.attach.toList.map (fun u => singleSiteMatrixUnit u.1 (α u) (β u))).prod

private lemma regionMatrixUnit_apply_ofLp {L : ℕ} {Site0 : Type}
    [Fintype Site0] [DecidableEq Site0]
    (W : Finset (Box3D L))
    (α β : LocalConfig (UniformSite3D L Site0) W)
    (ψ : ManyBodyHilbertSpace (UniformSite3D L Site0))
    (σ : ManyBodyConfig (UniformSite3D L Site0)) :
    (regionMatrixUnit W α β ψ).ofLp σ =
      if restrictConfig W σ = α then ψ.ofLp (spliceConfig W β σ) else 0 := by
  dsimp [regionMatrixUnit]
  rw [list_prod_singleSiteMatrixUnit_apply_ofLp W.attach.toList W.attach.nodup_toList α β ψ σ,
    spliceList_attach_toList_eq]
  have h_iff : (∀ u ∈ W.attach.toList, σ u.1 = α u) ↔ restrictConfig W σ = α := by
    constructor
    · intro h
      ext u
      exact h u (Finset.mem_toList.mpr (Finset.mem_attach W u))
    · intro h u _
      rw [← h]
      rfl
  split_ifs <;> tauto

private lemma clm_sum_apply_ofLp {L : ℕ} {Site0 : Type} [Fintype Site0] [DecidableEq Site0]
    {ι : Type*} (s : Finset ι)
    (F : ι → (ManyBodyHilbertSpace (UniformSite3D L Site0) →L[ℂ]
      ManyBodyHilbertSpace (UniformSite3D L Site0)))
    (ψ : ManyBodyHilbertSpace (UniformSite3D L Site0))
    (σ : ManyBodyConfig (UniformSite3D L Site0)) :
    ((∑ i ∈ s, F i) ψ).ofLp σ = ∑ i ∈ s, (F i ψ).ofLp σ := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha, add_apply]
    change (F a ψ).ofLp σ + ((∑ i ∈ s, F i) ψ).ofLp σ = _
    rw [ih]

private lemma cylinderOp_eq_sum_regionMatrixUnit {L : ℕ} {Site0 : Type}
    [Fintype Site0] [DecidableEq Site0]
    (W : Finset (Box3D L))
    (O_loc : LocalHilbertSpace (UniformSite3D L Site0) W →L[ℂ]
      LocalHilbertSpace (UniformSite3D L Site0) W) :
    cylinderOp (UniformSite3D L Site0) W O_loc =
      ∑ p : LocalConfig (UniformSite3D L Site0) W × LocalConfig (UniformSite3D L Site0) W,
        ((O_loc (_root_.deltaLp p.2)).ofLp p.1) • regionMatrixUnit W p.1 p.2 := by
  ext ψ σ
  have h_lhs :
      (cylinderOp (UniformSite3D L Site0) W O_loc ψ).ofLp σ =
        ∑ β : LocalConfig (UniformSite3D L Site0) W,
          ψ.ofLp (spliceConfig W β σ) * (O_loc (_root_.deltaLp β)).ofLp (restrictConfig W σ) := by
    change (O_loc (WithLp.toLp 2 (fun β : LocalConfig (UniformSite3D L Site0) W =>
        ψ.ofLp (spliceConfig W β σ)))).ofLp (restrictConfig W σ) = _
    exact _root_.clm_apply_ofLp_eq_sum O_loc _ (restrictConfig W σ)
  have h_rhs :
      ((∑ p : LocalConfig (UniformSite3D L Site0) W × LocalConfig (UniformSite3D L Site0) W,
          ((O_loc (_root_.deltaLp p.2)).ofLp p.1) • regionMatrixUnit W p.1 p.2) ψ).ofLp σ =
        ∑ β : LocalConfig (UniformSite3D L Site0) W,
          ψ.ofLp (spliceConfig W β σ) * (O_loc (_root_.deltaLp β)).ofLp (restrictConfig W σ) := by
    rw [clm_sum_apply_ofLp, Fintype.sum_prod_type, Finset.sum_eq_single (restrictConfig W σ)]
    · refine Finset.sum_congr rfl fun β _ => ?_
      change (O_loc (_root_.deltaLp β)).ofLp (restrictConfig W σ) *
          (regionMatrixUnit W (restrictConfig W σ) β ψ).ofLp σ =
        ψ.ofLp (spliceConfig W β σ) * (O_loc (_root_.deltaLp β)).ofLp (restrictConfig W σ)
      rw [regionMatrixUnit_apply_ofLp]
      simp only [↓reduceIte, mul_comm]
    · intro α _ hne
      refine Finset.sum_eq_zero fun β _ => ?_
      change (O_loc (_root_.deltaLp β)).ofLp α * (regionMatrixUnit W α β ψ).ofLp σ = 0
      rw [regionMatrixUnit_apply_ofLp]
      simp only [Ne.symm hne, ↓reduceIte, mul_zero]
    · intro h_abs
      exact False.elim (h_abs (Finset.mem_univ (restrictConfig W σ)))
  rw [h_lhs, h_rhs]

private lemma norm_matrixEntry_le_opNorm_cylinderOp {L : ℕ} {Site0 : Type}
    [Fintype Site0] [DecidableEq Site0] [Nonempty Site0]
    (W : Finset (Box3D L))
    (O_loc : LocalHilbertSpace (UniformSite3D L Site0) W →L[ℂ]
      LocalHilbertSpace (UniformSite3D L Site0) W)
    (α β : LocalConfig (UniformSite3D L Site0) W) :
    ‖(O_loc (_root_.deltaLp β)).ofLp α‖ ≤ ‖cylinderOp (UniformSite3D L Site0) W O_loc‖ := by
  let Site := UniformSite3D L Site0
  let γ₀ : LocalConfig Site (Finset.univ \ W) := fun _ => Classical.arbitrary Site0
  let σ₁ := combineConfig W β γ₀
  let σ₂ := combineConfig W α γ₀
  have h_entry :
      (O_loc (_root_.deltaLp β)).ofLp α =
        (cylinderOp Site W O_loc (basisVecGlobal Site σ₁)).ofLp σ₂ :=
    (partialTraceEntry_cylinderOp W O_loc γ₀ α β).symm
  have h_b_sq : ‖basisVecGlobal Site σ₁‖ ^ 2 = 1 := by
    rw [PiLp.norm_sq_eq_of_L2, Finset.sum_eq_single σ₁]
    · dsimp [basisVecGlobal]; simp
    · intro τ _ hne; dsimp [basisVecGlobal]; simp [hne]
    · intro h_abs; exact False.elim (h_abs (Finset.mem_univ σ₁))
  have h_b_norm : ‖basisVecGlobal Site σ₁‖ = 1 := by
    nlinarith [norm_nonneg (basisVecGlobal Site σ₁)]
  set v := cylinderOp Site W O_loc (basisVecGlobal Site σ₁)
  have h_coord_sq : ‖v.ofLp σ₂‖ ^ 2 ≤ ‖v‖ ^ 2 := by
    rw [PiLp.norm_sq_eq_of_L2]
    exact Finset.single_le_sum (f := fun τ => ‖v.ofLp τ‖ ^ 2)
      (fun _ _ => sq_nonneg _) (Finset.mem_univ σ₂)
  have h_coord : ‖v.ofLp σ₂‖ ≤ ‖v‖ := by
    nlinarith [norm_nonneg (v.ofLp σ₂), norm_nonneg v]
  rw [h_entry]
  calc ‖v.ofLp σ₂‖
    _ ≤ ‖v‖ := h_coord
    _ ≤ ‖cylinderOp Site W O_loc‖ * ‖basisVecGlobal Site σ₁‖ :=
      (cylinderOp Site W O_loc).le_opNorm _
    _ = ‖cylinderOp Site W O_loc‖ := by rw [h_b_norm, mul_one]

/-- **Matrix-Unit Product Telescoping for Dressed Cube Safe-Subspace Commutators
    (Part II, Lemma 6.1(ii)(b) (`lem:kms-fourth-root`))**:
    Let `U_dress` satisfy single-site quasi-locality at ball radius `R_cut` with error `g_LR_cut ≥ 0`,
    and let `(Pi_safe, O_0)` satisfy bare cube safe-subspace immunity up to side `R_imm`.
    Then for every cube `W ∈ boxCubes 3 L r` with `1 ≤ r ≤ min R_bath L` and `r + 2 * R_cut ≤ R_imm`
    and every `M_W` supported on `W`,
    `‖Pi_safe_dress * (M_W * O_dress - O_dress * M_W) * Pi_safe_dress‖ ≤ 2 * (r ^ 3 : ℝ) * ((Fintype.card Site0 ^ (2 * r ^ 3) : ℕ) : ℝ) * g_LR_cut * ‖M_W‖`. -/
theorem dressed_cube_safe_commutator_telescoping {L : ℕ} [NeZero L]
    {Site0 : Type} [Fintype Site0] [DecidableEq Site0] [Nonempty Site0]
    (U_dress : unitary (ManyBodyHilbertSpace (UniformSite3D L Site0) →L[ℂ]
      ManyBodyHilbertSpace (UniformSite3D L Site0)))
    (Pi_safe O_0 : ManyBodyHilbertSpace (UniformSite3D L Site0) →L[ℂ]
      ManyBodyHilbertSpace (UniformSite3D L Site0))
    {R_cut R_imm : ℕ} {g_LR_cut : ℝ}
    (hg_nonneg : 0 ≤ g_LR_cut)
    (hPi_norm : ‖Pi_safe‖ ≤ 1)
    (hO_norm : ‖O_0‖ ≤ 1)
    (hU_ql : ∀ (u : Box3D L)
      (A_u : ManyBodyHilbertSpace (UniformSite3D L Site0) →L[ℂ]
        ManyBodyHilbertSpace (UniformSite3D L Site0)),
      IsSupportedOn (UniformSite3D L Site0) {u} A_u →
      ‖U_dress.1† * A_u * U_dress.1 -
        condExp (UniformSite3D L Site0) (boxBall u R_cut) (U_dress.1† * A_u * U_dress.1)‖ ≤
          ‖A_u‖ * g_LR_cut)
    (h_imm : ∀ r' ∈ Finset.Icc 1 (min R_imm L), ∀ A ∈ boxCubes 3 L r',
      ∀ M_A : ManyBodyHilbertSpace (UniformSite3D L Site0) →L[ℂ]
        ManyBodyHilbertSpace (UniformSite3D L Site0),
        IsSupportedOn (UniformSite3D L Site0) A M_A →
        Pi_safe * (M_A * O_0 - O_0 * M_A) * Pi_safe = 0)
    {r : ℕ} (hr_pos : 1 ≤ r) (hr_le_L : r ≤ L) (hr_pad : r + 2 * R_cut ≤ R_imm)
    {W : Finset (Box3D L)} (hW : W ∈ boxCubes 3 L r)
    (M_W : ManyBodyHilbertSpace (UniformSite3D L Site0) →L[ℂ]
      ManyBodyHilbertSpace (UniformSite3D L Site0))
    (hM_supp : IsSupportedOn (UniformSite3D L Site0) W M_W) :
    let Pi_safe_dress := U_dress.1 * Pi_safe * U_dress.1†
    let O_dress := U_dress.1 * O_0 * U_dress.1†
    ‖Pi_safe_dress * (M_W * O_dress - O_dress * M_W) * Pi_safe_dress‖ ≤
      2 * ((r ^ 3 : ℕ) : ℝ) *
        (((Fintype.card Site0 ^ (2 * r ^ 3) : ℕ) : ℝ) * g_LR_cut) * ‖M_W‖ := by
  let _ := hr_le_L
  intro Pi_safe_dress O_dress
  let Site := UniformSite3D L Site0
  rcases hM_supp with ⟨O_loc, hM_eq⟩
  rcases unitary_opNorm_and_adj_le_one U_dress with ⟨hU_norm, hU_adj_norm⟩
  rcases exists_enclosing_boxCube_of_boxBall hr_pos hr_pad hW with
    ⟨r', hr'_mem, Q, hQ_mem, hQ_sub⟩
  have hW_card_le : W.card ≤ r ^ 3 := by
    rcases Finset.mem_image.mp hW with ⟨u0, _, rfl⟩
    exact card_boxCube_three_le u0 r
  let Idx := LocalConfig Site W × LocalConfig Site W
  let c : Idx → ℂ := fun p => (O_loc (_root_.deltaLp p.2)).ofLp p.1
  have hc_norm : ∀ p : Idx, ‖c p‖ ≤ ‖M_W‖ := by
    intro p
    rw [hM_eq]
    exact norm_matrixEntry_le_opNorm_cylinderOp W O_loc p.1 p.2
  let E_tilde : Idx → (ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site) :=
    fun p => U_dress.1† * regionMatrixUnit W p.1 p.2 * U_dress.1
  have h_pinch_p : ∀ p : Idx,
      ‖Pi_safe * (E_tilde p * O_0 - O_0 * E_tilde p) * Pi_safe‖ ≤
        2 * ((r ^ 3 : ℕ) : ℝ) * g_LR_cut := by
    intro p
    let f_p : {x // x ∈ W} → (ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site) :=
      fun u => U_dress.1† * singleSiteMatrixUnit u.1 (p.1 u) (p.2 u) * U_dress.1
    let g_p : {x // x ∈ W} → (ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site) :=
      fun u => condExp Site (boxBall u.1 R_cut) (f_p u)
    let B_p := (W.attach.toList.map g_p).prod
    have hE_eq : E_tilde p = (W.attach.toList.map f_p).prod := by
      dsimp [E_tilde, regionMatrixUnit]
      rw [unitary_conj_list_prod U_dress, List.map_map]
      rfl
    have hf_norm : ∀ u ∈ W.attach.toList, ‖f_p u‖ ≤ 1 := by
      intro u _
      dsimp [f_p]
      have h_single := norm_singleSiteMatrixUnit_le_one u.1 (p.1 u) (p.2 u)
      calc ‖U_dress.1† * singleSiteMatrixUnit u.1 (p.1 u) (p.2 u) * U_dress.1‖
        _ ≤ ‖U_dress.1† * singleSiteMatrixUnit u.1 (p.1 u) (p.2 u)‖ * ‖U_dress.1‖ :=
          norm_mul_le _ _
        _ ≤ (‖U_dress.1†‖ * ‖singleSiteMatrixUnit u.1 (p.1 u) (p.2 u)‖) * ‖U_dress.1‖ :=
          mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _)
        _ ≤ (1 * 1) * 1 := mul_le_mul
            (mul_le_mul hU_adj_norm h_single (norm_nonneg _) zero_le_one)
            hU_norm (norm_nonneg _) (by positivity)
        _ = 1 := by ring
    have hg_norm : ∀ u ∈ W.attach.toList, ‖g_p u‖ ≤ 1 := by
      intro u hu
      exact le_trans (norm_condExp_le _ _) (hf_norm u hu)
    have hfg_diff : ∀ u ∈ W.attach.toList, ‖f_p u - g_p u‖ ≤ g_LR_cut := by
      intro u _
      have h_ql := hU_ql u.1 (singleSiteMatrixUnit u.1 (p.1 u) (p.2 u))
        (isSupportedOn_singleSiteMatrixUnit u.1 (p.1 u) (p.2 u))
      have h_single := norm_singleSiteMatrixUnit_le_one u.1 (p.1 u) (p.2 u)
      calc ‖f_p u - g_p u‖
        _ ≤ ‖singleSiteMatrixUnit u.1 (p.1 u) (p.2 u)‖ * g_LR_cut := h_ql
        _ ≤ 1 * g_LR_cut := mul_le_mul_of_nonneg_right h_single hg_nonneg
        _ = g_LR_cut := one_mul g_LR_cut
    have h_tele : ‖E_tilde p - B_p‖ ≤ ((r ^ 3 : ℕ) : ℝ) * g_LR_cut := by
      rw [hE_eq]
      have h_len : W.attach.toList.length ≤ r ^ 3 := by
        simpa [Finset.length_toList, Finset.card_attach] using hW_card_le
      calc ‖(W.attach.toList.map f_p).prod - B_p‖
        _ ≤ (W.attach.toList.length : ℝ) * g_LR_cut :=
          norm_list_prod_sub_le W.attach.toList f_p g_p hf_norm hg_norm hfg_diff
        _ ≤ ((r ^ 3 : ℕ) : ℝ) * g_LR_cut :=
          mul_le_mul_of_nonneg_right (Nat.cast_le.mpr h_len) hg_nonneg
    have hB_supp : IsSupportedOn Site Q B_p := by
      apply _root_.isSupportedOn_list_prod Q
      intro A hA
      rcases List.mem_map.mp hA with ⟨u, _, rfl⟩
      exact _root_.isSupportedOn_mono (hQ_sub u.1 u.2) (isSupportedOn_condExp Site _ _)
    have hB_imm : Pi_safe * (B_p * O_0 - O_0 * B_p) * Pi_safe = 0 :=
      h_imm r' hr'_mem Q hQ_mem B_p hB_supp
    set D := E_tilde p - B_p
    have h_diff_id :
        Pi_safe * (E_tilde p * O_0 - O_0 * E_tilde p) * Pi_safe =
          Pi_safe * (D * O_0 - O_0 * D) * Pi_safe := by
      have h_alg :
          Pi_safe * (E_tilde p * O_0 - O_0 * E_tilde p) * Pi_safe -
            Pi_safe * (D * O_0 - O_0 * D) * Pi_safe =
            Pi_safe * (B_p * O_0 - O_0 * B_p) * Pi_safe := by
        dsimp [D]
        simp only [sub_mul, mul_sub]
        abel
      exact sub_eq_zero.mp (by rw [h_alg, hB_imm])
    rw [h_diff_id]
    have hcomm_D : ‖D * O_0 - O_0 * D‖ ≤ 2 * ‖D‖ :=
      norm_opCommutator_le_two_mul D hO_norm
    calc ‖Pi_safe * (D * O_0 - O_0 * D) * Pi_safe‖
      _ ≤ ‖Pi_safe * (D * O_0 - O_0 * D)‖ * ‖Pi_safe‖ := norm_mul_le _ _
      _ ≤ (‖Pi_safe‖ * ‖D * O_0 - O_0 * D‖) * ‖Pi_safe‖ :=
        mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _)
      _ ≤ (1 * (2 * ‖D‖)) * 1 := mul_le_mul
          (mul_le_mul hPi_norm hcomm_D (norm_nonneg _) zero_le_one)
          hPi_norm (norm_nonneg _) (by positivity)
      _ = 2 * ‖D‖ := by ring
      _ ≤ 2 * (((r ^ 3 : ℕ) : ℝ) * g_LR_cut) := by linarith
      _ = 2 * ((r ^ 3 : ℕ) : ℝ) * g_LR_cut := by ring
  have h_bare_expand :
      Pi_safe * ((U_dress.1† * M_W * U_dress.1) * O_0 -
          O_0 * (U_dress.1† * M_W * U_dress.1)) * Pi_safe =
        ∑ p : Idx, c p • (Pi_safe * (E_tilde p * O_0 - O_0 * E_tilde p) * Pi_safe) := by
    have h_mul_smul : ∀ (A B : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site) (z : ℂ),
        A * (z • B) = z • (A * B) := fun A B z => by ext ψ; simp
    have h_smul_mul : ∀ (A B : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site) (z : ℂ),
        (z • A) * B = z • (A * B) := fun A B z => by ext ψ; simp
    have hM_sum : M_W = ∑ p : Idx, c p • regionMatrixUnit W p.1 p.2 := by
      rw [hM_eq]
      exact cylinderOp_eq_sum_regionMatrixUnit W O_loc
    have hUMU : U_dress.1† * M_W * U_dress.1 = ∑ p : Idx, c p • E_tilde p := by
      rw [hM_sum, Finset.mul_sum, Finset.sum_mul]
      refine Finset.sum_congr rfl fun p _ => ?_
      dsimp [E_tilde]
      rw [h_mul_smul, h_smul_mul]
    rw [hUMU, Finset.sum_mul, Finset.mul_sum, ← Finset.sum_sub_distrib,
      Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [h_smul_mul, h_mul_smul, ← smul_sub, h_mul_smul, h_smul_mul]
  have h_card_idx : Fintype.card Idx ≤ Fintype.card Site0 ^ (2 * r ^ 3) := by
    have h1 : Fintype.card Idx = Fintype.card Site0 ^ (2 * W.card) := by
      dsimp [Idx, LocalConfig, Site, UniformSite3D]
      rw [Fintype.card_prod, Fintype.card_fun, Fintype.card_coe, ← pow_add, ← two_mul]
    rw [h1]
    exact Nat.pow_le_pow_right Fintype.card_pos (by omega)
  calc ‖Pi_safe_dress * (M_W * O_dress - O_dress * M_W) * Pi_safe_dress‖
    _ ≤ ‖Pi_safe * ((U_dress.1† * M_W * U_dress.1) * O_0 -
          O_0 * (U_dress.1† * M_W * U_dress.1)) * Pi_safe‖ :=
      norm_dressed_safe_commutator_le_bare U_dress Pi_safe O_0 M_W
    _ = ‖∑ p : Idx, c p • (Pi_safe * (E_tilde p * O_0 - O_0 * E_tilde p) * Pi_safe)‖ := by
      rw [h_bare_expand]
    _ ≤ ∑ p : Idx, ‖c p • (Pi_safe * (E_tilde p * O_0 - O_0 * E_tilde p) * Pi_safe)‖ :=
      norm_sum_le _ _
    _ ≤ ∑ _p : Idx, ‖M_W‖ * (2 * ((r ^ 3 : ℕ) : ℝ) * g_LR_cut) := by
      refine Finset.sum_le_sum fun p _ => ?_
      rw [norm_smul]
      exact mul_le_mul (hc_norm p) (h_pinch_p p) (norm_nonneg _) (norm_nonneg M_W)
    _ = (Fintype.card Idx : ℝ) * (‖M_W‖ * (2 * ((r ^ 3 : ℕ) : ℝ) * g_LR_cut)) := by
      rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    _ ≤ ((Fintype.card Site0 ^ (2 * r ^ 3) : ℕ) : ℝ) *
          (‖M_W‖ * (2 * ((r ^ 3 : ℕ) : ℝ) * g_LR_cut)) := by
      exact mul_le_mul_of_nonneg_right (Nat.cast_le.mpr h_card_idx) (by positivity)
    _ = 2 * ((r ^ 3 : ℕ) : ℝ) *
          (((Fintype.card Site0 ^ (2 * r ^ 3) : ℕ) : ℝ) * g_LR_cut) * ‖M_W‖ := by
      ring

private lemma isSuperpolynomialDecay_const_mul_aux {f : ℕ → ℝ} (hf : IsSuperpolynomialDecay f)
    {c : ℝ} (hc : 0 ≤ c) :
    IsSuperpolynomialDecay (fun r => c * f r) := by
  refine ⟨fun r => mul_nonneg hc (hf.1 r), fun n => ?_⟩
  have h_eq : (fun r : ℕ => (r : ℝ) ^ n * (c * f r)) =
      (fun r : ℕ => c * ((r : ℝ) ^ n * f r)) := by
    ext r; ring
  rw [h_eq]
  simpa [mul_zero] using (hf.2 n).const_mul c

private lemma isSuperpolynomialDecay_max_aux {f₁ f₂ : ℕ → ℝ}
    (hf₁ : IsSuperpolynomialDecay f₁) (hf₂ : IsSuperpolynomialDecay f₂) :
    IsSuperpolynomialDecay (fun r => max (f₁ r) (f₂ r)) := by
  refine ⟨fun r => le_trans (hf₁.1 r) (le_max_left _ _), fun n => ?_⟩
  have h_sum : Tendsto (fun r : ℕ => (r : ℝ) ^ n * f₁ r + (r : ℝ) ^ n * f₂ r) atTop (𝓝 0) := by
    simpa using (hf₁.2 n).add (hf₂.2 n)
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds h_sum
    (Eventually.of_forall fun r =>
      mul_nonneg (pow_nonneg (Nat.cast_nonneg r) n) (le_trans (hf₁.1 r) (le_max_left _ _))) ?_
  refine Eventually.of_forall fun r => ?_
  have h_le : max (f₁ r) (f₂ r) ≤ f₁ r + f₂ r :=
    max_le (le_add_of_nonneg_right (hf₂.1 r)) (le_add_of_nonneg_left (hf₁.1 r))
  calc (r : ℝ) ^ n * max (f₁ r) (f₂ r)
    _ ≤ (r : ℝ) ^ n * (f₁ r + f₂ r) :=
      mul_le_mul_of_nonneg_left h_le (pow_nonneg (Nat.cast_nonneg r) n)
    _ = (r : ℝ) ^ n * f₁ r + (r : ℝ) ^ n * f₂ r := mul_add _ _ _

private lemma one_add_le_pow4_add_one_mul_sq_sqrt_div {Λ_scale : ℕ} (hΛ : 1 ≤ Λ_scale) (n : ℕ) :
    1 + n ≤ (Λ_scale ^ 4 + 1) * (1 + Nat.sqrt n / (Λ_scale ^ 2)) ^ 2 := by
  have hΛ2_pos : 0 < Λ_scale ^ 2 := pow_pos (by omega) 2
  have h_div := Nat.div_add_mod (Nat.sqrt n) (Λ_scale ^ 2)
  have h_mod := Nat.mod_lt (Nat.sqrt n) hΛ2_pos
  have h_sqrt_le : Nat.sqrt n + 1 ≤ Λ_scale ^ 2 * (1 + Nat.sqrt n / (Λ_scale ^ 2)) := by
    nlinarith
  have h_lt_succ := Nat.lt_succ_sqrt n
  have h_n_le : 1 + n ≤ (Nat.sqrt n + 1) ^ 2 := by nlinarith
  have h_sq_le : (Nat.sqrt n + 1) ^ 2 ≤ (Λ_scale ^ 2 * (1 + Nat.sqrt n / (Λ_scale ^ 2))) ^ 2 :=
    Nat.pow_le_pow_left h_sqrt_le 2
  calc 1 + n
    _ ≤ (Λ_scale ^ 2 * (1 + Nat.sqrt n / (Λ_scale ^ 2))) ^ 2 := le_trans h_n_le h_sq_le
    _ = Λ_scale ^ 4 * (1 + Nat.sqrt n / (Λ_scale ^ 2)) ^ 2 := by ring
    _ ≤ (Λ_scale ^ 4 + 1) * (1 + Nat.sqrt n / (Λ_scale ^ 2)) ^ 2 :=
      Nat.mul_le_mul_right _ (Nat.le_succ _)

/-- **Superpolynomial Decay Closure of the Cube-Rescaled Splitting Envelope
    (Part II, Theorem 6.4 (`thm:main-B`) Proof)**:
    For `1 ≤ Λ_scale`, `0 ≤ C_const`, `IsSuperpolynomialDecay δ_0`, and `IsSuperpolynomialDecay g_LR`,
    the profile `fun n => max (9 * δ_0 n) (C_const * g_LR (Nat.sqrt n / (Λ_scale ^ 2)))` belongs to
    `IsSuperpolynomialDecay`, and at `n = Λ_scale ^ (2 * k + 4)` evaluates `Nat.sqrt n / Λ_scale ^ 2 = Λ_scale ^ k`. -/
theorem isSuperpolynomialDecay_cube_rescaled_profile
    {Λ_scale : ℕ} (hΛ : 1 ≤ Λ_scale)
    {C_const : ℝ} (hC : 0 ≤ C_const)
    {δ_0 g_LR : ℕ → ℝ}
    (hδ_0 : IsSuperpolynomialDecay δ_0)
    (hg_LR : IsSuperpolynomialDecay g_LR) :
    let δ_rescaled : ℕ → ℝ := fun n =>
      max (9 * δ_0 n) (C_const * g_LR (Nat.sqrt n / (Λ_scale ^ 2)))
    IsSuperpolynomialDecay δ_rescaled ∧
    (∀ k : ℕ, Nat.sqrt (Λ_scale ^ (2 * k + 4)) / (Λ_scale ^ 2) = Λ_scale ^ k) := by
  have hΛ2_pos : 0 < Λ_scale ^ 2 := pow_pos (by omega) 2
  let m : ℕ → ℕ := fun n => Nat.sqrt n / (Λ_scale ^ 2)
  have hm_tendsto : Tendsto m atTop atTop := by
    rw [Filter.tendsto_atTop_atTop]
    intro b
    refine ⟨(Λ_scale ^ 2 * b) * (Λ_scale ^ 2 * b), fun n hn => ?_⟩
    have h_sqrt : Λ_scale ^ 2 * b ≤ Nat.sqrt n := Nat.le_sqrt.mpr hn
    calc b
      _ = (Λ_scale ^ 2 * b) / (Λ_scale ^ 2) := (Nat.mul_div_right b hΛ2_pos).symm
      _ ≤ Nat.sqrt n / (Λ_scale ^ 2) := Nat.div_le_div_right h_sqrt
  have hg_rescaled : IsSuperpolynomialDecay (fun n => g_LR (m n)) := by
    refine ⟨fun n => hg_LR.1 (m n), fun p => ?_⟩
    have h_comp : Tendsto (fun n : ℕ => ((m n : ℕ) : ℝ) ^ (2 * p) * g_LR (m n)) atTop (𝓝 0) :=
      (hg_LR.2 (2 * p)).comp hm_tendsto
    let K : ℝ := (4 * ((Λ_scale ^ 4 + 1 : ℕ) : ℝ)) ^ p
    have h_upper : Tendsto (fun n : ℕ => K * (((m n : ℕ) : ℝ) ^ (2 * p) * g_LR (m n)))
        atTop (𝓝 0) := by
      simpa [mul_zero] using h_comp.const_mul K
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds h_upper
      (Eventually.of_forall fun n =>
        mul_nonneg (pow_nonneg (Nat.cast_nonneg n) p) (hg_LR.1 (m n))) ?_
    filter_upwards [Filter.eventually_ge_atTop (Λ_scale ^ 4)] with n hn
    have h_sq4 : (Λ_scale ^ 2) * (Λ_scale ^ 2) ≤ n := by
      have h_eq : (Λ_scale ^ 2) * (Λ_scale ^ 2) = Λ_scale ^ 4 := by ring
      omega
    have hm_pos : 1 ≤ m n := Nat.div_pos (Nat.le_sqrt.mpr h_sq4) hΛ2_pos
    have h_base_nat : n ≤ 4 * (Λ_scale ^ 4 + 1) * (m n) ^ 2 := by
      have h1 := one_add_le_pow4_add_one_mul_sq_sqrt_div hΛ n
      have h2 : (1 + m n) ^ 2 ≤ 4 * (m n) ^ 2 := by nlinarith
      have h3 : (Λ_scale ^ 4 + 1) * (1 + m n) ^ 2 ≤ (Λ_scale ^ 4 + 1) * (4 * (m n) ^ 2) :=
        Nat.mul_le_mul_left _ h2
      dsimp [m] at h3 ⊢
      nlinarith
    have h_base_real : (n : ℝ) ≤ (4 * ((Λ_scale ^ 4 + 1 : ℕ) : ℝ)) * ((m n : ℕ) : ℝ) ^ 2 := by
      have h_cast : (n : ℝ) ≤ ((4 * (Λ_scale ^ 4 + 1) * (m n) ^ 2 : ℕ) : ℝ) := by
        exact_mod_cast h_base_nat
      calc (n : ℝ)
        _ ≤ ((4 * (Λ_scale ^ 4 + 1) * (m n) ^ 2 : ℕ) : ℝ) := h_cast
        _ = (4 * ((Λ_scale ^ 4 + 1 : ℕ) : ℝ)) * ((m n : ℕ) : ℝ) ^ 2 := by push_cast; ring
    have h_pow : (n : ℝ) ^ p ≤ ((4 * ((Λ_scale ^ 4 + 1 : ℕ) : ℝ)) * ((m n : ℕ) : ℝ) ^ 2) ^ p :=
      pow_le_pow_left₀ (Nat.cast_nonneg n) h_base_real p
    calc (n : ℝ) ^ p * g_LR (m n)
      _ ≤ ((4 * ((Λ_scale ^ 4 + 1 : ℕ) : ℝ)) * ((m n : ℕ) : ℝ) ^ 2) ^ p * g_LR (m n) :=
        mul_le_mul_of_nonneg_right h_pow (hg_LR.1 (m n))
      _ = K * (((m n : ℕ) : ℝ) ^ (2 * p) * g_LR (m n)) := by
        dsimp [K]
        rw [mul_pow, ← pow_mul, mul_assoc]
  refine ⟨isSuperpolynomialDecay_max_aux
    (isSuperpolynomialDecay_const_mul_aux hδ_0 (by norm_num))
    (isSuperpolynomialDecay_const_mul_aux hg_rescaled hC), fun k => ?_⟩
  have h_pow_sq : Λ_scale ^ (2 * k + 4) = (Λ_scale ^ (k + 2)) * (Λ_scale ^ (k + 2)) := by ring
  rw [h_pow_sq, Nat.sqrt_eq, pow_add, Nat.mul_div_cancel _ hΛ2_pos]

private lemma gibbsFailureProb_one_sub_bounds {D L_box : ℕ}
    {Site : BoxD D L_box → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    [∀ x, Nonempty (Site x)]
    (H : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site)
    (hH : IsSelfAdjoint H) (β : ℝ)
    {P : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site}
    (hP : IsStarProjection P) :
    0 ≤ gibbsFailureProb H hH β P ∧ gibbsFailureProb H hH β P ≤ 1 := by
  let ψ_eig := opEigenbasis H hH
  let E_eig := opEigenvalues H hH
  have h_onb := opEigenbasis_orthonormal H hH
  have h_tr := hilbertTrace_eq_sum_opEigenbasis H hH
  have h_pars := opEigenbasis_parseval H hH
  refine ⟨hilbertTrace_gibbsDensityOp_mul_proj_nonneg ψ_eig E_eig β h_onb h_tr hP, ?_⟩
  dsimp [gibbsFailureProb]
  rw [hilbertTrace_gibbsDensityOp_mul_eq ψ_eig E_eig β h_onb h_tr P]
  calc ∑ ω : ManyBodyConfig Site, gibbsProb E_eig β ω * RCLike.re (inner ℂ (ψ_eig ω) (P (ψ_eig ω)))
    _ ≤ ∑ ω : ManyBodyConfig Site, gibbsProb E_eig β ω * 1 := by
      refine Finset.sum_le_sum fun ω _ => mul_le_mul_of_nonneg_left ?_ (gibbsProb_nonneg E_eig β ω)
      rw [isStarProjection_re_inner_eq_norm_sq hP (ψ_eig ω)]
      have h1 : ‖P (ψ_eig ω)‖ ^ 2 ≤ ‖ψ_eig ω‖ ^ 2 :=
        isStarProjection_norm_sq_apply_le hP (ψ_eig ω)
      rwa [eigenbasis_norm_eq_one ψ_eig h_onb h_pars ω, one_pow] at h1
    _ = ∑ ω : ManyBodyConfig Site, gibbsProb E_eig β ω := by simp only [mul_one]
    _ = 1 := sum_gibbsProb_eq_one E_eig β

private lemma opKMSNorm_three_block_safe_le {D L_box : ℕ}
    {Site : BoxD D L_box → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    [∀ x, Nonempty (Site x)]
    (H : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site)
    (hH : IsSelfAdjoint H) (β : ℝ)
    {Pi_s C : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site}
    (hPi : IsStarProjection Pi_s) :
    opKMSNorm H hH β C ≤
      ‖Pi_s * C * Pi_s‖ +
        2 * ‖C‖ * ((gibbsFailureProb H hH β (1 - Pi_s)) ^ (1 / 4 : ℝ)) := by
  let ψ_eig := opEigenbasis H hH
  let E_eig := opEigenvalues H hH
  let P_fail := 1 - Pi_s
  let p_act := gibbsFailureProb H hH β P_fail
  have h_onb := opEigenbasis_orthonormal H hH
  have h_tr := hilbertTrace_eq_sum_opEigenbasis H hH
  have h_pars := opEigenbasis_parseval H hH
  have hP_fail : IsStarProjection P_fail := hPi.one_sub
  have hp_act_nn : 0 ≤ p_act := (gibbsFailureProb_one_sub_bounds H hH β hP_fail).1
  have h1_proj : IsStarProjection (1 : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site) :=
    ⟨IsIdempotentElem.one, IsSelfAdjoint.one _⟩
  have h1_tr : hilbertTrace (gibbsDensityOp ψ_eig E_eig β * 1) ≤ 1 :=
    (gibbsFailureProb_one_sub_bounds H hH β h1_proj).2
  have h_term0 : kmsNorm ψ_eig E_eig β (Pi_s * C * Pi_s) ≤ ‖Pi_s * C * Pi_s‖ := by
    have hb := (kms_fourth_root_projector_bound ψ_eig E_eig β h_onb h_tr h_pars h1_proj
      (Pi_s * C * Pi_s) h1_tr).2.2.1
    rw [one_mul, Real.one_rpow, mul_one] at hb
    exact hb
  have h_term1 : kmsNorm ψ_eig E_eig β (P_fail * C) ≤ ‖C‖ * (p_act ^ (1 / 4 : ℝ)) :=
    (kms_fourth_root_projector_bound ψ_eig E_eig β h_onb h_tr h_pars hP_fail C le_rfl).2.2.1
  have hPi_C_norm : ‖Pi_s * C‖ ≤ ‖C‖ :=
    le_trans (ContinuousLinearMap.opNorm_comp_le Pi_s C)
      (mul_le_of_le_one_left (norm_nonneg C) (isStarProjection_norm_le_one hPi))
  have h_term2 : kmsNorm ψ_eig E_eig β (Pi_s * C * P_fail) ≤ ‖C‖ * (p_act ^ (1 / 4 : ℝ)) := by
    have hb := (kms_fourth_root_projector_bound ψ_eig E_eig β h_onb h_tr h_pars hP_fail
      (Pi_s * C) le_rfl).2.2.2
    exact le_trans hb (mul_le_mul_of_nonneg_right hPi_C_norm (Real.rpow_nonneg hp_act_nn _))
  have h_decomp : C = Pi_s * C * Pi_s + (P_fail * C + Pi_s * C * P_fail) := by
    dsimp [P_fail]
    rw [sub_mul, one_mul, mul_sub, mul_one]
    abel
  change kmsNorm ψ_eig E_eig β C ≤ ‖Pi_s * C * Pi_s‖ + 2 * ‖C‖ * (p_act ^ (1 / 4 : ℝ))
  have h_tri1 := kmsNorm_add_le ψ_eig E_eig β h_onb h_tr
    (Pi_s * C * Pi_s) (P_fail * C + Pi_s * C * P_fail)
  have h_tri2 := kmsNorm_add_le ψ_eig E_eig β h_onb h_tr (P_fail * C) (Pi_s * C * P_fail)
  have h_eq : kmsNorm ψ_eig E_eig β C =
      kmsNorm ψ_eig E_eig β (Pi_s * C * Pi_s + (P_fail * C + Pi_s * C * P_fail)) :=
    congrArg (kmsNorm ψ_eig E_eig β) h_decomp
  linarith

/-- **Bare-Frame Coherent Commutator and `IsCubeRangeBath` KMS Pre-Dirichlet Bounds
    (Part II, Lemma 6.1(ii)(a) (`lem:kms-fourth-root`))**:
    Without assuming `[H, Pi_safe] = 0`, if `gibbsFailureProb H hH β (1 - Pi_safe) ≤ p_fail` (`0 ≤ p_fail`)
    and `(Pi_safe, O_0)` satisfies bare cube safe-subspace immunity up to `R_imm`:
    1. When `Pi_safe * (H * O_0 - O_0 * H) * Pi_safe = 0`,
       `opKMSNorm H hH β (opCommutator H O_0) ≤ 2 * ‖H * O_0 - O_0 * H‖ * (p_fail ^ (1 / 4 : ℝ))`;
    2. For any `bath` with `IsCubeRangeBath D L_box R_imm bath`,
       `2 * kmsDissipativeForm H hH β (opKMSLindbladDissipator H hH β bath) O_0 O_0 ≤ 16 * (∑ ch ∈ bath, ch.γ * ‖ch.L‖ ^ 2) * (p_fail ^ (1 / 2 : ℝ))`. -/
theorem bare_cubeRangeBath_drift_and_dissipativeForm_le {D L_box : ℕ} [NeZero L_box]
    {Site : BoxD D L_box → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    [∀ x, Nonempty (Site x)]
    (H : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site)
    (hH : IsSelfAdjoint H) (β : ℝ)
    (Pi_safe O_0 : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site)
    (hPi : IsStarProjection Pi_safe) (hO_norm : ‖O_0‖ ≤ 1)
    {R_imm : ℕ} {p_fail : ℝ} (hp_nonneg : 0 ≤ p_fail)
    (hp_le : gibbsFailureProb H hH β (1 - Pi_safe) ≤ p_fail)
    (h_imm : ∀ r ∈ Finset.Icc 1 (min R_imm L_box), ∀ A ∈ boxCubes D L_box r,
      ∀ M_A : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site,
        IsSupportedOn Site A M_A →
        Pi_safe * (M_A * O_0 - O_0 * M_A) * Pi_safe = 0) :
    (Pi_safe * (H * O_0 - O_0 * H) * Pi_safe = 0 →
      opKMSNorm H hH β (opCommutator H O_0) ≤
        2 * ‖H * O_0 - O_0 * H‖ * (p_fail ^ (1 / 4 : ℝ))) ∧
    (∀ bath : Finset (BathChannel D L_box Site),
      IsCubeRangeBath D L_box R_imm bath →
      2 * kmsDissipativeForm H hH β (opKMSLindbladDissipator H hH β bath) O_0 O_0 ≤
        16 * (∑ ch ∈ bath, ch.γ * ‖ch.L‖ ^ 2) * (p_fail ^ (1 / 2 : ℝ))) := by
  have hp_act_nn : 0 ≤ gibbsFailureProb H hH β (1 - Pi_safe) :=
    (gibbsFailureProb_one_sub_bounds H hH β hPi.one_sub).1
  have h_rpow4 :
      (gibbsFailureProb H hH β (1 - Pi_safe)) ^ (1 / 4 : ℝ) ≤ p_fail ^ (1 / 4 : ℝ) :=
    Real.rpow_le_rpow hp_act_nn hp_le (by norm_num)
  refine ⟨fun hH_zero => ?_, fun bath h_bath => ?_⟩
  · have hb := opKMSNorm_three_block_safe_le H hH β hPi (C := opCommutator H O_0)
    dsimp [opCommutator] at hb ⊢
    rw [hH_zero, norm_zero, zero_add] at hb
    exact le_trans hb (mul_le_mul_of_nonneg_left h_rpow4 (by positivity))
  · rw [kmsDissipativeForm_opKMSLindbladDissipator_eq H hH β bath O_0 O_0]
    have h_onb := opEigenbasis_orthonormal H hH
    have h_tr := hilbertTrace_eq_sum_opEigenbasis H hH
    have h_rpow_sq : (p_fail ^ (1 / 4 : ℝ)) ^ 2 = p_fail ^ (1 / 2 : ℝ) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hp_nonneg]; norm_num
    have h_ch_bound : ∀ ch ∈ bath,
        ch.γ * kmsInnerReal (opEigenbasis H hH) (opEigenvalues H hH) β
          (opCommutator ch.L O_0) (opCommutator ch.L O_0) ≤
        ch.γ * (16 * ‖ch.L‖ ^ 2 * (p_fail ^ (1 / 2 : ℝ))) := by
      intro ch hch
      rcases h_bath ch hch with ⟨hγ_nn, r, hr_mem, W, hW_mem, _, hL_supp⟩
      have h_zero := h_imm r hr_mem W hW_mem ch.L hL_supp
      set C := opCommutator ch.L O_0
      have hb := opKMSNorm_three_block_safe_le H hH β hPi (C := C)
      have h_pinch0 : Pi_safe * C * Pi_safe = 0 := h_zero
      rw [h_pinch0, norm_zero, zero_add] at hb
      have hC_norm : ‖C‖ ≤ 2 * ‖ch.L‖ := norm_opCommutator_le_two_mul ch.L hO_norm
      have h_norm_le : opKMSNorm H hH β C ≤ 4 * ‖ch.L‖ * (p_fail ^ (1 / 4 : ℝ)) := by
        have h1 : 2 * ‖C‖ * ((gibbsFailureProb H hH β (1 - Pi_safe)) ^ (1 / 4 : ℝ)) ≤
            2 * (2 * ‖ch.L‖) * (p_fail ^ (1 / 4 : ℝ)) := by
          exact mul_le_mul (by linarith) h_rpow4 (Real.rpow_nonneg hp_act_nn _) (by positivity)
        linarith
      have h_sq_eq :
          kmsInnerReal (opEigenbasis H hH) (opEigenvalues H hH) β C C =
            (opKMSNorm H hH β C) ^ 2 :=
        (Real.sq_sqrt (kmsNormSq_nonneg (opEigenbasis H hH) (opEigenvalues H hH) β
          h_onb h_tr C)).symm
      have h_kms_nn : 0 ≤ opKMSNorm H hH β C := Real.sqrt_nonneg _
      have h_sq_le : (opKMSNorm H hH β C) ^ 2 ≤ 16 * ‖ch.L‖ ^ 2 * (p_fail ^ (1 / 2 : ℝ)) := by
        calc (opKMSNorm H hH β C) ^ 2
          _ ≤ (4 * ‖ch.L‖ * (p_fail ^ (1 / 4 : ℝ))) ^ 2 := by nlinarith
          _ = 16 * ‖ch.L‖ ^ 2 * ((p_fail ^ (1 / 4 : ℝ)) ^ 2) := by ring
          _ = 16 * ‖ch.L‖ ^ 2 * (p_fail ^ (1 / 2 : ℝ)) := by rw [h_rpow_sq]
      rw [h_sq_eq]
      exact mul_le_mul_of_nonneg_left h_sq_le hγ_nn
    calc ∑ ch ∈ bath, ch.γ *
          kmsInnerReal (opEigenbasis H hH) (opEigenvalues H hH) β
            (opCommutator ch.L O_0) (opCommutator ch.L O_0)
      _ ≤ ∑ ch ∈ bath, ch.γ * (16 * ‖ch.L‖ ^ 2 * (p_fail ^ (1 / 2 : ℝ))) :=
        Finset.sum_le_sum h_ch_bound
      _ = 16 * (∑ ch ∈ bath, ch.γ * ‖ch.L‖ ^ 2) * (p_fail ^ (1 / 2 : ℝ)) := by
        rw [Finset.mul_sum, Finset.sum_mul]
        refine Finset.sum_congr rfl fun ch _ => by ring

/-- **Dressed-Frame Coherent Commutator and `IsCubeRangeBath` KMS Pre-Dirichlet Bounds
    (Part II, Lemma 6.1(ii)(b) (`lem:kms-fourth-root`) and Theorem 6.4(ii) (`thm:main-B`))**:
    Suppose `IsStarProjection Pi_safe_dress`, `‖O_dress‖ ≤ 1`,
    `gibbsFailureProb H hH β (1 - Pi_safe_dress) ≤ p_log` (`0 ≤ p_log`),
    `‖Pi_safe_dress * (H * O_dress - O_dress * H) * Pi_safe_dress‖ ≤ δ_split`,
    and for every `r ∈ Finset.Icc 1 (min R_bath L_box)`, `W ∈ boxCubes D L_box r`, and `M_W` on `W`,
    `‖Pi_safe_dress * (M_W * O_dress - O_dress * M_W) * Pi_safe_dress‖ ≤ δ_ch' * ‖M_W‖`
    with `0 ≤ δ_ch'`, `δ_ch' ≤ 1`, and `9 * δ_ch' ≤ δ_split`. Then:
    1. `opKMSNorm H hH β (opCommutator H O_dress) ≤ 2 * ‖H * O_dress - O_dress * H‖ * (p_log ^ (1 / 4 : ℝ)) + δ_split`;
    2. For any `bath` with `IsCubeRangeBath D L_box R_bath bath`,
       `2 * kmsDissipativeForm H hH β (opKMSLindbladDissipator H hH β bath) O_dress O_dress ≤ (∑ ch ∈ bath, ch.γ * ‖ch.L‖ ^ 2) * (16 * (p_log ^ (1 / 2 : ℝ)) + δ_split)`. -/
theorem dressed_cubeRangeBath_drift_and_dissipativeForm_le {D L_box : ℕ} [NeZero L_box]
    {Site : BoxD D L_box → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    [∀ x, Nonempty (Site x)]
    (H : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site)
    (hH : IsSelfAdjoint H) (β : ℝ)
    (Pi_safe_dress O_dress : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site)
    (hPi : IsStarProjection Pi_safe_dress) (hO_norm : ‖O_dress‖ ≤ 1)
    {R_bath : ℕ} {p_log δ_ch' δ_split : ℝ}
    (hp_nonneg : 0 ≤ p_log)
    (hp_le : gibbsFailureProb H hH β (1 - Pi_safe_dress) ≤ p_log)
    (hH_comm_le : ‖Pi_safe_dress * (H * O_dress - O_dress * H) * Pi_safe_dress‖ ≤ δ_split)
    (hδ_nonneg : 0 ≤ δ_ch') (hδ_le_one : δ_ch' ≤ 1) (hδ_nine : 9 * δ_ch' ≤ δ_split)
    (h_cube_imm : ∀ r ∈ Finset.Icc 1 (min R_bath L_box), ∀ W ∈ boxCubes D L_box r,
      ∀ M_W : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site,
        IsSupportedOn Site W M_W →
        ‖Pi_safe_dress * (M_W * O_dress - O_dress * M_W) * Pi_safe_dress‖ ≤ δ_ch' * ‖M_W‖) :
    opKMSNorm H hH β (opCommutator H O_dress) ≤
      2 * ‖H * O_dress - O_dress * H‖ * (p_log ^ (1 / 4 : ℝ)) + δ_split ∧
    (∀ bath : Finset (BathChannel D L_box Site),
      IsCubeRangeBath D L_box R_bath bath →
      2 * kmsDissipativeForm H hH β (opKMSLindbladDissipator H hH β bath) O_dress O_dress ≤
        (∑ ch ∈ bath, ch.γ * ‖ch.L‖ ^ 2) * (16 * (p_log ^ (1 / 2 : ℝ)) + δ_split)) := by
  let _ := hp_nonneg
  let p_act := gibbsFailureProb H hH β (1 - Pi_safe_dress)
  rcases gibbsFailureProb_one_sub_bounds H hH β hPi.one_sub with ⟨hp_act_nn, hp_act_le_one⟩
  have h_rpow4_le : p_act ^ (1 / 4 : ℝ) ≤ p_log ^ (1 / 4 : ℝ) :=
    Real.rpow_le_rpow hp_act_nn hp_le (by norm_num)
  have h_rpow2_le : p_act ^ (1 / 2 : ℝ) ≤ p_log ^ (1 / 2 : ℝ) :=
    Real.rpow_le_rpow hp_act_nn hp_le (by norm_num)
  have h_rpow4_le_one : p_act ^ (1 / 4 : ℝ) ≤ 1 :=
    Real.rpow_le_one hp_act_nn hp_act_le_one (by norm_num)
  have h_rpow4_nn : 0 ≤ p_act ^ (1 / 4 : ℝ) := Real.rpow_nonneg hp_act_nn _
  have h_rpow4_sq : (p_act ^ (1 / 4 : ℝ)) ^ 2 = p_act ^ (1 / 2 : ℝ) := by
    dsimp [p_act]
    rw [← Real.rpow_natCast, ← Real.rpow_mul hp_act_nn]; norm_num
  refine ⟨?_, fun bath h_bath => ?_⟩
  · have hb := opKMSNorm_three_block_safe_le H hH β hPi (C := opCommutator H O_dress)
    dsimp [opCommutator] at hb ⊢
    have h_mul : 2 * ‖H * O_dress - O_dress * H‖ * (p_act ^ (1 / 4 : ℝ)) ≤
        2 * ‖H * O_dress - O_dress * H‖ * (p_log ^ (1 / 4 : ℝ)) :=
      mul_le_mul_of_nonneg_left h_rpow4_le (by positivity)
    linarith
  · rw [kmsDissipativeForm_opKMSLindbladDissipator_eq H hH β bath O_dress O_dress]
    have h_onb := opEigenbasis_orthonormal H hH
    have h_tr := hilbertTrace_eq_sum_opEigenbasis H hH
    have h_env_sq :
        (δ_ch' + 4 * (p_act ^ (1 / 4 : ℝ))) ^ 2 ≤
          16 * (p_log ^ (1 / 2 : ℝ)) + δ_split := by
      have h1 : δ_ch' ^ 2 ≤ δ_ch' := by nlinarith
      have h2 : 8 * δ_ch' * (p_act ^ (1 / 4 : ℝ)) ≤ 8 * δ_ch' := by nlinarith
      have h3 : (δ_ch' + 4 * (p_act ^ (1 / 4 : ℝ))) ^ 2 =
          δ_ch' ^ 2 + 8 * δ_ch' * (p_act ^ (1 / 4 : ℝ)) + 16 * ((p_act ^ (1 / 4 : ℝ)) ^ 2) := by
        ring
      rw [h3, h_rpow4_sq]
      linarith
    have h_ch_bound : ∀ ch ∈ bath,
        ch.γ * kmsInnerReal (opEigenbasis H hH) (opEigenvalues H hH) β
          (opCommutator ch.L O_dress) (opCommutator ch.L O_dress) ≤
        (ch.γ * ‖ch.L‖ ^ 2) * (16 * (p_log ^ (1 / 2 : ℝ)) + δ_split) := by
      intro ch hch
      rcases h_bath ch hch with ⟨hγ_nn, r, hr_mem, W, hW_mem, _, hL_supp⟩
      have h_pinch := h_cube_imm r hr_mem W hW_mem ch.L hL_supp
      set C := opCommutator ch.L O_dress
      have hb := opKMSNorm_three_block_safe_le H hH β hPi (C := C)
      have hC_norm : ‖C‖ ≤ 2 * ‖ch.L‖ := norm_opCommutator_le_two_mul ch.L hO_norm
      have h_norm_le : opKMSNorm H hH β C ≤ ‖ch.L‖ * (δ_ch' + 4 * (p_act ^ (1 / 4 : ℝ))) := by
        have h_mul : 2 * ‖C‖ * (p_act ^ (1 / 4 : ℝ)) ≤ 4 * ‖ch.L‖ * (p_act ^ (1 / 4 : ℝ)) :=
          mul_le_mul_of_nonneg_right (by linarith) h_rpow4_nn
        have h_pinch' : ‖Pi_safe_dress * C * Pi_safe_dress‖ ≤ δ_ch' * ‖ch.L‖ := h_pinch
        linarith
      have h_sq_eq :
          kmsInnerReal (opEigenbasis H hH) (opEigenvalues H hH) β C C =
            (opKMSNorm H hH β C) ^ 2 :=
        (Real.sq_sqrt (kmsNormSq_nonneg (opEigenbasis H hH) (opEigenvalues H hH) β
          h_onb h_tr C)).symm
      have h_kms_nn : 0 ≤ opKMSNorm H hH β C := Real.sqrt_nonneg _
      have h_rhs_nn : 0 ≤ ‖ch.L‖ * (δ_ch' + 4 * (p_act ^ (1 / 4 : ℝ))) := by positivity
      have h_sq_le :
          (opKMSNorm H hH β C) ^ 2 ≤
            ‖ch.L‖ ^ 2 * (16 * (p_log ^ (1 / 2 : ℝ)) + δ_split) := by
        calc (opKMSNorm H hH β C) ^ 2
          _ ≤ (‖ch.L‖ * (δ_ch' + 4 * (p_act ^ (1 / 4 : ℝ)))) ^ 2 := by nlinarith
          _ = ‖ch.L‖ ^ 2 * (δ_ch' + 4 * (p_act ^ (1 / 4 : ℝ))) ^ 2 := by ring
          _ ≤ ‖ch.L‖ ^ 2 * (16 * (p_log ^ (1 / 2 : ℝ)) + δ_split) :=
            mul_le_mul_of_nonneg_left h_env_sq (sq_nonneg _)
      rw [h_sq_eq, mul_assoc]
      exact mul_le_mul_of_nonneg_left h_sq_le hγ_nn
    calc ∑ ch ∈ bath, ch.γ *
          kmsInnerReal (opEigenbasis H hH) (opEigenvalues H hH) β
            (opCommutator ch.L O_dress) (opCommutator ch.L O_dress)
      _ ≤ ∑ ch ∈ bath, (ch.γ * ‖ch.L‖ ^ 2) * (16 * (p_log ^ (1 / 2 : ℝ)) + δ_split) :=
        Finset.sum_le_sum h_ch_bound
      _ = (∑ ch ∈ bath, ch.γ * ‖ch.L‖ ^ 2) * (16 * (p_log ^ (1 / 2 : ℝ)) + δ_split) :=
        (Finset.sum_mul _ _ _).symm

end
