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

import Proofs.KatoHastingsFlow.CanonicalQACFlowPackage

noncomputable section

open scoped Classical InnerProduct ComplexConjugate BigOperators
open Filter Topology Asymptotics ContinuousLinearMap MeasureTheory

/-!
# Interpolated Lattice Hamiltonians and Bare Bochner Tail Bounds

Transfers compact-support light-cone bounds through Bochner integrals, embeds the interpolated Hamiltonian $H_0 + s V_{\mathrm{tot}}$ as `interpolatedLatticeHamiltonian`, and proves Hastings–Koma bare-frame conditional expectation tail bounds (`barePerturbationTailProfile`) for filtered site perturbations.

## References

* Part I, Section 6.2 (`subsec:bochner-lr`), Equation (70) (`eq:hastings-koma-lr`), Proposition 6.3 (`prop:bochner-time-convolution`), Equations (71)–(72) (`eq:bochner-bare-V-tail`, `eq:bochner-bare-Q-tail`)
* Hastings–Koma (2006), Communications in Mathematical Physics 265, 781–804
-/

/-!
## 1. Compact-Support Bochner Conditional-Expectation Tail Transfer
-/

/-- **Compact-Support Bochner `condExp` Tail Transfer (`norm_bochnerFilteredOp_sub_condExp_le_of_compact_support`)**:
    If $w : \mathbb{R} \to \mathbb{C}$ is supported on $[-T, T]$ (`∀ t, T < |t| → w t = 0`) and
    $\|\tau_t^{H'}(O) - \mathbb{E}_B(\tau_t^{H'}(O))\| \le \varepsilon$ for all $t \in [-T, T]$, then
    $$\|\mathcal{F}_w^{H'}(O) - \mathbb{E}_B(\mathcal{F}_w^{H'}(O))\|
      \le \left(\int_{-\infty}^\infty \|w(t)\|\,dt\right) \varepsilon.$$ -/
theorem norm_bochnerFilteredOp_sub_condExp_le_of_compact_support {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    (H' : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site)
    (w : ℝ → ℂ)
    (O : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site)
    (B : Finset (BoxD D L)) {T ε : ℝ} (hε : 0 ≤ ε)
    (hw_int : Integrable w MeasureTheory.volume)
    (h_flow_int : Integrable (fun t : ℝ => w t • heisenbergFlow H' t O) MeasureTheory.volume)
    (hw_supp : ∀ t : ℝ, T < |t| → w t = 0)
    (h_pt : ∀ t ∈ Set.Icc (-T) T,
      ‖heisenbergFlow H' t O - condExp Site B (heisenbergFlow H' t O)‖ ≤ ε) :
    ‖bochnerFilteredOp H' w O - condExp Site B (bochnerFilteredOp H' w O)‖ ≤
      (∫ t : ℝ, ‖w t‖) * ε := by
  let Ψ : (ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site) →L[ℂ]
      (ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site) :=
    ContinuousLinearMap.id ℂ _ - condExpCLM Site B
  have hΨ_apply : ∀ X : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site,
      Ψ X = X - condExp Site B X := fun _ => rfl
  have hΨ_bochner :
      bochnerFilteredOp H' w O - condExp Site B (bochnerFilteredOp H' w O) =
        ∫ t : ℝ, w t • Ψ (heisenbergFlow H' t O) := by
    rw [← hΨ_apply (bochnerFilteredOp H' w O)]
    exact clm_apply_bochnerFilteredOp H' w O Ψ h_flow_int
  have hΨ_int : Integrable (fun t : ℝ => w t • Ψ (heisenbergFlow H' t O)) MeasureTheory.volume := by
    have h1 := Ψ.integrable_comp h_flow_int
    have h2 : (fun t : ℝ => Ψ (w t • heisenbergFlow H' t O)) =
        (fun t : ℝ => w t • Ψ (heisenbergFlow H' t O)) := by
      funext t
      exact map_smul Ψ (w t) (heisenbergFlow H' t O)
    rwa [h2] at h1
  rw [hΨ_bochner]
  calc ‖∫ t : ℝ, w t • Ψ (heisenbergFlow H' t O)‖
    _ ≤ ∫ t : ℝ, ‖w t • Ψ (heisenbergFlow H' t O)‖ := norm_integral_le_integral_norm _
    _ ≤ ∫ t : ℝ, ‖w t‖ * ε := by
      apply integral_mono hΨ_int.norm (hw_int.norm.mul_const ε)
      intro t
      dsimp only
      rw [norm_smul]
      by_cases ht : |t| ≤ T
      · rw [hΨ_apply]
        exact mul_le_mul_of_nonneg_left (h_pt t (abs_le.mp ht)) (norm_nonneg (w t))
      · push_neg at ht
        rw [hw_supp t ht, norm_zero, zero_mul, zero_mul]
    _ = (∫ t : ℝ, ‖w t‖) * ε := integral_mul_const ε (fun t => ‖w t‖)

/-- **Compact-Support `condExp` Transfer for `bhFilterWeight` (`norm_bochnerFilteredOp_w_BH11_sub_condExp_le_of_Icc_pi`)**:
    If $\|\tau_t^{H'}(O) - \mathbb{E}_B(\tau_t^{H'}(O))\| \le \varepsilon$ for all $t \in [-\pi, \pi]$, then
    $$\|\mathrm{bochnerFilteredOp}\ H'\ w_{\mathrm{BH11}}\ O -
      \mathbb{E}_B(\mathrm{bochnerFilteredOp}\ H'\ w_{\mathrm{BH11}}\ O)\| \le \varepsilon.$$ -/
theorem norm_bochnerFilteredOp_w_BH11_sub_condExp_le_of_Icc_pi {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    (H' : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site)
    (O : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site)
    (B : Finset (BoxD D L)) {ε : ℝ} (hε : 0 ≤ ε)
    (h_pt : ∀ t ∈ Set.Icc (-Real.pi) Real.pi,
      ‖heisenbergFlow H' t O - condExp Site B (heisenbergFlow H' t O)‖ ≤ ε) :
    ‖bochnerFilteredOp H' bhFilterWeight O - condExp Site B (bochnerFilteredOp H' bhFilterWeight O)‖ ≤ ε := by
  have h1 := norm_bochnerFilteredOp_sub_condExp_le_of_compact_support H' bhFilterWeight O B hε
    integrable_w_BH11 (integrable_w_BH11_smul_heisenbergFlow H' O)
    (fun _ ht => w_BH11_eq_zero_of_abs_gt_pi ht) h_pt
  rwa [integral_norm_w_BH11_eq_one, one_mul] at h1

/-!
## 2. Explicit `LatticeHamiltonian` Representation of $H(s) = H_0 + s V_{\mathrm{tot}}$ & Hastings–Koma Light-Cone Bound
-/

/-- Local interaction term of `sys.H0` supported on a subset $Z \subseteq \mathrm{BoxD}\ D\ L$. -/
def unperturbedLatticeTerm {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (sys : IndexedCommutingProjectorHamiltonian D L Site ι) (Z : Finset (BoxD D L)) :
    ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site :=
  ∑ i ∈ Finset.univ.filter (fun i : ι => sys.support i = Z),
    (sys.weight i : ℂ) • sys.checkProj i

/-- Local interaction term of $(s : \mathbb{C}) \bullet V.V_{\mathrm{tot}}$ supported on $Z \subseteq \mathrm{BoxD}\ D\ L$. -/
def perturbationLatticeTerm {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    (V : QuasiLocalPerturbation D L Site) (s : ℝ) (Z : Finset (BoxD D L)) :
    ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site :=
  ∑ r ∈ Finset.Icc 1 L, if Z ∈ boxCubes D L r then (s : ℂ) • V.term r Z else 0

/-- **Explicit `LatticeHamiltonian` Representation of $H(s) = H_0 + s V_{\mathrm{tot}}$ (`interpolatedLatticeHamiltonian`)**:
    Packages $H(s) = \mathrm{sys.H0} + (s : \mathbb{C}) \bullet V.V_{\mathrm{tot}}$ as a genuine
    `LatticeHamiltonian D L Site` for direct use in `hastings_koma_lieb_robinson_box`. -/
def interpolatedLatticeHamiltonian {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (sys : IndexedCommutingProjectorHamiltonian D L Site ι)
    (V : QuasiLocalPerturbation D L Site) (s : ℝ) :
    LatticeHamiltonian D L Site where
  h Z := unperturbedLatticeTerm sys Z + perturbationLatticeTerm V s Z
  is_selfAdjoint Z := by
    refine isSelfAdjoint_add_clm ?_ ?_
    · exact isSelfAdjoint_finset_sum _ _ (fun i _ =>
        isSelfAdjoint_real_smul (sys.weight i) (sys.is_projector i).isSelfAdjoint)
    · refine isSelfAdjoint_finset_sum _ _ (fun r _ => ?_)
      split_ifs
      · exact isSelfAdjoint_real_smul s (V.is_selfAdjoint r Z)
      · exact IsSelfAdjoint.zero _
  is_supported Z := by
    refine isSupportedOn_add Z ?_ ?_
    · refine isSupportedOn_finset_sum Z _ _ (fun i hi => ?_)
      rw [← (Finset.mem_filter.mp hi).2]
      exact isSupportedOn_smul (sys.support i) (sys.weight i : ℂ) (sys.is_supported i)
    · refine isSupportedOn_finset_sum Z _ _ (fun r hr => ?_)
      split_ifs with hZ
      · exact isSupportedOn_smul Z (s : ℂ) (V.is_supported r hr Z hZ)
      · exact isSupportedOn_zero Z

/-- Exact global Hamiltonian identity `(interpolatedLatticeHamiltonian sys V s).H_tot = interpolatedHamiltonianOp sys V s`. -/
theorem interpolatedLatticeHamiltonian_H_tot {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (sys : IndexedCommutingProjectorHamiltonian D L Site ι)
    (V : QuasiLocalPerturbation D L Site) (s : ℝ) :
    (interpolatedLatticeHamiltonian sys V s).totalHamiltonian = interpolatedHamiltonianOp sys V s := by
  unfold LatticeHamiltonian.totalHamiltonian interpolatedLatticeHamiltonian interpolatedHamiltonianOp
  dsimp only
  rw [Finset.sum_add_distrib]
  have hH0 : (∑ Z : Finset (BoxD D L), unperturbedLatticeTerm sys Z) = sys.H0 := by
    unfold unperturbedLatticeTerm IndexedCommutingProjectorHamiltonian.H0
    exact Finset.sum_fiberwise_of_maps_to (fun i _ => Finset.mem_univ (sys.support i))
      (fun i => (sys.weight i : ℂ) • sys.checkProj i)
  have hV : (∑ Z : Finset (BoxD D L), perturbationLatticeTerm V s Z) = (s : ℂ) • V.totalPerturbation := by
    unfold perturbationLatticeTerm QuasiLocalPerturbation.totalPerturbation
    rw [Finset.sum_comm, Finset.smul_sum]
    refine Finset.sum_congr rfl (fun r _ => ?_)
    rw [← Finset.sum_filter, Finset.smul_sum]
    refine Finset.sum_congr ?_ (fun _ _ => rfl)
    ext Z
    simp
  rw [hH0, hV]

/-- At $s = 1$, `(interpolatedLatticeHamiltonian sys V 1).H_tot = sys.H0 + V.V_tot`. -/
theorem interpolatedLatticeHamiltonian_one_H_tot {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (sys : IndexedCommutingProjectorHamiltonian D L Site ι)
    (V : QuasiLocalPerturbation D L Site) :
    (interpolatedLatticeHamiltonian sys V 1).totalHamiltonian = sys.H0 + V.totalPerturbation := by
  rw [interpolatedLatticeHamiltonian_H_tot, interpolatedHamiltonianOp, Complex.ofReal_one, one_smul]

/-- Any cylinder operator supported on the empty region `∅` is a scalar multiple of the identity. -/
lemma isSupportedOn_empty_eq_smul_one {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    {Y : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site}
    (hY : IsSupportedOn Site ∅ Y) :
    ∃ c : ℂ, Y = c • 1 := by
  rcases hY with ⟨O_loc, rfl⟩
  let α0 : LocalConfig Site ∅ := fun x => False.elim (Finset.notMem_empty x.1 x.2)
  have h_uniq : ∀ α : LocalConfig Site ∅, α = α0 :=
    fun α => funext (fun x => False.elim (Finset.notMem_empty x.1 x.2))
  let ones : LocalHilbertSpace Site ∅ := WithLp.toLp 2 (fun _ => (1 : ℂ))
  refine ⟨(O_loc ones).ofLp α0, ?_⟩
  ext ψ σ
  have h_slice : WithLp.toLp 2 (fun α : LocalConfig Site ∅ => ψ.ofLp (spliceConfig ∅ α σ)) =
      ψ.ofLp σ • ones := by
    ext α
    change ψ.ofLp (spliceConfig ∅ α σ) = ψ.ofLp σ * 1
    have h_sp : spliceConfig ∅ α σ = σ := by funext x; simp [spliceConfig]
    rw [h_sp, mul_one]
  change (O_loc (WithLp.toLp 2 (fun α : LocalConfig Site ∅ => ψ.ofLp (spliceConfig ∅ α σ)))).ofLp
      (restrictConfig ∅ σ) =
    (O_loc ones).ofLp α0 * ψ.ofLp σ
  rw [h_slice, map_smul, h_uniq (restrictConfig ∅ σ)]
  change ψ.ofLp σ * (O_loc ones).ofLp α0 = (O_loc ones).ofLp α0 * ψ.ofLp σ
  ring

/-- **Hastings–Koma Light-Cone `condExp` Tail Bound (`norm_heisenbergFlow_sub_condExp_le_hastings_koma`)**:
    For any `H : LatticeHamiltonian D L Site`, exponent $\eta \ge 0$, time horizon $T \ge 0$,
    observable $O_X$ supported on a nonempty region $X \subseteq \mathrm{BoxD}\ D\ L$, and target region
    $B \subseteq \mathrm{BoxD}\ D\ L$ such that $\Lambda_L \setminus B = \emptyset$ or
    $\mathrm{regionDist}(X, \Lambda_L \setminus B) \ge d > 0$, for all $t \in [-T, T]$:
    $$\|\tau_t^{H.H_{\mathrm{tot}}}(O_X) - \mathbb{E}_B(\tau_t^{H.H_{\mathrm{tot}}}(O_X))\|
      \le 2 \|O_X\| |X| \frac{\exp(2 H.s_1(\eta) T) - 1}{(1 + d / 2)^\eta}.$$ -/
theorem norm_heisenbergFlow_sub_condExp_le_hastings_koma
    {D L : ℕ} [NeZero D] [NeZero L]
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    [∀ x, Nonempty (Site x)]
    (H : LatticeHamiltonian D L Site) {η T : ℝ} (hη : 0 ≤ η) (hT : 0 ≤ T)
    {X B : Finset (BoxD D L)} (hX : X.Nonempty)
    {d : ℕ} (hd_pos : 0 < d)
    (h_dist : (Finset.univ \ B).Nonempty → d ≤ regionDist X (Finset.univ \ B))
    (O_X : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site)
    (hO_X : IsSupportedOn Site X O_X)
    {t : ℝ} (ht : t ∈ Set.Icc (-T) T) :
    ‖heisenbergFlow H.totalHamiltonian t O_X - condExp Site B (heisenbergFlow H.totalHamiltonian t O_X)‖ ≤
      2 * ‖O_X‖ * (X.card : ℝ) *
        ((Real.exp (2 * H.s1 η * T) - 1) / (1 + (d : ℝ) / 2) ^ η) := by
  have hs1_nn : 0 ≤ H.s1 η := by
    unfold LatticeHamiltonian.s1
    have x0 : BoxD D L := fun _ => ⟨0, NeZero.pos L⟩
    have h0 : 0 ≤ ∑ Z ∈ Finset.univ.filter (fun Z : Finset (BoxD D L) => x0 ∈ Z),
        ‖H.h Z‖ * (Z.card : ℝ) * (1 + (regionDiam Z : ℝ)) ^ η :=
      Finset.sum_nonneg (fun Z _ => by positivity)
    exact le_trans h0 (Finset.le_sup' (f := fun x => ∑ Z ∈ Finset.univ.filter (fun Z => x ∈ Z),
      ‖H.h Z‖ * (Z.card : ℝ) * (1 + (regionDiam Z : ℝ)) ^ η) (Finset.mem_univ x0))
  set ε : ℝ := 2 * ‖O_X‖ * (X.card : ℝ) *
    ((Real.exp (2 * H.s1 η * T) - 1) / (1 + (d : ℝ) / 2) ^ η)
  have hexp_ge : 1 ≤ Real.exp (2 * H.s1 η * T) := Real.one_le_exp (by positivity)
  have hε_nn : 0 ≤ ε := by
    dsimp [ε]
    exact mul_nonneg (by positivity)
      (div_nonneg (by linarith) (le_of_lt (Real.rpow_pos_of_pos (by positivity) η)))
  by_cases hBc : (Finset.univ \ B).Nonempty
  · apply norm_heisenbergFlow_sub_condExp_le_of_lieb_robinson H B O_X t hε_nn
    intro Y hY
    have hd_le : d ≤ regionDist X (Finset.univ \ B) := h_dist hBc
    have h_dist_ne : regionDist X (Finset.univ \ B) ≠ 0 := by omega
    have h_lr := hastings_koma_lieb_robinson_box H η hη X (Finset.univ \ B) hX hBc
      O_X Y hO_X hY t
    rw [if_neg h_dist_ne, mul_zero, add_zero] at h_lr
    have ht_abs : |t| ≤ T := abs_le.mpr ht
    have hexp_t_ge : 1 ≤ Real.exp (2 * H.s1 η * |t|) := Real.one_le_exp (by positivity)
    have hexp_le : Real.exp (2 * H.s1 η * |t|) - 1 ≤ Real.exp (2 * H.s1 η * T) - 1 := by
      have h_mul : 2 * H.s1 η * |t| ≤ 2 * H.s1 η * T :=
        mul_le_mul_of_nonneg_left ht_abs (by positivity)
      linarith [Real.exp_le_exp.mpr h_mul]
    have hd_cast : (1 + (d : ℝ) / 2) ^ η ≤
        (1 + (regionDist X (Finset.univ \ B) : ℝ) / 2) ^ η := by
      apply Real.rpow_le_rpow (by positivity) _ hη
      have : (d : ℝ) ≤ (regionDist X (Finset.univ \ B) : ℝ) := Nat.cast_le.mpr hd_le
      linarith
    have h_div : (Real.exp (2 * H.s1 η * |t|) - 1) /
          (1 + (regionDist X (Finset.univ \ B) : ℝ) / 2) ^ η ≤
        (Real.exp (2 * H.s1 η * T) - 1) / (1 + (d : ℝ) / 2) ^ η :=
      div_le_div₀ (by linarith) hexp_le (Real.rpow_pos_of_pos (by positivity) η) hd_cast
    calc ‖opCommutator (H.heisenbergEvolve t O_X) Y‖
      _ ≤ 2 * ‖O_X‖ * ‖Y‖ * (X.card : ℝ) *
            ((Real.exp (2 * H.s1 η * |t|) - 1) /
              (1 + (regionDist X (Finset.univ \ B) : ℝ) / 2) ^ η) := h_lr
      _ ≤ 2 * ‖O_X‖ * ‖Y‖ * (X.card : ℝ) *
            ((Real.exp (2 * H.s1 η * T) - 1) / (1 + (d : ℝ) / 2) ^ η) :=
        mul_le_mul_of_nonneg_left h_div (by positivity)
      _ = ε * ‖Y‖ := by dsimp [ε]; ring
  · rw [Finset.not_nonempty_iff_eq_empty] at hBc
    apply norm_heisenbergFlow_sub_condExp_le_of_lieb_robinson H B O_X t hε_nn
    intro Y hY
    rw [hBc] at hY
    rcases isSupportedOn_empty_eq_smul_one hY with ⟨c, rfl⟩
    have h_comm : opCommutator (H.heisenbergEvolve t O_X) (c • 1) = 0 := by
      unfold opCommutator
      rw [mul_smul_comm, smul_mul_assoc, mul_one, one_mul, sub_self]
    rw [h_comm, norm_zero]
    positivity

/-!
## 3. Bare-Frame `condExp` Tail Bounds and Generator Commutator Bounds
-/

/-- Explicit $J$-independent bare perturbation tail profile $g_{\mathrm{bare}, V}$ at scale cutoff $r_{\mathrm{cut}}$:
    combines the low-scale Lieb–Robinson `condExp` factor $\varepsilon_{\mathrm{LR}, \mathrm{bare}}$
    for $1 \le q \le r_{\mathrm{cut}}$ with the high-scale decay tail $2 \sum_{q = r_{\mathrm{cut}} + 1}^L f(q)$. -/
def barePerturbationTailProfile (L r_cut : ℕ) (f : ℕ → ℝ) (ε_LR_bare : ℝ) : ℝ :=
  ε_LR_bare * (∑ q ∈ Finset.Icc 1 r_cut, f q) +
    2 * ∑ q ∈ Finset.Icc (r_cut + 1) L, f q

/-- Nonnegativity of `barePerturbationTailProfile`. -/
lemma barePerturbationTailProfile_nonneg (L r_cut : ℕ) {f : ℕ → ℝ}
    (hf : ∀ q : ℕ, 0 ≤ f q) {ε_LR_bare : ℝ} (hε : 0 ≤ ε_LR_bare) :
    0 ≤ barePerturbationTailProfile L r_cut f ε_LR_bare := by
  dsimp [barePerturbationTailProfile]
  have h1 : 0 ≤ ∑ q ∈ Finset.Icc 1 r_cut, f q := Finset.sum_nonneg (fun q _ => hf q)
  have h2 : 0 ≤ ∑ q ∈ Finset.Icc (r_cut + 1) L, f q := Finset.sum_nonneg (fun q _ => hf q)
  positivity

/-- **Explicit $O(J)$ Bare-Frame Perturbation `condExp` Tail Bound (`h_bare_V`)
    (`norm_bare_bochnerFilteredOp_anchoredSitePerturbationOp_sub_condExp_le_J_mul`)**:
    Under `V.SatisfiesDecayBound J f`, if for scales $1 \le q \le r_{\mathrm{cut}}$ ($r_{\mathrm{cut}} \le L$)
    the bare Bochner filter $\mathcal{F}_{w_{\mathrm{BH11}}}^H$ of an operator supported on `boxCube u q`
    has `condExp` tail on `boxCube u r_bare` bounded by $\varepsilon_{\mathrm{LR}, \mathrm{bare}} \|O\|$,
    then `anchoredSitePerturbationOp anchor V u` satisfies:
    $$\|\mathcal{F}_{w_{\mathrm{BH11}}}^H(V_u) - \mathbb{E}_{B(u, r_{\mathrm{bare}})}(\mathcal{F}_{w_{\mathrm{BH11}}}^H(V_u))\|
      \le J \cdot \mathrm{barePerturbationTailProfile}(L, r_{\mathrm{cut}}, f, \varepsilon_{\mathrm{LR}, \mathrm{bare}}).$$ -/
theorem norm_bare_bochnerFilteredOp_anchoredSitePerturbationOp_sub_condExp_le_J_mul {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    [∀ x, Nonempty (Site x)]
    {anchor : ℕ → Finset (BoxD D L) → BoxD D L}
    {H : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site}
    (hH : IsSelfAdjoint H)
    (V : QuasiLocalPerturbation D L Site) {J : ℝ} {f : ℕ → ℝ}
    (hJ : 0 ≤ J) (hf : ∀ q : ℕ, 0 ≤ f q)
    (hV : V.SatisfiesDecayBound J f)
    (h_anchor : ∀ q ∈ Finset.Icc 1 L, ∀ A ∈ boxCubes D L q, boxCube (anchor q A) q = A)
    (u : BoxD D L) (r_cut r_bare : ℕ) (hr_cut_L : r_cut ≤ L)
    {ε_LR_bare : ℝ} (hε_LR_nn : 0 ≤ ε_LR_bare)
    (h_low_lr : ∀ q ∈ Finset.Icc 1 r_cut,
      ∀ O_q : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site,
      IsSupportedOn Site (boxCube u q) O_q →
      ‖bochnerFilteredOp H bhFilterWeight O_q -
        condExp Site (boxCube u r_bare) (bochnerFilteredOp H bhFilterWeight O_q)‖ ≤
        ε_LR_bare * ‖O_q‖) :
    let V_u := anchoredSitePerturbationOp anchor V u
    ‖bochnerFilteredOp H bhFilterWeight V_u -
      condExp Site (boxCube u r_bare) (bochnerFilteredOp H bhFilterWeight V_u)‖ ≤
      J * barePerturbationTailProfile L r_cut f ε_LR_bare := by
  intro V_u
  let term_q : ℕ → (ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site) :=
    fun q => ∑ A ∈ (boxCubes D L q).filter (fun A => anchor q A = u), V.term q A
  let Ψ : (ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site) →L[ℂ]
      (ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site) :=
    ContinuousLinearMap.id ℂ _ - condExpCLM Site (boxCube u r_bare)
  have hΨ_sum : Ψ (bochnerFilteredOp H bhFilterWeight V_u) =
      ∑ q ∈ Finset.Icc 1 L, Ψ (bochnerFilteredOp H bhFilterWeight (term_q q)) := by
    change Ψ (bochnerFilteredOp H bhFilterWeight (∑ q ∈ Finset.Icc 1 L, term_q q)) = _
    rw [bochnerFilteredOp_finset_sum (Finset.Icc 1 L) H bhFilterWeight term_q
      (fun q _ => integrable_w_BH11_smul_heisenbergFlow H (term_q q)), map_sum]
  have h_norm_q : ∀ q ∈ Finset.Icc 1 L, ‖term_q q‖ ≤ J * f q := by
    intro q hq
    have hJf : 0 ≤ J * f q := mul_nonneg hJ (hf q)
    have hcard : (((boxCubes D L q).filter (fun A => anchor q A = u)).card : ℝ) ≤ 1 := by
      exact_mod_cast card_filter_anchor_le_one q u (h_anchor q hq)
    calc ‖term_q q‖
      _ ≤ ∑ A ∈ (boxCubes D L q).filter (fun A => anchor q A = u), ‖V.term q A‖ :=
        norm_sum_le _ _
      _ ≤ ∑ _A ∈ (boxCubes D L q).filter (fun A => anchor q A = u), (J * f q) :=
        Finset.sum_le_sum (fun A hA => hV q hq A (Finset.mem_filter.mp hA).1)
      _ = (((boxCubes D L q).filter (fun A => anchor q A = u)).card : ℝ) * (J * f q) := by
        rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ 1 * (J * f q) := mul_le_mul_of_nonneg_right hcard hJf
      _ = J * f q := one_mul _
  have h_supp_q : ∀ q ∈ Finset.Icc 1 L, IsSupportedOn Site (boxCube u q) (term_q q) := by
    intro q hq
    refine isSupportedOn_finset_sum (boxCube u q) _ _ (fun A hA => ?_)
    have hA_mem : A ∈ boxCubes D L q := (Finset.mem_filter.mp hA).1
    have hA_eq : A = boxCube u q :=
      Finset.mem_singleton.mp (filter_anchor_subset_singleton q u (h_anchor q hq) hA)
    rw [← hA_eq]
    exact V.is_supported q hq A hA_mem
  have h_union : Finset.Icc 1 L = Finset.Icc 1 r_cut ∪ Finset.Icc (r_cut + 1) L := by
    ext q; simp only [Finset.mem_Icc, Finset.mem_union]; omega
  have h_disj : Disjoint (Finset.Icc 1 r_cut) (Finset.Icc (r_cut + 1) L) := by
    rw [Finset.disjoint_left]
    intro q hq1 hq2
    simp only [Finset.mem_Icc] at hq1 hq2; omega
  have h_low_bound : ∑ q ∈ Finset.Icc 1 r_cut, ‖Ψ (bochnerFilteredOp H bhFilterWeight (term_q q))‖ ≤
      J * (ε_LR_bare * ∑ q ∈ Finset.Icc 1 r_cut, f q) := by
    calc ∑ q ∈ Finset.Icc 1 r_cut, ‖Ψ (bochnerFilteredOp H bhFilterWeight (term_q q))‖
      _ ≤ ∑ q ∈ Finset.Icc 1 r_cut, ε_LR_bare * (J * f q) := by
        refine Finset.sum_le_sum (fun q hq => ?_)
        have hq_L : q ∈ Finset.Icc 1 L :=
          Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp hq).1, le_trans (Finset.mem_Icc.mp hq).2 hr_cut_L⟩
        exact le_trans (h_low_lr q hq (term_q q) (h_supp_q q hq_L))
          (mul_le_mul_of_nonneg_left (h_norm_q q hq_L) hε_LR_nn)
      _ = J * (ε_LR_bare * ∑ q ∈ Finset.Icc 1 r_cut, f q) := by
        rw [← Finset.mul_sum, ← Finset.mul_sum]; ring
  have h_high_bound : ∑ q ∈ Finset.Icc (r_cut + 1) L, ‖Ψ (bochnerFilteredOp H bhFilterWeight (term_q q))‖ ≤
      J * (2 * ∑ q ∈ Finset.Icc (r_cut + 1) L, f q) := by
    calc ∑ q ∈ Finset.Icc (r_cut + 1) L, ‖Ψ (bochnerFilteredOp H bhFilterWeight (term_q q))‖
      _ ≤ ∑ q ∈ Finset.Icc (r_cut + 1) L, 2 * (J * f q) := by
        refine Finset.sum_le_sum (fun q hq => ?_)
        have hq_L : q ∈ Finset.Icc 1 L :=
          Finset.mem_Icc.mpr ⟨by have := (Finset.mem_Icc.mp hq).1; omega, (Finset.mem_Icc.mp hq).2⟩
        have h_ce : ‖Ψ (bochnerFilteredOp H bhFilterWeight (term_q q))‖ ≤
            2 * ‖bochnerFilteredOp H bhFilterWeight (term_q q)‖ :=
          norm_sub_condExp_le_two_mul_norm (boxCube u r_bare) _
        have h_boch : ‖bochnerFilteredOp H bhFilterWeight (term_q q)‖ ≤ ‖term_q q‖ := by
          have h1 := norm_bochnerFilteredOp_le hH bhFilterWeight (term_q q)
          rwa [integral_norm_w_BH11_eq_one, one_mul] at h1
        exact le_trans h_ce (mul_le_mul_of_nonneg_left
          (le_trans h_boch (h_norm_q q hq_L)) (by norm_num))
      _ = J * (2 * ∑ q ∈ Finset.Icc (r_cut + 1) L, f q) := by
        rw [← Finset.mul_sum, ← Finset.mul_sum]; ring
  change ‖Ψ (bochnerFilteredOp H bhFilterWeight V_u)‖ ≤ _
  rw [hΨ_sum, h_union, Finset.sum_union h_disj]
  calc ‖(∑ q ∈ Finset.Icc 1 r_cut, Ψ (bochnerFilteredOp H bhFilterWeight (term_q q))) +
        (∑ q ∈ Finset.Icc (r_cut + 1) L, Ψ (bochnerFilteredOp H bhFilterWeight (term_q q)))‖
    _ ≤ ‖∑ q ∈ Finset.Icc 1 r_cut, Ψ (bochnerFilteredOp H bhFilterWeight (term_q q))‖ +
          ‖∑ q ∈ Finset.Icc (r_cut + 1) L, Ψ (bochnerFilteredOp H bhFilterWeight (term_q q))‖ :=
      norm_add_le _ _
    _ ≤ (∑ q ∈ Finset.Icc 1 r_cut, ‖Ψ (bochnerFilteredOp H bhFilterWeight (term_q q))‖) +
          (∑ q ∈ Finset.Icc (r_cut + 1) L, ‖Ψ (bochnerFilteredOp H bhFilterWeight (term_q q))‖) :=
      add_le_add (norm_sum_le _ _) (norm_sum_le _ _)
    _ ≤ J * (ε_LR_bare * ∑ q ∈ Finset.Icc 1 r_cut, f q) +
          J * (2 * ∑ q ∈ Finset.Icc (r_cut + 1) L, f q) :=
      add_le_add h_low_bound h_high_bound
    _ = J * barePerturbationTailProfile L r_cut f ε_LR_bare := by
      dsimp [barePerturbationTailProfile]; ring

/-- **Explicit $O(J)$ Bare-Frame Check `condExp` Tail Bound (`h_bare_Q`)
    (`norm_bare_bochnerFilteredOp_check_sub_condExp_le_J_mul`)**:
    When `Commute H0 Q_u`, `IsSupportedOn Site (boxCube u r_0) Q_u`, and
    `IsSupportedOn Site (boxCube u r_bare) Q_u`, the bare Bochner filter of $Q_u$ under
    $H = H_0 + V_{\mathrm{tot}}$ satisfies the unconditional $O(J)$ `condExp` tail bound:
    $$\|\mathcal{F}_{w_{\mathrm{BH11}}}^H(Q_u) - \mathbb{E}_{B(u, r_{\mathrm{bare}})}(\mathcal{F}_{w_{\mathrm{BH11}}}^H(Q_u))\|
      \le J \cdot \big(4 \pi C_Q \cdot \mathrm{uniformCubeCommutatorFactor}(D, L, r_0, f)\big).$$ -/
theorem norm_bare_bochnerFilteredOp_check_sub_condExp_le_J_mul {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    [∀ x, Nonempty (Site x)]
    {H0 Q_u : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site}
    (V : QuasiLocalPerturbation D L Site) {J C_Q : ℝ} {f : ℕ → ℝ}
    (hJ : 0 ≤ J) (hf : ∀ q ∈ Finset.Icc 1 L, 0 ≤ f q)
    (hV : V.SatisfiesDecayBound J f)
    (hH : IsSelfAdjoint (H0 + V.totalPerturbation))
    (h_comm : Commute H0 Q_u)
    (u : BoxD D L) (r_0 r_bare : ℕ)
    (hQ_norm : ‖Q_u‖ ≤ C_Q)
    (hQ_supp_0 : IsSupportedOn Site (boxCube u r_0) Q_u)
    (hQ_supp_bare : IsSupportedOn Site (boxCube u r_bare) Q_u) :
    let H := H0 + V.totalPerturbation
    ‖bochnerFilteredOp H bhFilterWeight Q_u -
      condExp Site (boxCube u r_bare) (bochnerFilteredOp H bhFilterWeight Q_u)‖ ≤
      J * (4 * Real.pi * C_Q * uniformCubeCommutatorFactor D L r_0 f) := by
  intro H
  let ΔQ := bochnerFilteredOp H bhFilterWeight Q_u - Q_u
  have hQ_ce : condExp Site (boxCube u r_bare) Q_u = Q_u :=
    condExp_eq_self_of_isSupportedOn hQ_supp_bare
  have h_id : bochnerFilteredOp H bhFilterWeight Q_u -
      condExp Site (boxCube u r_bare) (bochnerFilteredOp H bhFilterWeight Q_u) =
      ΔQ - condExp Site (boxCube u r_bare) ΔQ := by
    dsimp [ΔQ]
    rw [condExp_sub_clm, hQ_ce]
    abel
  have h1 := norm_bochnerFilteredOp_w_BH11_sub_self_le_of_satisfiesDecayBound
    V hH h_comm hV u r_0 hQ_supp_0
  have h_uf_nn : 0 ≤ uniformCubeCommutatorFactor D L r_0 f :=
    uniformCubeCommutatorFactor_nonneg D L r_0 hf
  have h_drift : ‖ΔQ‖ ≤ J * (2 * Real.pi * C_Q * uniformCubeCommutatorFactor D L r_0 f) := by
    have h2 : 2 * Real.pi * ‖Q_u‖ * J * uniformCubeCommutatorFactor D L r_0 f ≤
        2 * Real.pi * C_Q * J * uniformCubeCommutatorFactor D L r_0 f := by
      have : 0 ≤ 2 * Real.pi * J * uniformCubeCommutatorFactor D L r_0 f := by positivity
      nlinarith
    linarith
  have h_ce : ‖ΔQ - condExp Site (boxCube u r_bare) ΔQ‖ ≤ 2 * ‖ΔQ‖ :=
    norm_sub_condExp_le_two_mul_norm (boxCube u r_bare) ΔQ
  rw [h_id]
  linarith

/-- **Explicit $O(J)$ Commutator Bound with a Quasi-Local QAC Generator (`norm_opCommutator_localOp_katoGenerator_le_J_mul`)**:
    If a QAC generator $D_{\mathrm{loc}} : \mathrm{QuasiLocalPerturbation}\ D\ L\ \mathrm{Site}$ satisfies
    `D_loc.SatisfiesDecayBound J f_D` (`∀ q ∈ Icc 1 L, ∀ A ∈ BoxCubes D L q, ‖D_loc.term q A‖ ≤ J * f_D q`),
    then for any observable $O_X$ supported on `boxCube u r_X`,
    $$\|[D_{\mathrm{loc}}.V_{\mathrm{tot}}, O_X]\|
      \le J \cdot \big(2 \cdot \mathrm{uniformCubeCommutatorFactor}(D, L, r_X, f_D)\big) \cdot \|O_X\|.$$ -/
theorem norm_opCommutator_localOp_katoGenerator_le_J_mul {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    (D_loc : QuasiLocalPerturbation D L Site) {J : ℝ} {f_D : ℕ → ℝ}
    (_hJ : 0 ≤ J) (_hf_D : ∀ q ∈ Finset.Icc 1 L, 0 ≤ f_D q)
    (hD_decay : D_loc.SatisfiesDecayBound J f_D)
    (u : BoxD D L) (r_X : ℕ)
    {O_X : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site}
    (hO_X : IsSupportedOn Site (boxCube u r_X) O_X) :
    ‖opCommutator D_loc.totalPerturbation O_X‖ ≤
      (J * (2 * uniformCubeCommutatorFactor D L r_X f_D)) * ‖O_X‖ ∧
    ‖opCommutator O_X D_loc.totalPerturbation‖ ≤
      (J * (2 * uniformCubeCommutatorFactor D L r_X f_D)) * ‖O_X‖ := by
  have h1 := norm_opCommutator_V_tot_boxCube_le_uniform D_loc hD_decay u r_X hO_X
  have h_eq : 2 * ‖O_X‖ * J * uniformCubeCommutatorFactor D L r_X f_D =
      (J * (2 * uniformCubeCommutatorFactor D L r_X f_D)) * ‖O_X‖ := by ring
  rw [h_eq] at h1
  have h2 : ‖opCommutator O_X D_loc.totalPerturbation‖ = ‖opCommutator D_loc.totalPerturbation O_X‖ := by
    unfold opCommutator
    rw [← norm_neg, neg_sub]
  exact ⟨h1, h2.symm ▸ h1⟩

end
