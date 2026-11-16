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

import Proofs.HastingsKomaLightCone.LatticeHamiltonianS1Bounds

open scoped Classical InnerProduct ComplexConjugate BigOperators
open Filter Topology Asymptotics ContinuousLinearMap KMSPinchedGibbs PerturbedThermalBarrier
open WeldedHierarchy WeldedHierarchy.BDLDecoder InhomogeneousMemoryChallenge

noncomputable section

set_option maxRecDepth 200000
set_option maxHeartbeats 800000

/-!
# Interpolated Lattice Interaction Moments and Superpolynomial Envelopes

Bounds the Hastings–Koma polynomial interaction moment `s1` of `interpolatedLatticeHamiltonian` uniformly in system size (`bdlInhomogeneousInterpolatedS1Bound`). Constructs the infimum envelope `hastingsKomaSuperpolyEnvelope` across all polynomial decay orders, proving membership in `IsSuperpolynomialDecay` and deriving single-site and Bochner light-cone bounds.

## References

* Part I, Section 6.1 (`subsec:dsuper-banach`), Lemma 6.2 (`lem:dsuper-closure`)
* Part I, Section 6.2 (`subsec:bochner-lr`), Equation (70) (`eq:hastings-koma-lr`), Equation (73) (`eq:unitary-one-site-lr`)
* Hastings–Koma (2006), Communications in Mathematical Physics 265, 781–804
-/

/-! ## 1. $L$-Independent `s1` Bound for `interpolatedLatticeHamiltonian` -/

/-- $L$-independent and $J$-independent upper bound on `(interpolatedLatticeHamiltonian mem.sys V s).s1 η`
    for $s \in [-1, 1]$ and $0 \le J \le 1$. -/
def bdlInhomogeneousInterpolatedS1Bound (f : ℕ → ℝ) (η : ℝ) : ℝ :=
  bdlInhomogeneousUnperturbedS1Bound η + quasiLocalS1Factor 3 f η

lemma bdlInhomogeneousInterpolatedS1Bound_nonneg {f : ℕ → ℝ} (hf : IsSuperpolynomialDecay f)
    (η : ℝ) : 0 ≤ bdlInhomogeneousInterpolatedS1Bound f η :=
  add_nonneg (bdlInhomogeneousUnperturbedS1Bound_nonneg η) (quasiLocalS1Factor_nonneg 3 hf η)

/-- **$L$-Independent `s1` Bound for `interpolatedLatticeHamiltonian`
    (`interpolatedLatticeHamiltonian_s1_inhomogeneous_le`)**:
    For any `mem : Inhomogeneous3DMemoryRealization`, any `V` with `V.SatisfiesDecayBound J f`
    (`0 ≤ J ≤ 1`, `IsSuperpolynomialDecay f`), any `s` with `|s| ≤ 1`, and any `0 ≤ η`:
    `(interpolatedLatticeHamiltonian mem.sys V s).s1 η ≤ bdlInhomogeneousInterpolatedS1Bound f η`. -/
theorem interpolatedLatticeHamiltonian_s1_inhomogeneous_le {L : ℕ} [NeZero L]
    {c_star C β_c c_F η_mem c_mem J s η : ℝ} {f : ℕ → ℝ}
    (mem : Inhomogeneous3DMemoryRealization L qCodeBDL r0BDL mMaxBDL c_star C β_c c_F η_mem c_mem)
    (V : QuasiLocalPerturbation 3 L (UniformSite3D L (CodeSlotConfig qCodeBDL)))
    (hJ0 : 0 ≤ J) (hJ1 : J ≤ 1) (hs : |s| ≤ 1)
    (hf : IsSuperpolynomialDecay f) (hV : V.SatisfiesDecayBound J f) (hη : 0 ≤ η) :
    (interpolatedLatticeHamiltonian mem.sys V s).s1 η ≤
      bdlInhomogeneousUnperturbedS1Bound η + J * quasiLocalS1Factor 3 f η ∧
    (interpolatedLatticeHamiltonian mem.sys V s).s1 η ≤
      bdlInhomogeneousInterpolatedS1Bound f η := by
  haveI : NeZero 3 := ⟨by decide⟩
  have h1 : (interpolatedLatticeHamiltonian mem.sys V s).s1 η ≤
      bdlInhomogeneousUnperturbedS1Bound η + J * quasiLocalS1Factor 3 f η := by
    unfold LatticeHamiltonian.s1 interpolatedLatticeHamiltonian
    (try dsimp only)
    refine Finset.sup'_le Finset.univ_nonempty _ fun x _ => ?_
    have h_tri : (∑ Z ∈ Finset.univ.filter (fun Z : Finset (Box3D L) => x ∈ Z),
        ‖unperturbedLatticeTerm mem.sys Z + perturbationLatticeTerm V s Z‖ *
          (Z.card : ℝ) * (1 + (regionDiam Z : ℝ)) ^ η) ≤
        (∑ Z ∈ Finset.univ.filter (fun Z : Finset (Box3D L) => x ∈ Z),
          ‖unperturbedLatticeTerm mem.sys Z‖ * (Z.card : ℝ) * (1 + (regionDiam Z : ℝ)) ^ η) +
        (∑ Z ∈ Finset.univ.filter (fun Z : Finset (Box3D L) => x ∈ Z),
          ‖perturbationLatticeTerm V s Z‖ * (Z.card : ℝ) * (1 + (regionDiam Z : ℝ)) ^ η) := by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_le_sum fun Z _ => ?_
      have h_add := norm_add_le (unperturbedLatticeTerm mem.sys Z) (perturbationLatticeTerm V s Z)
      have h_w_nn : 0 ≤ (Z.card : ℝ) * (1 + (regionDiam Z : ℝ)) ^ η := by positivity
      calc ‖unperturbedLatticeTerm mem.sys Z + perturbationLatticeTerm V s Z‖ *
            (Z.card : ℝ) * (1 + (regionDiam Z : ℝ)) ^ η
        _ = ‖unperturbedLatticeTerm mem.sys Z + perturbationLatticeTerm V s Z‖ *
              ((Z.card : ℝ) * (1 + (regionDiam Z : ℝ)) ^ η) := by ring
        _ ≤ (‖unperturbedLatticeTerm mem.sys Z‖ + ‖perturbationLatticeTerm V s Z‖) *
              ((Z.card : ℝ) * (1 + (regionDiam Z : ℝ)) ^ η) :=
          mul_le_mul_of_nonneg_right h_add h_w_nn
        _ = ‖unperturbedLatticeTerm mem.sys Z‖ * (Z.card : ℝ) * (1 + (regionDiam Z : ℝ)) ^ η +
              ‖perturbationLatticeTerm V s Z‖ * (Z.card : ℝ) * (1 + (regionDiam Z : ℝ)) ^ η := by
          ring
    exact le_trans h_tri (add_le_add
      (sum_unperturbedLatticeTerm_s1_inhomogeneous_le mem hη x)
      (sum_perturbationLatticeTerm_s1_le_J_mul V hJ0 hs hf hV hη x))
  have h2 : bdlInhomogeneousUnperturbedS1Bound η + J * quasiLocalS1Factor 3 f η ≤
      bdlInhomogeneousInterpolatedS1Bound f η := by
    unfold bdlInhomogeneousInterpolatedS1Bound
    have h_f_nn := quasiLocalS1Factor_nonneg 3 hf η
    linarith [mul_le_of_le_one_left h_f_nn hJ1]
  exact ⟨h1, le_trans h1 h2⟩

/-- `bhmUniformCouplingThreshold D C m_0 g_tail ≤ 1` whenever `1 ≤ C`, `0 ≤ m_0`, and `IsSuperpolynomialDecay g_tail`. -/
lemma bhmUniformCouplingThreshold_le_one (D : ℕ) {C m_0 : ℝ} (hC : 1 ≤ C) (hm0 : 0 ≤ m_0)
    {g_tail : ℕ → ℝ} (hg_tail : IsSuperpolynomialDecay g_tail) :
    bhmUniformCouplingThreshold D C m_0 g_tail ≤ 1 := by
  unfold bhmUniformCouplingThreshold
  have h_nn := (bhmShellNormalizedMomentSum_le_uniform D hC hm0 hg_tail (le_refl 1)).1
  have h_dev : bhmSandwichDeviation ≤ 1 := by dsimp [bhmSandwichDeviation]; norm_num
  exact div_le_one_of_le₀ (by linarith) (by linarith)

/-- For $0 \le J \le 1$, $0 \le a$, and $x \le J a$, $\exp(x) - 1 \le J (a \exp(a))$. -/
lemma exp_sub_one_le_J_mul_of_le_J_mul {x J a : ℝ}
    (hJ0 : 0 ≤ J) (hJ1 : J ≤ 1) (ha : 0 ≤ a) (hx : x ≤ J * a) :
    Real.exp x - 1 ≤ J * (a * Real.exp a) := by
  have h_exp_x : Real.exp x ≤ Real.exp (J * a) := Real.exp_le_exp.mpr hx
  have h1 : 1 - J * a ≤ Real.exp (-(J * a)) := by
    have := Real.add_one_le_exp (-(J * a))
    linarith
  have h_prod : Real.exp (-(J * a)) * Real.exp (J * a) = 1 := by
    rw [← Real.exp_add]; ring_nf; exact Real.exp_zero
  have h_step : Real.exp (J * a) - 1 ≤ J * a * Real.exp (J * a) := by
    have := mul_le_mul_of_nonneg_right h1 (le_of_lt (Real.exp_pos (J * a)))
    linarith
  have h_exp_Ja : Real.exp (J * a) ≤ Real.exp a :=
    Real.exp_le_exp.mpr (by nlinarith)
  have h_rhs : J * a * Real.exp (J * a) ≤ J * (a * Real.exp a) := by
    have hJa_nn : 0 ≤ J * a := mul_nonneg hJ0 ha
    calc J * a * Real.exp (J * a)
      _ ≤ J * a * Real.exp a := mul_le_mul_of_nonneg_left h_exp_Ja hJa_nn
      _ = J * (a * Real.exp a) := by ring
  linarith

/-! ## 2. Polynomial-Family Infimum Envelope & Superpolynomial Decay -/

/-- Infimum over $0 \le m \le r$ of the polynomial-decay bounds $C(m) / (1 + d(r) / 2)^m$. -/
def hastingsKomaSuperpolyEnvelope (C : ℕ → ℝ) (d : ℕ → ℕ) (r : ℕ) : ℝ :=
  (Finset.range (r + 1)).inf' Finset.nonempty_range_add_one
    (fun m => C m / (1 + (d r : ℝ) / 2) ^ m)

lemma hastingsKomaSuperpolyEnvelope_nonneg {C : ℕ → ℝ} (hC : ∀ m, 0 ≤ C m)
    (d : ℕ → ℕ) (r : ℕ) :
    0 ≤ hastingsKomaSuperpolyEnvelope C d r := by
  unfold hastingsKomaSuperpolyEnvelope
  exact Finset.le_inf' Finset.nonempty_range_add_one _ fun m _ =>
    div_nonneg (hC m) (by positivity)

/-- If $X \le J \cdot (C(m) / (1 + d(r)/2)^m)$ for all $m \in \mathbb{N}$, then
    $X \le J \cdot \mathrm{hastingsKomaSuperpolyEnvelope}\ C\ d\ r$. -/
lemma le_mul_hastingsKomaSuperpolyEnvelope_of_forall {C : ℕ → ℝ} {d : ℕ → ℕ}
    {J X : ℝ} {r : ℕ}
    (h : ∀ m : ℕ, X ≤ J * (C m / (1 + (d r : ℝ) / 2) ^ m)) :
    X ≤ J * hastingsKomaSuperpolyEnvelope C d r := by
  rcases Finset.exists_mem_eq_inf' (@Finset.nonempty_range_add_one r)
      (fun m => C m / (1 + (d r : ℝ) / 2) ^ m) with ⟨m, _, hm_eq⟩
  unfold hastingsKomaSuperpolyEnvelope
  rw [hm_eq]
  exact h m

/-- Unscaled variant of `le_mul_hastingsKomaSuperpolyEnvelope_of_forall` ($J = 1$). -/
lemma le_hastingsKomaSuperpolyEnvelope_of_forall {C : ℕ → ℝ} {d : ℕ → ℕ}
    {X : ℝ} {r : ℕ}
    (h : ∀ m : ℕ, X ≤ C m / (1 + (d r : ℝ) / 2) ^ m) :
    X ≤ hastingsKomaSuperpolyEnvelope C d r := by
  simpa only [one_mul] using
    le_mul_hastingsKomaSuperpolyEnvelope_of_forall (J := 1) (fun m => by simpa using h m)

/-- **Superpolynomial Decay of `hastingsKomaSuperpolyEnvelope`
    (`isSuperpolynomialDecay_hastingsKomaSuperpolyEnvelope`)**:
    Whenever `0 ≤ C m` for all $m$ and `r ≤ c * d r` eventually for some $c \ge 1$,
    `hastingsKomaSuperpolyEnvelope C d` belongs to `IsSuperpolynomialDecay`. -/
theorem isSuperpolynomialDecay_hastingsKomaSuperpolyEnvelope
    {C : ℕ → ℝ} (hC : ∀ m, 0 ≤ C m)
    {d : ℕ → ℕ} (hd : ∃ c : ℕ, 1 ≤ c ∧ ∀ᶠ r in atTop, r ≤ c * d r) :
    IsSuperpolynomialDecay (hastingsKomaSuperpolyEnvelope C d) := by
  refine ⟨hastingsKomaSuperpolyEnvelope_nonneg hC d, fun n => ?_⟩
  rcases hd with ⟨c, hc1, hdc⟩
  let M_const : ℝ := C (n + 1) * (2 * (c : ℝ)) ^ (n + 1)
  have h_zero : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 0) := tendsto_const_nhds
  have h_upper : Tendsto (fun r : ℕ => M_const * (r : ℝ)⁻¹) atTop (𝓝 0) := by
    simpa using (tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop).const_mul M_const
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' h_zero h_upper
    (Eventually.of_forall fun r =>
      mul_nonneg (pow_nonneg (Nat.cast_nonneg r) n)
        (hastingsKomaSuperpolyEnvelope_nonneg hC d r)) ?_
  filter_upwards [hdc, eventually_ge_atTop (n + 1)] with r hr_d hr_n
  have hr_pos : (0 : ℝ) < (r : ℝ) := Nat.cast_pos.mpr (by omega)
  have hr_ne : (r : ℝ) ≠ 0 := ne_of_gt hr_pos
  have hm_mem : n + 1 ∈ Finset.range (r + 1) := Finset.mem_range.mpr (by omega)
  have h_inf_le : hastingsKomaSuperpolyEnvelope C d r ≤
      C (n + 1) / (1 + (d r : ℝ) / 2) ^ (n + 1) :=
    Finset.inf'_le (fun m => C m / (1 + (d r : ℝ) / 2) ^ m) hm_mem
  have hc_r : (1 : ℝ) ≤ (c : ℝ) := by exact_mod_cast hc1
  have hr_le : (r : ℝ) ≤ (2 * (c : ℝ)) * (1 + (d r : ℝ) / 2) := by
    have hd_r : (r : ℝ) ≤ (c : ℝ) * (d r : ℝ) := by exact_mod_cast hr_d
    nlinarith
  have h_pow : (r : ℝ) ^ (n + 1) ≤
      (2 * (c : ℝ)) ^ (n + 1) * (1 + (d r : ℝ) / 2) ^ (n + 1) := by
    rw [← mul_pow]
    exact pow_le_pow_left₀ (Nat.cast_nonneg r) hr_le (n + 1)
  let D_pow : ℝ := (1 + (d r : ℝ) / 2) ^ (n + 1)
  have hD_pos : 0 < D_pow := by dsimp [D_pow]; positivity
  have h_div_le : (r : ℝ) ^ (n + 1) / D_pow ≤ (2 * (c : ℝ)) ^ (n + 1) :=
    (div_le_iff₀ hD_pos).mpr h_pow
  have h_id : (r : ℝ) ^ n * (C (n + 1) / D_pow) =
      C (n + 1) * ((r : ℝ)⁻¹ * ((r : ℝ) ^ (n + 1) / D_pow)) := by
    have h_rn : (r : ℝ) ^ (n + 1) = (r : ℝ) * (r : ℝ) ^ n := by rw [pow_succ']
    have h1 : (r : ℝ)⁻¹ * (r : ℝ) ^ (n + 1) = (r : ℝ) ^ n := by
      rw [h_rn, inv_mul_cancel_left₀ hr_ne]
    calc (r : ℝ) ^ n * (C (n + 1) / D_pow)
      _ = ((r : ℝ)⁻¹ * (r : ℝ) ^ (n + 1)) * (C (n + 1) / D_pow) := by rw [h1]
      _ = C (n + 1) * ((r : ℝ)⁻¹ * ((r : ℝ) ^ (n + 1) / D_pow)) := by ring
  calc (r : ℝ) ^ n * hastingsKomaSuperpolyEnvelope C d r
    _ ≤ (r : ℝ) ^ n * (C (n + 1) / D_pow) :=
      mul_le_mul_of_nonneg_left h_inf_le (pow_nonneg (Nat.cast_nonneg r) n)
    _ = C (n + 1) * ((r : ℝ)⁻¹ * ((r : ℝ) ^ (n + 1) / D_pow)) := h_id
    _ ≤ C (n + 1) * ((r : ℝ)⁻¹ * (2 * (c : ℝ)) ^ (n + 1)) := by
      refine mul_le_mul_of_nonneg_left ?_ (hC (n + 1))
      exact mul_le_mul_of_nonneg_left h_div_le (inv_nonneg.mpr (le_of_lt hr_pos))
    _ = M_const * (r : ℝ)⁻¹ := by dsimp [M_const]; ring

/-! ## 3. Unconditional 1-Site `boxBall v r_LR` & Interpolated Bochner Light-Cone Bounds -/

/-- Order-$m$ Hastings–Koma 1-site numerator constant for a quasi-local generator with decay `f_D`. -/
def hastingsKomaOneSiteConst (D : ℕ) (f_D : ℕ → ℝ) (m : ℕ) : ℝ :=
  4 * quasiLocalS1Factor D f_D (m : ℝ) * Real.exp (2 * quasiLocalS1Factor D f_D (m : ℝ))

lemma hastingsKomaOneSiteConst_nonneg (D : ℕ) {f_D : ℕ → ℝ} (hf_D : IsSuperpolynomialDecay f_D)
    (m : ℕ) : 0 ≤ hastingsKomaOneSiteConst D f_D m := by
  unfold hastingsKomaOneSiteConst
  have := quasiLocalS1Factor_nonneg D hf_D (m : ℝ)
  positivity

/-- $L$-independent superpolynomially decaying 1-site `boxBall` light-cone tail profile `g_LR`. -/
def hastingsKomaOneSiteTailProfile (D : ℕ) (f_D : ℕ → ℝ) (r : ℕ) : ℝ :=
  hastingsKomaSuperpolyEnvelope (hastingsKomaOneSiteConst D f_D) (fun r => r + 1) r

/-- `hastingsKomaOneSiteTailProfile D f_D` belongs to `IsSuperpolynomialDecay` whenever `f_D` does. -/
theorem isSuperpolynomialDecay_hastingsKomaOneSiteTailProfile (D : ℕ) {f_D : ℕ → ℝ}
    (hf_D : IsSuperpolynomialDecay f_D) :
    IsSuperpolynomialDecay (hastingsKomaOneSiteTailProfile D f_D) :=
  isSuperpolynomialDecay_hastingsKomaSuperpolyEnvelope
    (hastingsKomaOneSiteConst_nonneg D hf_D)
    ⟨1, le_rfl, Eventually.of_forall fun r => by omega⟩

/-- **Unconditional 1-Site `boxBall v r_LR` Hastings–Koma Light-Cone `condExp` Bound
    (`norm_unitaryOfTimeEvolutionOp_singleSite_boxBall_sub_condExp_le_J_mul`)**:
    For any `D_loc : QuasiLocalPerturbation D L Site` satisfying `D_loc.SatisfiesDecayBound J f_D`
    (`0 ≤ J ≤ 1`, `IsSuperpolynomialDecay f_D`), any `s ∈ Set.Icc (-1) 1`, any `v : BoxD D L`,
    any `r_LR : ℕ`, and any 1-site observable `A_v` (`IsSupportedOn Site {v} A_v`):
    $$\|U_s^\dagger A_v U_s - \mathbb{E}_{\mathrm{boxBall}(v, r_{\mathrm{LR}})}(U_s^\dagger A_v U_s)\|
      \le (J \cdot \mathrm{hastingsKomaOneSiteTailProfile}\ D\ f_D\ r_{\mathrm{LR}}) \cdot \|A_v\|.$$ -/
theorem norm_unitaryOfTimeEvolutionOp_singleSite_boxBall_sub_condExp_le_J_mul
    {D L : ℕ} [NeZero D] [NeZero L]
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    [∀ x, Nonempty (Site x)]
    (D_loc : QuasiLocalPerturbation D L Site) {J s : ℝ} {f_D : ℕ → ℝ}
    (hJ0 : 0 ≤ J) (hJ1 : J ≤ 1) (hs : s ∈ Set.Icc (-1) 1)
    (hf_D : IsSuperpolynomialDecay f_D) (hD_dec : D_loc.SatisfiesDecayBound J f_D)
    (v : BoxD D L) (r_LR : ℕ)
    (A_v : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site)
    (hA_v : IsSupportedOn Site {v} A_v) :
    let U_s := unitaryOfTimeEvolutionOp D_loc.totalPerturbation D_loc.isSelfAdjoint_totalPerturbation s
    ‖U_s.1† * A_v * U_s.1 - condExp Site (boxBall v r_LR) (U_s.1† * A_v * U_s.1)‖ ≤
      (J * hastingsKomaOneSiteTailProfile D f_D r_LR) * ‖A_v‖ := by
  intro U_s
  let H_D := perturbationLatticeHamiltonian D_loc 1
  have hU_eq : U_s.1 = (unitaryOfTimeEvolutionOp H_D.totalHamiltonian H_D.isSelfAdjoint_totalHamiltonian s).1 := by
    change timeEvolutionOp D_loc.totalPerturbation s = timeEvolutionOp H_D.totalHamiltonian s
    rw [perturbationLatticeHamiltonian_one_H_tot]
  rw [show (J * hastingsKomaOneSiteTailProfile D f_D r_LR) * ‖A_v‖ =
      (J * ‖A_v‖) * hastingsKomaSuperpolyEnvelope (hastingsKomaOneSiteConst D f_D)
        (fun r => r + 1) r_LR by unfold hastingsKomaOneSiteTailProfile; ring]
  apply le_mul_hastingsKomaSuperpolyEnvelope_of_forall
  intro m
  have hm_nn : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
  have h_hk :
      ‖(unitaryOfTimeEvolutionOp H_D.totalHamiltonian H_D.isSelfAdjoint_totalHamiltonian s).1† * A_v *
          (unitaryOfTimeEvolutionOp H_D.totalHamiltonian H_D.isSelfAdjoint_totalHamiltonian s).1 -
        condExp Site (boxBall v r_LR)
          ((unitaryOfTimeEvolutionOp H_D.totalHamiltonian H_D.isSelfAdjoint_totalHamiltonian s).1† * A_v *
            (unitaryOfTimeEvolutionOp H_D.totalHamiltonian H_D.isSelfAdjoint_totalHamiltonian s).1)‖ ≤
      (2 * (({v} : Finset (BoxD D L)).card : ℝ) *
        ((Real.exp (2 * H_D.s1 (m : ℝ) * 1) - 1) /
          (1 + ((r_LR + 1 : ℕ) : ℝ) / 2) ^ (m : ℝ))) * ‖A_v‖ :=
    norm_unitaryOfTimeEvolutionOp_adj_conj_sub_condExp_le_hastings_koma
      H_D hm_nn zero_le_one hs (Finset.singleton_nonempty v) (Nat.succ_pos r_LR)
      (regionDist_singleton_compl_boxBall_ge v r_LR) A_v hA_v
  rw [← hU_eq, Finset.card_singleton, Nat.cast_one, mul_one, Real.rpow_natCast] at h_hk
  have hs1 : H_D.s1 (m : ℝ) ≤ J * quasiLocalS1Factor D f_D (m : ℝ) :=
    perturbationLatticeHamiltonian_s1_le_J_mul D_loc hJ0 (by norm_num) hf_D hD_dec hm_nn
  have h_exp : Real.exp (2 * H_D.s1 (m : ℝ) * 1) - 1 ≤
      J * ((2 * quasiLocalS1Factor D f_D (m : ℝ)) *
        Real.exp (2 * quasiLocalS1Factor D f_D (m : ℝ))) := by
    refine exp_sub_one_le_J_mul_of_le_J_mul hJ0 hJ1 ?_ (by linarith)
    have := quasiLocalS1Factor_nonneg D hf_D (m : ℝ); positivity
  have h_denom_pos : (0 : ℝ) < (1 + ((r_LR + 1 : ℕ) : ℝ) / 2) ^ m := by positivity
  have h_div : 2 * ((Real.exp (2 * H_D.s1 (m : ℝ) * 1) - 1) /
        (1 + ((r_LR + 1 : ℕ) : ℝ) / 2) ^ m) * ‖A_v‖ ≤
      (J * ‖A_v‖) * (hastingsKomaOneSiteConst D f_D m /
        (1 + ((r_LR + 1 : ℕ) : ℝ) / 2) ^ m) := by
    have h_num : 2 * (Real.exp (2 * H_D.s1 (m : ℝ) * 1) - 1) * ‖A_v‖ ≤
        (J * ‖A_v‖) * hastingsKomaOneSiteConst D f_D m := by
      unfold hastingsKomaOneSiteConst
      have h1 := mul_le_mul_of_nonneg_right h_exp (norm_nonneg A_v)
      linarith
    calc 2 * ((Real.exp (2 * H_D.s1 (m : ℝ) * 1) - 1) /
            (1 + ((r_LR + 1 : ℕ) : ℝ) / 2) ^ m) * ‖A_v‖
      _ = (2 * (Real.exp (2 * H_D.s1 (m : ℝ) * 1) - 1) * ‖A_v‖) /
            (1 + ((r_LR + 1 : ℕ) : ℝ) / 2) ^ m := by ring
      _ ≤ ((J * ‖A_v‖) * hastingsKomaOneSiteConst D f_D m) /
            (1 + ((r_LR + 1 : ℕ) : ℝ) / 2) ^ m :=
        div_le_div_of_nonneg_right h_num (le_of_lt h_denom_pos)
      _ = (J * ‖A_v‖) * (hastingsKomaOneSiteConst D f_D m /
            (1 + ((r_LR + 1 : ℕ) : ℝ) / 2) ^ m) := by ring
  exact le_trans h_hk h_div

/-- Order-$m$ Hastings–Koma Bochner `bhFilterWeight` numerator constant for `interpolatedLatticeHamiltonian`. -/
def bdlBochnerHastingsKomaConst (f : ℕ → ℝ) (m : ℕ) : ℝ :=
  2 * (Real.exp (2 * bdlInhomogeneousInterpolatedS1Bound f (m : ℝ) * Real.pi) - 1)

lemma bdlBochnerHastingsKomaConst_nonneg {f : ℕ → ℝ} (hf : IsSuperpolynomialDecay f) (m : ℕ) :
    0 ≤ bdlBochnerHastingsKomaConst f m := by
  unfold bdlBochnerHastingsKomaConst
  have h_s1 := bdlInhomogeneousInterpolatedS1Bound_nonneg hf (m : ℝ)
  have h_pi := Real.pi_pos.le
  have h1 : 1 ≤ Real.exp (2 * bdlInhomogeneousInterpolatedS1Bound f (m : ℝ) * Real.pi) :=
    Real.one_le_exp (by positivity)
  linarith

/-- Superpolynomially decaying Hastings–Koma Bochner `bhFilterWeight` envelope with distance function `d`. -/
def bdlBochnerHastingsKomaEnvelope (f : ℕ → ℝ) (d : ℕ → ℕ) (r : ℕ) : ℝ :=
  hastingsKomaSuperpolyEnvelope (bdlBochnerHastingsKomaConst f) d r

lemma bdlBochnerHastingsKomaEnvelope_nonneg {f : ℕ → ℝ} (hf : IsSuperpolynomialDecay f)
    (d : ℕ → ℕ) (r : ℕ) :
    0 ≤ bdlBochnerHastingsKomaEnvelope f d r :=
  hastingsKomaSuperpolyEnvelope_nonneg (bdlBochnerHastingsKomaConst_nonneg hf) d r

/-- **Hastings–Koma Bochner `bhFilterWeight` Light-Cone `condExp` Bound for $H(s) = H_0 + s V_{\mathrm{tot}}$
    (`norm_bochnerFilteredOp_interpolated_sub_condExp_inhomogeneous_le`)**. -/
theorem norm_bochnerFilteredOp_interpolated_sub_condExp_inhomogeneous_le
    {L : ℕ} [NeZero L]
    {c_star C β_c c_F η_mem c_mem J s : ℝ} {f : ℕ → ℝ}
    (mem : Inhomogeneous3DMemoryRealization L qCodeBDL r0BDL mMaxBDL c_star C β_c c_F η_mem c_mem)
    (V : QuasiLocalPerturbation 3 L (UniformSite3D L (CodeSlotConfig qCodeBDL)))
    (hJ0 : 0 ≤ J) (hJ1 : J ≤ 1) (hs : s ∈ Set.Icc (-1) 1)
    (hf : IsSuperpolynomialDecay f) (hV : V.SatisfiesDecayBound J f)
    {X B : Finset (Box3D L)} (hX : X.Nonempty)
    (d : ℕ → ℕ) (r : ℕ) (hd_pos : 0 < d r)
    (h_dist : (Finset.univ \ B).Nonempty → d r ≤ regionDist X (Finset.univ \ B))
    (O_X : ManyBodyHilbertSpace (UniformSite3D L (CodeSlotConfig qCodeBDL)) →L[ℂ]
      ManyBodyHilbertSpace (UniformSite3D L (CodeSlotConfig qCodeBDL)))
    (hO_X : IsSupportedOn (UniformSite3D L (CodeSlotConfig qCodeBDL)) X O_X) :
    let H_s := mem.sys.H0 + (scaleQuasiLocalPerturbation s V).totalPerturbation
    ‖bochnerFilteredOp H_s bhFilterWeight O_X -
      condExp (UniformSite3D L (CodeSlotConfig qCodeBDL)) B
        (bochnerFilteredOp H_s bhFilterWeight O_X)‖ ≤
      ((X.card : ℝ) * bdlBochnerHastingsKomaEnvelope f d r) * ‖O_X‖ := by
  intro H_s
  haveI : NeZero 3 := ⟨by decide⟩
  let H_lat := interpolatedLatticeHamiltonian mem.sys V s
  have hHs_eq : H_s = H_lat.totalHamiltonian := by
    dsimp [H_s, H_lat]
    rw [interpolatedLatticeHamiltonian_H_tot, interpolatedHamiltonianOp,
      scaleQuasiLocalPerturbation_V_tot]
  have hs_abs : |s| ≤ 1 := abs_le.mpr hs
  rw [show ((X.card : ℝ) * bdlBochnerHastingsKomaEnvelope f d r) * ‖O_X‖ =
      ((X.card : ℝ) * ‖O_X‖) *
        hastingsKomaSuperpolyEnvelope (bdlBochnerHastingsKomaConst f) d r by
    unfold bdlBochnerHastingsKomaEnvelope; ring]
  apply le_mul_hastingsKomaSuperpolyEnvelope_of_forall
  intro m0
  set ε : ℝ := ((X.card : ℝ) * ‖O_X‖) *
    (bdlBochnerHastingsKomaConst f m0 / (1 + (d r : ℝ) / 2) ^ m0)
  have hε_nn : 0 ≤ ε := by
    dsimp [ε]
    have := bdlBochnerHastingsKomaConst_nonneg hf m0
    positivity
  apply norm_bochnerFilteredOp_w_BH11_sub_condExp_le_of_Icc_pi H_s O_X B hε_nn
  intro t ht
  rw [hHs_eq]
  have hm0_nn : (0 : ℝ) ≤ (m0 : ℝ) := Nat.cast_nonneg m0
  have h_hk := norm_heisenbergFlow_sub_condExp_le_hastings_koma
    H_lat hm0_nn Real.pi_pos.le hX hd_pos h_dist O_X hO_X ht
  rw [Real.rpow_natCast] at h_hk
  have hs1 : H_lat.s1 (m0 : ℝ) ≤ bdlInhomogeneousInterpolatedS1Bound f (m0 : ℝ) :=
    (interpolatedLatticeHamiltonian_s1_inhomogeneous_le mem V hJ0 hJ1 hs_abs hf hV hm0_nn).2
  have h_exp : Real.exp (2 * H_lat.s1 (m0 : ℝ) * Real.pi) - 1 ≤
      Real.exp (2 * bdlInhomogeneousInterpolatedS1Bound f (m0 : ℝ) * Real.pi) - 1 := by
    have h_mul : 2 * H_lat.s1 (m0 : ℝ) * Real.pi ≤
        2 * bdlInhomogeneousInterpolatedS1Bound f (m0 : ℝ) * Real.pi := by
      have := Real.pi_pos.le; nlinarith
    linarith [Real.exp_le_exp.mpr h_mul]
  have h_denom_pos : (0 : ℝ) < (1 + (d r : ℝ) / 2) ^ m0 := by positivity
  calc ‖heisenbergFlow H_lat.totalHamiltonian t O_X -
        condExp (UniformSite3D L (CodeSlotConfig qCodeBDL)) B
          (heisenbergFlow H_lat.totalHamiltonian t O_X)‖
    _ ≤ 2 * ‖O_X‖ * (X.card : ℝ) *
          ((Real.exp (2 * H_lat.s1 (m0 : ℝ) * Real.pi) - 1) / (1 + (d r : ℝ) / 2) ^ m0) := h_hk
    _ = ((X.card : ℝ) * ‖O_X‖) *
          ((2 * (Real.exp (2 * H_lat.s1 (m0 : ℝ) * Real.pi) - 1)) /
            (1 + (d r : ℝ) / 2) ^ m0) := by ring
    _ ≤ ((X.card : ℝ) * ‖O_X‖) *
          (bdlBochnerHastingsKomaConst f m0 / (1 + (d r : ℝ) / 2) ^ m0) := by
      refine mul_le_mul_of_nonneg_left ?_ (by positivity)
      unfold bdlBochnerHastingsKomaConst
      exact div_le_div_of_nonneg_right (by linarith) (le_of_lt h_denom_pos)
    _ = ε := rfl

/-- Tail sum $j \mapsto 2 \sum'_{q : \mathbb{N}} \text{if } r_{\mathrm{cut}}(j) < q \text{ then } f(q) \text{ else } 0$
    belongs to `IsSuperpolynomialDecay` whenever $j \le c \cdot (r_{\mathrm{cut}}(j) + 1)$ eventually. -/
theorem isSuperpolynomialDecay_two_mul_tsum_tail {f : ℕ → ℝ} (hf : IsSuperpolynomialDecay f)
    {r_cut : ℕ → ℕ} (h_cut : ∃ c : ℕ, 1 ≤ c ∧ ∀ᶠ j in atTop, j ≤ c * (r_cut j + 1)) :
    IsSuperpolynomialDecay (fun j => 2 * ∑' q : ℕ, if r_cut j < q then f q else 0) := by
  refine ⟨fun j => mul_nonneg zero_le_two
    (tsum_nonneg fun q => by split_ifs <;> [exact hf.1 q; exact le_rfl]), fun n => ?_⟩
  rcases h_cut with ⟨c, hc1, h_ev⟩
  have h_sum : Summable (fun q : ℕ => (q : ℝ) ^ (n + 1) * f q) :=
    summable_pow_mul_of_isSuperpolynomialDecay hf (n + 1)
  let S : ℝ := ∑' q : ℕ, (q : ℝ) ^ (n + 1) * f q
  let M_const : ℝ := 2 * (c : ℝ) ^ (n + 1) * S
  have h_zero : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 0) := tendsto_const_nhds
  have h_upper : Tendsto (fun j : ℕ => M_const * (j : ℝ)⁻¹) atTop (𝓝 0) := by
    simpa using (tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop).const_mul M_const
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' h_zero h_upper
    (Eventually.of_forall fun j => mul_nonneg (pow_nonneg (Nat.cast_nonneg j) n)
      (mul_nonneg zero_le_two (tsum_nonneg fun q => by split_ifs <;> [exact hf.1 q; exact le_rfl]))) ?_
  filter_upwards [h_ev, eventually_ge_atTop 1] with j hj_c hj1
  have hj_pos : (0 : ℝ) < (j : ℝ) := Nat.cast_pos.mpr hj1
  have hj_ne : (j : ℝ) ≠ 0 := ne_of_gt hj_pos
  let g_j : ℕ → ℝ := fun q => if r_cut j < q then f q else 0
  have hg_nn : ∀ q, 0 ≤ g_j q := fun q => by dsimp [g_j]; split_ifs <;> [exact hf.1 q; exact le_rfl]
  have hg_sum : Summable g_j := Summable.of_nonneg_of_le hg_nn
    (fun q => by dsimp [g_j]; split_ifs <;> [exact le_rfl; exact hf.1 q])
    (summable_of_isSuperpolynomialDecay hf)
  have h_term : ∀ q : ℕ, (j : ℝ) ^ (n + 1) * g_j q ≤
      (c : ℝ) ^ (n + 1) * ((q : ℝ) ^ (n + 1) * f q) := by
    intro q
    dsimp [g_j]
    split_ifs with hq
    · have hj_le_cq : (j : ℝ) ≤ (c : ℝ) * (q : ℝ) := by
        have h_nat : j ≤ c * q := le_trans hj_c (Nat.mul_le_mul_left c hq)
        exact_mod_cast h_nat
      calc (j : ℝ) ^ (n + 1) * f q
        _ ≤ ((c : ℝ) * (q : ℝ)) ^ (n + 1) * f q :=
          mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (Nat.cast_nonneg j) hj_le_cq (n + 1)) (hf.1 q)
        _ = (c : ℝ) ^ (n + 1) * ((q : ℝ) ^ (n + 1) * f q) := by rw [mul_pow, mul_assoc]
    · rw [mul_zero]
      exact mul_nonneg (by positivity) (mul_nonneg (by positivity) (hf.1 q))
  have h_tsum : (j : ℝ) ^ (n + 1) * (∑' q : ℕ, g_j q) ≤ (c : ℝ) ^ (n + 1) * S := by
    rw [← tsum_mul_left]
    calc ∑' q : ℕ, (j : ℝ) ^ (n + 1) * g_j q
      _ ≤ ∑' q : ℕ, (c : ℝ) ^ (n + 1) * ((q : ℝ) ^ (n + 1) * f q) :=
        Summable.tsum_le_tsum h_term (hg_sum.mul_left _) (h_sum.mul_left _)
      _ = (c : ℝ) ^ (n + 1) * S := tsum_mul_left
  have h_id : (j : ℝ) ^ n * (2 * ∑' q : ℕ, g_j q) =
      2 * (j : ℝ)⁻¹ * ((j : ℝ) ^ (n + 1) * ∑' q : ℕ, g_j q) := by
    have h_jn : (j : ℝ) ^ (n + 1) = (j : ℝ) * (j : ℝ) ^ n := by rw [pow_succ']
    have h1 : (j : ℝ)⁻¹ * (j : ℝ) ^ (n + 1) = (j : ℝ) ^ n := by
      rw [h_jn, inv_mul_cancel_left₀ hj_ne]
    calc (j : ℝ) ^ n * (2 * ∑' q : ℕ, g_j q)
      _ = ((j : ℝ)⁻¹ * (j : ℝ) ^ (n + 1)) * (2 * ∑' q : ℕ, g_j q) := by rw [h1]
      _ = 2 * (j : ℝ)⁻¹ * ((j : ℝ) ^ (n + 1) * ∑' q : ℕ, g_j q) := by ring
  calc (j : ℝ) ^ n * (2 * ∑' q : ℕ, g_j q)
    _ = 2 * (j : ℝ)⁻¹ * ((j : ℝ) ^ (n + 1) * ∑' q : ℕ, g_j q) := h_id
    _ ≤ 2 * (j : ℝ)⁻¹ * ((c : ℝ) ^ (n + 1) * S) :=
      mul_le_mul_of_nonneg_left h_tsum (by positivity)
    _ = M_const * (j : ℝ)⁻¹ := by dsimp [M_const]; ring

end
