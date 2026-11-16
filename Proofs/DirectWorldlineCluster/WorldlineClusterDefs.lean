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
import Defs.KMSAndGibbs
import Defs.SuperpolyDecay
import Defs.FlowAndFilter
import Defs.SafeSubspaceAndKMS
import Proofs.SpacetimeWorldlineKP.SpacetimeKoteckyPreissRatio

/-!
# Direct Worldline Monomer-Polymer Gas, Ursell Functions, and QAC-Dressed Safe Systems

Defines super-polynomial, stretched-exponential, and finite-range perturbation classes (`InPerturbationClassSuper`, `InPerturbationClassStretch`, `InPerturbationClassFin`), scale-split truncations (`scaleSplitTruncatedOp`, `scaleSplitTailOp`), and native-scale worldline Kotecky-Preiss thresholds (`worldlineNativeKPSum`, `worldlineSpanningThreshold`, `scaleSplitMasterUpperBound`). Formalizes spacetime worldline monomers and overlap adjacency (`WorldlineMonomer`, `WorldlineMonomerAdj`), Penrose/Ursell polymer systems (`UrsellPolymerSystem`, `ursellConnectedWeight`), and QAC-dressed crossover systems (`IsQACDressedSafeSystem`, `qacDressedGibbsUpperBound`).

## References

* Part II, Section 2 (`subsec:setup`), Definition 2.3 (`def:perturbation-class`), Definition 2.5 (`def:syndrome-safe`)
* Part II, Section 3.5 (`subsec:worldline-expansion`), Lemma 3.9 (`lem:worldline-factorization-time-reversal`), Proposition 3.10 (`prop:tube-local-ursell-erasure`)
* Part II, Section 5.1 (`subsec:direct-worldline-synthesis`), Theorem 5.1 (`thm:direct-worldline-intact-cluster-erasure`), Section 5.2 (`subsec:low-temp-crossover`), Theorem 5.3 (`thm:low-temperature-window-and-crossover`)
-/

noncomputable section

open scoped Classical BigOperators InnerProduct ComplexConjugate
open ContinuousLinearMap PerturbedThermalBarrier SpacetimeWorldlineKP

namespace DirectWorldlineCluster

instance instNonemptyCodeSlotConfig (q_code : ℕ) : Nonempty (CodeSlotConfig q_code) :=
  ⟨fun _ => false⟩

instance instNonemptyUniformSite3DCodeSlotConfig (L q_code : ℕ) (x : Box3D L) :
    Nonempty (UniformSite3D L (CodeSlotConfig q_code) x) :=
  ⟨fun _ => false⟩

local notation "ℋ[" L ", " Site0 "]" => ManyBodyHilbertSpace (UniformSite3D L Site0)
local notation "ℬ[" L ", " Site0 "]" => ℋ[L, Site0] →L[ℂ] ℋ[L, Site0]
local notation "ℋ_CP[" L ", " Site0 ", " N_checks "]" =>
  IndexedCommutingProjectorHamiltonian 3 L (UniformSite3D L Site0) (Fin N_checks)
local notation "𝒱_pert[" L ", " Site0 "]" =>
  QuasiLocalPerturbation 3 L (UniformSite3D L Site0)

/-!
## 1. Perturbation Decay Classes $\mathcal{D}_{\mathrm{fin}}(r_{\mathrm{pert}}) \subset \mathcal{D}_{\mathrm{stretch}}(\alpha,\mu_0) \subset \mathcal{D}_{\mathrm{super}}$
(Part II, Section 2 (`subsec:setup`), Definition 2.3 (`def:perturbation-class`) & Lemma 2.4 (`lem:D-super-closure`))
-/

/-- Active check footprint bound $N_{\max}(r) = c_{\mathrm{chk}} (r + r_0)^3$
    (Part II, Definition 2.3 (`def:perturbation-class`), Equation (12) (`eq:Nmax-r-def`)). -/
def activeCheckFootprintBound (c_chk r_0 r : ℕ) : ℕ :=
  c_chk * (r + r_0) ^ 3

/-- RCA1 collar reconstruction radius $R_{\mathrm{RCA}}(r) = \lceil C_{\mathrm{RCA}} \max(r, r_0)\rceil$
    (Part II, Definition 2.2 (`def:RCA`), Equation (6) (`eq:dilated-collar-Bplus`)). -/
def rcaCollarRadius (C_RCA : ℝ) (r_0 r : ℕ) : ℕ :=
  Nat.ceil (C_RCA * (max r r_0 : ℝ))

/-- $p$-th polynomial moment bound $\|f\|_{(p)} = \sup_{r \ge 0} (1+r)^p f(r) \le M_p$
    (Part II, Definition 2.3 (`def:perturbation-class`), Equation (9) (`eq:D-super-seminorms`)). -/
def HasDecayMomentBound (f : ℕ → ℝ) (p : ℕ) (M_p : ℝ) : Prop :=
  (∀ r : ℕ, 0 ≤ f r) ∧ f 0 = 1 ∧
  ∀ r : ℕ, ((1 + (r : ℝ)) ^ p) * f r ≤ M_p

/-- Class $\mathcal{D}_{\mathrm{super}}$ (Part II, Definition 2.3 (`def:perturbation-class`), Equation (9) (`eq:D-super-seminorms`)):
    non-increasing decay profile $f : \mathbb{N} \to [0,\infty)$ with $f(0) = 1$ and finite $p$-th polynomial moments for all $p \in \mathbb{N}$. -/
def InPerturbationClassSuper (f : ℕ → ℝ) : Prop :=
  (∀ r : ℕ, 0 ≤ f r) ∧
  (∀ r s : ℕ, r ≤ s → f s ≤ f r) ∧
  f 0 = 1 ∧
  ∀ p : ℕ, ∃ M_p : ℝ, 0 ≤ M_p ∧ HasDecayMomentBound f p M_p

/-- Class $\mathcal{D}_{\mathrm{stretch}}(\alpha, \mu_0)$ (Part II, Definition 2.3 (`def:perturbation-class`)):
    stretched-exponential decay profile $f(r) \le C_{\mathrm{stretch}} \exp(-\mu_0 r^\alpha)$ with $\alpha > 0, \mu_0 > 0$. -/
def InPerturbationClassStretch (f : ℕ → ℝ) (α μ_0 C_stretch : ℝ) : Prop :=
  InPerturbationClassSuper f ∧
  0 < α ∧ 0 < μ_0 ∧ 1 ≤ C_stretch ∧
  ∀ r : ℕ, f r ≤ C_stretch * Real.exp (-μ_0 * ((r : ℝ) ^ α))

/-- Class $\mathcal{D}_{\mathrm{fin}}(r_{\mathrm{pert}})$ (Part II, Definition 2.3 (`def:perturbation-class`)):
    strictly finite-range decay profile with $f(r) = 0$ for all $r > r_{\mathrm{pert}}$. -/
def InPerturbationClassFin (f : ℕ → ℝ) (r_pert : ℕ) : Prop :=
  InPerturbationClassSuper f ∧
  ∀ r : ℕ, r_pert < r → f r = 0

/-- Tail sum $F_f(R_{\mathrm{cut}}) = \sum_{r > R_{\mathrm{cut}}} f(r)$
    (Part II, Definition 2.3 (`def:perturbation-class`) and Lemma 2.4 (`lem:D-super-closure`), Equation (15) (`eq:tail-sum-seminorm`)). -/
def perturbationTailSeries (f : ℕ → ℝ) (R_cut : ℕ) : ℝ :=
  ∑' r : ℕ, if R_cut < r then f r else 0

/-- Basis-free RCA1 collar constant $\Delta_{\mathrm{RCA}}(f) = \sum_{r=0}^\infty f(r) N_{\max}(R_{\mathrm{RCA}}(r))$
    (Part II, Definition 2.3 (`def:perturbation-class`), Equation (13) (`eq:Delta-RCA-def`)). -/
def rcaCollarSeries (f : ℕ → ℝ) (c_chk r_0 : ℕ) (C_RCA : ℝ) : ℝ :=
  ∑' r : ℕ, f r * (activeCheckFootprintBound c_chk r_0 (rcaCollarRadius C_RCA r_0 r) : ℝ)

/-- The finite-range RCA collar sum up to cutoff `L_star`:
    `\sum_{r=1}^{L^*} f(r) N_{chk}(R_{RCA}(r))`
    (Part II, Definition 2.3 (`def:perturbation-class`), Equation (13) (`eq:Delta-RCA-def`)). -/
def rcaCollarFiniteSum (f : ℕ → ℝ) (c_chk r_0 L_star : ℕ) (C_RCA : ℝ) : ℝ :=
  ∑ r ∈ Finset.Icc 1 L_star,
    f r * (activeCheckFootprintBound c_chk r_0 (rcaCollarRadius C_RCA r_0 r) : ℝ)

/-- Envelope constant $C_{\mathrm{col}} = c_{\mathrm{chk}} (C_{\mathrm{RCA}} r_0 + r_0 + 1)^3$ in
    Part II, Lemma 2.4 (`lem:D-super-closure`), accounting for $\max(r, r_0) \le r_0 (1 + r)$ at $r = 0$. -/
def rcaCollarEnvelopeConst (c_chk r_0 : ℕ) (C_RCA : ℝ) : ℝ :=
  (c_chk : ℝ) * (C_RCA * (r_0 : ℝ) + (r_0 : ℝ) + 1) ^ 3

/-!
## 2. Scale-Split Perturbation $V = V^{\le R_{\mathrm{cut}}} + V^{> R_{\mathrm{cut}}}$ & Thermodynamic Thresholds
(Part II, Section 6.3 (`subsec:main-theorems`), Section 3 (`sec:foundations`), and Section 5 (`sec:worldline-synthesis`))
-/

/-- Truncated perturbation $V^{\le R_{\mathrm{cut}}} = \sum_{1 \le r \le \min(R_{\mathrm{cut}}, L)} \sum_{A \in \mathrm{BoxCubes}(L,r)} V_{r,A}$
    (Part II, Section 3.5 (`subsec:worldline-expansion`), Equation (54) (`eq:H-short-split-def`)). -/
def scaleSplitTruncatedOp {D L : ℕ} {Site : BoxD D L → Type}
    [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    (V : QuasiLocalPerturbation D L Site) (R_cut : ℕ) :
    ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site :=
  ∑ r ∈ Finset.Icc 1 (min R_cut L), ∑ A ∈ boxCubes D L r, V.term r A

/-- Tail perturbation $V^{> R_{\mathrm{cut}}} = \sum_{R_{\mathrm{cut}} < r \le L} \sum_{A \in \mathrm{BoxCubes}(L,r)} V_{r,A}$
    (Part II, Section 3.5 (`subsec:worldline-expansion`), Equation (54) (`eq:H-short-split-def`)). -/
def scaleSplitTailOp {D L : ℕ} {Site : BoxD D L → Type}
    [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    (V : QuasiLocalPerturbation D L Site) (R_cut : ℕ) :
    ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site :=
  ∑ r ∈ (Finset.Icc 1 L).filter (fun r => R_cut < r), ∑ A ∈ boxCubes D L r, V.term r A

/-- Local syndrome-off-diagonal jump term $V_{r,A}^{\mathrm{off}} = V_{r,A} - \mathcal{P}_{\mathrm{diag}}(V_{r,A})$
    (Part II, Proposition 3.4 (`prop:pauli-diag-off`), Equation (35) (`eq:V-off-jump-decomp`)). -/
def pauliOffDiagonalTerm {D L : ℕ} {Site : BoxD D L → Type}
    [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (sys : IndexedCommutingProjectorHamiltonian D L Site ι)
    (V : QuasiLocalPerturbation D L Site) (r : ℕ) (A : Finset (BoxD D L)) :
    ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site :=
  V.term r A - syndromePinchOp sys (V.term r A)

/-- Quasi-local perturbation norm bound $\|V_{r,A}\| \le J f(r)$ and $\sum_{A \in \mathcal{B}_r} \|V_{r,A}\| \le J L^3 f(r)$
    (Part II, Definition 2.3 (`def:perturbation-class`), Equation (11) (`eq:VrA-norm-bound`)). -/
def HasQuasiLocalDecayBound {D L : ℕ} {Site : BoxD D L → Type}
    [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    (V : QuasiLocalPerturbation D L Site) (J : ℝ) (f : ℕ → ℝ) : Prop :=
  (∀ r ∈ Finset.Icc 1 L, ∀ A ∈ boxCubes D L r,
    IsSelfAdjoint (V.term r A) ∧ ‖V.term r A‖ ≤ J * f r) ∧
  (∀ r ∈ Finset.Icc 1 L,
    (∑ A ∈ boxCubes D L r, ‖V.term r A‖) ≤ J * ((L ^ D : ℕ) : ℝ) * f r)

/-- Klarner lattice animal constant $K_{\mathrm{Klarner}} = 28512 \, e$
    (Part II, Lemma 3.3 (`lem:klarner-bound`), Equation (29) (`eq:klarner-rooted`)). -/
def klarnerAnimalConst : ℝ :=
  28512 * Real.exp 1

/-- Critical inverse temperature $\beta_c^{\mathrm{hier}} = \frac{\ln K_{\mathrm{Klarner}} + 2}{\frac{3}{2} \Delta_0}$
    (Part II, Theorem 6.3 (`thm:main-A`) and Theorem 5.1 (`thm:direct-worldline-intact-cluster-erasure`)). -/
def criticalInverseTempHier (Δ_0 : ℝ) : ℝ :=
  (Real.log klarnerAnimalConst + 2) / ((3 / 2 : ℝ) * Δ_0)

/-- Diagonal and worldline RCA coupling threshold $J_{\mathrm{wl}}(f) = \frac{\Delta_0}{16 \Delta_{\mathrm{RCA}}(f)}$
    (Part II, Proposition 3.10 (`prop:tube-local-ursell-erasure`), Equation (62) (`eq:J-span-full-def`)). -/
def worldlineCouplingThreshold (Δ_0 Δ_RCA : ℝ) : ℝ :=
  Δ_0 / (16 * Δ_RCA)

/-- Native-scale worldline Kotecký–Preiss scale sum $\Sigma_{\mathrm{nat}}(R_{\mathrm{cut}}, \beta; f)$
    (Part II, Proposition 3.10 (`prop:tube-local-ursell-erasure`), Equation (61) (`eq:Sigma-nat-def`)):
    $$\Sigma_{\mathrm{nat}}(R_{\mathrm{cut}}, \beta; f) = \sum_{r=1}^{R_{\mathrm{cut}}} C_{\mathrm{wl}} r^6 f(r) \exp\bigl(c_{\mathrm{wl}}(1 + \beta) r^3\bigr).$$ -/
def worldlineNativeKPSum (f : ℕ → ℝ) (C_wl c_wl β : ℝ) (R_cut : ℕ) : ℝ :=
  ∑ r ∈ Finset.Icc 1 R_cut,
    C_wl * ((r : ℝ) ^ 6) * f r * Real.exp (c_wl * (1 + β) * ((r : ℝ) ^ 3))

/-- Native-scale worldline coupling threshold $J_{\mathrm{span}}(R_{\mathrm{cut}}, \beta; f)$
    (Part II, Proposition 3.10 (`prop:tube-local-ursell-erasure`), Equation (62) (`eq:J-span-full-def`)):
    $$J_{\mathrm{span}}(R_{\mathrm{cut}}, \beta; f) = \min\Bigl\{\frac{1}{16 \Delta_{\mathrm{RCA}}(f)},\; \frac{1}{64 e \max(1, \beta) \Sigma_{\mathrm{nat}}(R_{\mathrm{cut}}, \beta; f)}\Bigr\}.$$ -/
def worldlineSpanningThreshold (Δ_RCA C_wl c_wl β : ℝ) (f : ℕ → ℝ) (R_cut : ℕ) : ℝ :=
  min (1 / (16 * Δ_RCA))
    (1 / (64 * Real.exp 1 * max 1 β * worldlineNativeKPSum f C_wl c_wl β R_cut))

/-- Worldline cluster Peierls exponent $\gamma_{\mathrm{wl}}(\beta, J) = c_{\mathrm{wt}} [\beta(2\Delta_0 - 6 J \Delta_{\mathrm{RCA}}(f)) - \ln K_{\mathrm{Klarner}} - 1]$. -/
def worldlineSuppressionRate (c_wt Δ_0 Δ_RCA β J : ℝ) : ℝ :=
  c_wt * (β * (2 * Δ_0 - 6 * J * Δ_RCA) - Real.log klarnerAnimalConst - 1)

/-- Scale-split master upper bound on $\operatorname{Tr}(\rho_\beta(H)(I - \Pi_{\mathrm{safe}}))$ in
    Part II, Theorem 6.3 (`thm:main-A`), Equation (95) (`eq:main-A-master`):
    $$2 e^{2\beta \varepsilon_{\mathrm{tail}}(R_{\mathrm{cut}}, L_k)} \exp\bigl(-c_{\beta,\mathrm{hier}}(\beta - \beta_c^{\mathrm{hier}}) L_k^{3\eta}\bigr) + \bigl(e^{2\beta \varepsilon_{\mathrm{tail}}(R_{\mathrm{cut}}, L_k)} - 1\bigr),$$
    where $\varepsilon_{\mathrm{tail}}(R_{\mathrm{cut}}, L_k) = C_{\mathrm{vol}} J L_k^3 F_f(R_{\mathrm{cut}})$. -/
def scaleSplitMasterUpperBound
    (L_k : ℕ) (η c_β_hier β β_c_hier C_vol J F_tail : ℝ) : ℝ :=
  let vol := ((L_k ^ 3 : ℕ) : ℝ)
  let ε_tail := C_vol * J * vol * F_tail
  2 * Real.exp (2 * β * ε_tail) * Real.exp (-c_β_hier * (β - β_c_hier) * (vol ^ η)) +
    (Real.exp (2 * β * ε_tail) - 1)

/-- Scale-split probability upper bound $\min(1, \dots)$ in Part II, Theorem 6.3 (`thm:main-A`), Equation (96) (`eq:main-A-bound`). -/
def scaleSplitGibbsUpperBound
    (L_k : ℕ) (η γ_wl β J F_tail : ℝ) : ℝ :=
  let vol := ((L_k ^ 3 : ℕ) : ℝ)
  let tail := 2 * β * vol * J * F_tail
  min 1 (4 * vol * Real.exp (-γ_wl * (vol ^ η) + tail) + tail)

/-- First-order single-jump thermal excitation lower bound (compare Part II, Section 5.2 (`subsec:low-temp-crossover`),
    Theorem 5.3 (`thm:low-temperature-window-and-crossover`), Equation (84) (`eq:exact-T0-lower-bound-proof`)):
    $$\frac{J^2 f(r_K)^2}{16(C_{\mathrm{spec}}|K| + 2 J f(r_K))^2}.$$ -/
def singleJumpThermalLowerBound (J f_rK C_spec K_card : ℝ) : ℝ :=
  (J ^ 2 * f_rK ^ 2) / (16 * (C_spec * K_card + 2 * J * f_rK) ^ 2)

/-- First-order single-jump excitation floor with volume factor. -/
def singleJumpExcitationFloor
    (c_pert β J Δ_0 : ℝ) (L_k : ℕ) (f_R_star : ℝ) : ℝ :=
  c_pert * ((β * J) ^ 2 / ((1 + β * Δ_0) ^ 2)) * (((L_k ^ 3 : ℕ) : ℝ)) * (f_R_star ^ 2)

/-- Low-temperature crossover inverse temperature $\beta_{\max}(J; R_{\mathrm{cut}})$ associated with
    Part II, Proposition 3.10 (`prop:tube-local-ursell-erasure`), Equation (62) (`eq:J-span-full-def`):
    $$\beta_{\max}(J; R_{\mathrm{cut}}) = 2 \beta_c^{\mathrm{hier}} + \frac{1}{c_{\mathrm{wl}} R_{\mathrm{cut}}^3 + 1} \ln\frac{J_{\mathrm{span}}^{\mathrm{hier}}(R_{\mathrm{cut}})}{J}.$$ -/
def lowTempWindowBetaMax (β_c_hier c_wl : ℝ) (R_cut : ℕ) (J_span_hier J : ℝ) : ℝ :=
  2 * β_c_hier + (1 / (c_wl * ((R_cut : ℝ) ^ 3) + 1)) * Real.log (J_span_hier / J)

/-- Low-temperature crossover upper bound $\beta_{\max}(J; R_{\mathrm{cut}})$ (exponential form). -/
def lowTempCrossoverBetaMax
    (c_wt : ℝ) (L_k : ℕ) (η J F_tail : ℝ) : ℝ :=
  Real.exp ((c_wt / 4) * (((L_k ^ 3 : ℕ) : ℝ) ^ η)) / (J * F_tail)

/-- Zero-temperature bare quantum fluctuation floor in Part II,
    Theorem 5.3 (`thm:low-temperature-window-and-crossover`),
    Equation (84) (`eq:exact-T0-lower-bound-proof`):
    $$\max\Bigl\{\Bigl(\frac{J f(r_{\min})}{2 N_{\max}(r_{\min})}\Bigr)^{2 m_{\min}(k)},\; \frac{J^2 f(r_K)^2}{16(|K| + 2 J f(r_K))^2}\Bigr\}.$$ -/
def bareZeroTempFluctuationFloor
    (J f_rmin : ℝ) (N_max_rmin m_min_k : ℕ) (f_rK K_card : ℝ) : ℝ :=
  max ((J * f_rmin / (2 * (N_max_rmin : ℝ))) ^ (2 * m_min_k))
    (singleJumpThermalLowerBound J f_rK 1 K_card)

/-- QAC-dressed two-regime thermal upper bound in Part II, Theorem 6.4(i) (`thm:main-B`),
    Equation (98) (`eq:main-B-dressed`):
    $$\mathbf{1}_{\{\beta \le \beta_{\mathrm{cross}}\}}\Bigl(2 e^{2\beta\delta_{\mathrm{split}}(L_k)} \exp\bigl(-\frac{3}{4} c_{\beta,\mathrm{hier}}(\beta - \tilde{\beta}_c) L_k^{3\eta}\bigr) + (e^{2\beta\delta_{\mathrm{split}}(L_k)} - 1)\Bigr) + \mathbf{1}_{\{\beta > \beta_{\mathrm{cross}}\}} e^{-\frac{3}{8}\beta}.$$ -/
def qacDressedGibbsUpperBound
    (L_k : ℕ) (η c_β_hier β β_tilde_c β_cross δ_split : ℝ) : ℝ :=
  let vol := ((L_k ^ 3 : ℕ) : ℝ)
  if β ≤ β_cross then
    2 * Real.exp (2 * β * δ_split) *
      Real.exp (-(3 / 4 : ℝ) * c_β_hier * (β - β_tilde_c) * (vol ^ η)) +
      (Real.exp (2 * β * δ_split) - 1)
  else
    Real.exp (-(3 / 8 : ℝ) * β)

/-!
## 3. Intact-Cluster Worldline Definitions & Physical System Predicates
(Part II, Section 3.5 (`subsec:worldline-expansion`), Lemma 3.2 (`lem:positive-witness-bound`),
Lemma 3.3 (`lem:klarner-bound`), Lemma 3.9 (`lem:worldline-factorization-time-reversal`),
Proposition 3.10 (`prop:tube-local-ursell-erasure`), Theorem 5.1 (`thm:direct-worldline-intact-cluster-erasure`),
and Theorem 5.3 (`thm:low-temperature-window-and-crossover`))
-/

/-- Connected check-graph witness cover (Part II, Lemma 3.2 (`lem:positive-witness-bound`) &
    Lemma 3.3 (`lem:klarner-bound`), Equation (29) (`eq:klarner-rooted`)):
    `W_cover` is a positive-cone check witness cover for `S_safe` whose elements `W ∈ W_cover`
    are connected animals containing an anchor check `v_0` of size at least `d_min` in a
    symmetric check-overlap graph `adj` of maximum degree `Δ_adj ≤ 168`
    ($\Delta_{\mathrm{adj}}^2 \le 168^2 = 28224 \le 28512 e = K_{\mathrm{Klarner}}$). -/
def IsConnectedCheckWitnessCover {ι_chk : Type} [Fintype ι_chk] [DecidableEq ι_chk]
    (adj : ι_chk → ι_chk → Prop) [DecidableRel adj]
    (S_safe : Finset (ι_chk → Bool)) (W_cover : Finset (Finset ι_chk))
    (v_0 : ι_chk) (Δ_adj d_min : ℕ) : Prop :=
  IsPositiveCheckWitnessCover S_safe W_cover ∧
  (∀ u v : ι_chk, adj u v → adj v u) ∧
  Δ_adj ≤ 168 ∧
  (∀ u : ι_chk, (Finset.univ.filter (fun v => adj u v)).card ≤ Δ_adj) ∧
  ∀ W ∈ W_cover, d_min ≤ W.card ∧ v_0 ∈ W ∧ KPIsConnectedSubgraph adj W

/-- Single-logical-qubit Pauli character group $\mathbb{F}_2^2$
    (Part II, Lemma 3.9 (`lem:worldline-factorization-time-reversal`) and
    Proposition 3.10 (`prop:tube-local-ursell-erasure`)). -/
abbrev LogicalPauliChar : Type := ZMod 2 × ZMod 2

/-- Symplectic character sign $(-1)^{\langle \nu, \mu\rangle} \in \{\pm 1\}$ on $\mathbb{F}_2^2$
    (Part II, Proposition 3.10 (`prop:tube-local-ursell-erasure`), Equation (63) (`eq:ursell-partition-sigma`)). -/
def logicalCharSign (ν μ : LogicalPauliChar) : ℝ :=
  (-1 : ℝ) ^ (ν.1 * μ.1 + ν.2 * μ.2).val

/-- Character-twisted polymer weight $w_\nu(\gamma; \sigma) = (-1)^{\langle \nu, \mu(\gamma)\rangle} w_{\mathrm{micro}}(\gamma; \sigma)$
    (Part II, Proposition 3.10 (`prop:tube-local-ursell-erasure`), Equation (63) (`eq:ursell-partition-sigma`)). -/
def characterTwistedPolymerWeight {ι_poly : Type*}
    (w_micro : ι_poly → ℝ) (μ : ι_poly → LogicalPauliChar) (ν : LogicalPauliChar) (γ : ι_poly) : ℝ :=
  logicalCharSign ν (μ γ) * w_micro γ

/-- Unmerged native collar support $\overline{\mathcal{C}}(\gamma) := \bigcup_{x \in \gamma} \mathcal{C}(A_x^+)$
    for any worldline polymer $\gamma$, both microscopic and macroscopic without merging
    (Part II, Lemma 3.9 (`lem:worldline-factorization-time-reversal`), Equation (60) (`eq:C-bar-span-def`),
    and Proposition 3.10 (`prop:tube-local-ursell-erasure`)). -/
def nativeCollarSupport {ι_mon ι_chk : Type*} [DecidableEq ι_chk]
    (collarChecks : ι_mon → Finset ι_chk) (γ : Finset ι_mon) : Finset ι_chk :=
  γ.biUnion collarChecks

/-- Worldline polymer size weight $a(\gamma) := \sum_{x \in \gamma} \frac{1}{8}|\mathcal{C}(A_x^+)|$
    (Part II, Proposition 3.10 (`prop:tube-local-ursell-erasure`), Equation (64) (`eq:touching-ursell-bound`)). -/
def worldlinePolymerSize {ι_mon ι_chk : Type*}
    (collarChecks : ι_mon → Finset ι_chk) (γ : Finset ι_mon) : ℝ :=
  ∑ x ∈ γ, (1 / 8 : ℝ) * ((collarChecks x).card : ℝ)

/-- Prüfer spanning-tree root-sum degree identity (Part II, Proposition 3.10 (`prop:tube-local-ursell-erasure`)):
    for any out-degree sequence $d_1, \dots, d_n$ on $n = m + 2$ monomers with $\sum_{i=1}^n d_i = n - 1 = m + 1$,
    summing the rooted Prüfer count $d_i (n - 2)! = d_i m!$ over all $n$ root choices yields $(n - 1)! = (m + 1)!$. -/
def pruferRootedTreeDegreeSum {m : ℕ} (d_deg : Fin (m + 2) → ℕ) : ℕ :=
  ∑ i : Fin (m + 2), d_deg i * Nat.factorial m

/-- Spacetime worldline monomer `(slice, r, A)` (Part II, Section 3.5 (`subsec:worldline-expansion`)):
    discrete imaginary-time slice index `slice : Fin N_slices`, spatial interaction scale `r : ℕ`,
    and spatial box `A : Finset (Box3D L)`. -/
structure WorldlineMonomer (L N_slices : ℕ) where
  slice : Fin N_slices
  r : ℕ
  A : Finset (Box3D L)
  deriving DecidableEq

/-- Spacetime worldline polymer (Part II, Section 3.5 (`subsec:worldline-expansion`)):
    finite set of spacetime worldline monomers. -/
abbrev WorldlinePolymer (L N_slices : ℕ) : Type :=
  Finset (WorldlineMonomer L N_slices)

/-- Periodic circle distance between discrete imaginary-time slices
    (Part II, Section 3.5 (`subsec:worldline-expansion`)). -/
def periodicSliceDist {N_slices : ℕ} (s₁ s₂ : Fin N_slices) : ℕ :=
  min ((s₁.val + N_slices - s₂.val) % N_slices) ((s₂.val + N_slices - s₁.val) % N_slices)

/-- Worldline monomer adjacency (Part II, Section 3.5 (`subsec:worldline-expansion`) &
    Proposition 3.10 (`prop:tube-local-ursell-erasure`)):
    two monomers are adjacent if their RCA1 collar check sets overlap and their imaginary-time slices
    are within periodic distance $1$ on the thermal circle. -/
def WorldlineMonomerAdj {L N_slices : ℕ} {ι_chk : Type*} [DecidableEq ι_chk]
    (collarChecks : WorldlineMonomer L N_slices → Finset ι_chk)
    (x y : WorldlineMonomer L N_slices) : Prop :=
  ¬Disjoint (collarChecks x) (collarChecks y) ∧ periodicSliceDist x.slice y.slice ≤ 1

/-- Abstract Penrose tree-graph / Ursell connected weight $\phi^T(\gamma) \prod_{x \in \gamma} w(x)$
    for a finite worldline polymer $\gamma$ (Part II, Lemma 3.9 (`lem:worldline-factorization-time-reversal`) &
    Proposition 3.10 (`prop:tube-local-ursell-erasure`)). -/
structure UrsellPolymerSystem (L N_slices : ℕ) (ι_chk : Type*) [DecidableEq ι_chk] where
  collarChecks : WorldlineMonomer L N_slices → Finset ι_chk
  monomerActivity : WorldlineMonomer L N_slices → ℝ
  ursellPhiT : WorldlinePolymer L N_slices → ℝ

/-- Connected Ursell polymer weight $w^{\mathrm{Ursell}}(\gamma) = \phi^T(\gamma) \prod_{x \in \gamma} z(x)$
    (Part II, Lemma 3.9 (`lem:worldline-factorization-time-reversal`) &
    Proposition 3.10 (`prop:tube-local-ursell-erasure`), Equation (63) (`eq:ursell-partition-sigma`)). -/
def ursellConnectedWeight {L N_slices : ℕ} {ι_chk : Type*} [DecidableEq ι_chk]
    (U : UrsellPolymerSystem L N_slices ι_chk) (γ : WorldlinePolymer L N_slices) : ℝ :=
  U.ursellPhiT γ * ∏ x ∈ γ, U.monomerActivity x

/-- Spatial diameter of the unmerged collar support of a worldline polymer
    (Part II, Section 3.5 (`subsec:worldline-expansion`), Lemma 3.9 (`lem:worldline-factorization-time-reversal`)). -/
def worldlinePolymerSpatialDiameter {L N_slices : ℕ}
    (γ : WorldlinePolymer L N_slices) : ℕ :=
  (γ ×ˢ γ).sup fun p =>
    (p.1.A ×ˢ p.2.A).sup fun q => boxDist q.1 q.2

/-- Microscopic worldline polymer predicate (Part II, Section 3.5 (`subsec:worldline-expansion`),
    Lemma 3.9 (`lem:worldline-factorization-time-reversal`)):
    contractible on the open spatial box and thermal circle with spatial diameter $\le L^*/2$ and zero winding. -/
def IsMicroscopicWorldlinePolymer {L N_slices : ℕ}
    (L_star : ℕ) (winding : WorldlinePolymer L N_slices → ℤ)
    (γ : WorldlinePolymer L N_slices) : Prop :=
  winding γ = 0 ∧ 2 * worldlinePolymerSpatialDiameter γ ≤ L_star

/-- Macroscopic worldline polymer predicate (Part II, Section 3.5 (`subsec:worldline-expansion`),
    Lemma 3.9 (`lem:worldline-factorization-time-reversal`)):
    non-zero winding or spatial diameter $> L^*/2$. -/
def IsMacroscopicWorldlinePolymer {L N_slices : ℕ}
    (L_star : ℕ) (winding : WorldlinePolymer L N_slices → ℤ)
    (γ : WorldlinePolymer L N_slices) : Prop :=
  winding γ ≠ 0 ∨ L_star < 2 * worldlinePolymerSpatialDiameter γ

/-- QAC-dressed crossover parameter bundle (Part II, Section 5.2 (`subsec:low-temp-crossover`),
    Theorem 5.3 (`thm:low-temperature-window-and-crossover`), and Theorem 6.4(i) (`thm:main-B`),
    Equation (98) (`eq:main-B-dressed`)) recording positive coupling/gap scales `g_0, g_eff`,
    critical and crossover inverse temperatures `0 < β_tilde_c < β_cross`, and non-negative
    ground-band splitting `0 ≤ δ_split`. -/
structure IsQACDressedSafeSystem (g_0 g_eff β_tilde_c β_cross δ_split : ℝ) : Prop where
  g_0_pos : 0 < g_0
  g_eff_pos : 0 < g_eff
  β_tilde_c_pos : 0 < β_tilde_c
  β_tilde_c_le_cross : β_tilde_c < β_cross
  δ_split_nonneg : 0 ≤ δ_split

end DirectWorldlineCluster

end
