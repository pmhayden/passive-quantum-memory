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

import Proofs.BandLimitedFilter.BandLimitedFilterSynthesis
import Proofs.QuasiLocalDressing.UnfilteredMultiScaleFlowWitnesses
import Proofs.TwoAxisMemorySynthesis.UniformCouplingThreshold

open scoped Classical InnerProduct ComplexConjugate BigOperators
open Filter Topology Asymptotics ContinuousLinearMap KMSPinchedGibbs PerturbedThermalBarrier
open WeldedHierarchy WeldedHierarchy.BDLDecoder InhomogeneousMemoryChallenge

noncomputable section

set_option maxRecDepth 200000
set_option maxHeartbeats 800000

/-!
# Site Check Operator Supports and Total-Perturbation Commutator Bounds

Establishes `collarConstRCABDL` positivity (`one_le_collar_const_rca_bdl_twoBlock`), full-box support of `siteCheckOp` (`isSupportedOn_siteCheckOp_univ`), and $O(J)$ commutator norm bounds for `opCommutator V.totalPerturbation (sys.siteCheckOp u)` (`norm_opCommutator_V_tot_siteCheckOp_le_J_mul`) from interaction decay bounds.

## References

* Part I, Section 6.2 (`subsec:bochner-lr`), Proposition 6.3 (`prop:bochner-time-convolution`)
* Part I, Section 6.3 (`subsec:qac-block-diag`), Proposition 6.4 (`prop:qac-block-diagonalization`)
-/

lemma one_le_collar_const_rca_bdl_twoBlock : (1 : ℝ) ≤ (collarConstRCABDL : ℝ) := by
  dsimp [collarConstRCABDL, bBDL, bdlLambda]; norm_num

/-! ## 1. Site Check Operator Support and $O(J)$ Commutator Bounds -/

/-- Every site check operator `sys.siteCheckOp u` is supported on `Finset.univ`. -/
theorem isSupportedOn_siteCheckOp_univ {D L : ℕ} [NeZero L]
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (sys : IndexedCommutingProjectorHamiltonian D L Site ι) (u : BoxD D L) :
    IsSupportedOn Site Finset.univ (sys.siteCheckOp u) := by
  unfold IndexedCommutingProjectorHamiltonian.siteCheckOp
  refine isSupportedOn_finset_sum Finset.univ _ _ fun i _ => ?_
  exact isSupportedOn_smul Finset.univ (sys.weight i : ℂ)
    (_root_.isSupportedOn_mono (Finset.subset_univ (sys.support i)) (sys.is_supported i))

/-- Explicit $O(J)$ commutator bound `‖opCommutator V.V_tot (sys.siteCheckOp u)‖ ≤ J * S_Q`
    from `V.SatisfiesDecayBound J f`. -/
theorem norm_opCommutator_V_tot_siteCheckOp_le_J_mul {D L : ℕ} [NeZero L]
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (sys : IndexedCommutingProjectorHamiltonian D L Site ι)
    (V : QuasiLocalPerturbation D L Site) {J : ℝ} {f : ℕ → ℝ}
    (hV_dec : V.SatisfiesDecayBound J f) (u : BoxD D L) :
    ‖opCommutator V.totalPerturbation (sys.siteCheckOp u)‖ ≤
      J * (2 * ‖sys.siteCheckOp u‖ * siteOverlapCommutatorFactor D L Finset.univ f) := by
  have h1 := norm_opCommutator_V_tot_localOp_le V hV_dec u (isSupportedOn_siteCheckOp_univ sys u)
  linarith

end
