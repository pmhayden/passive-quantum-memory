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

import Proofs.BandLimitedFilter.AnchoredSitePerturbationOps
import Proofs.TwoBlockDecomposition.SitePerturbationNormsAndEnvelopes
import Proofs.CenteredBallBHM.QACTailPinchedCommutators

open scoped Classical InnerProduct ComplexConjugate BigOperators
open Filter Topology Asymptotics ContinuousLinearMap PerturbedThermalBarrier
open WeldedHierarchy WeldedHierarchy.BDLDecoder InhomogeneousMemoryChallenge

noncomputable section

set_option maxRecDepth 200000
set_option maxHeartbeats 800000

/-!
# Volume-Independent Perturbation Coupling Threshold Calibration

Defines the strictly positive volume-independent coupling threshold `bhmUniformCouplingThreshold` from superpolynomial conditional-expectation tail profiles (`bhmUniformCouplingThreshold_pos`).

## References

* Part I, Section 7.1 (`subsec:single-cube-telescoping`), Proposition 7.2 (`prop:single-cube-telescoping`)
* Part I, Section 7.2 (`subsec:gap-bootstrap`), Theorem 7.3 (`thm:gap-bootstrap`)
* Bravyi, Hastings, and Michalakis (2010); Bravyi and Hastings (2011)
-/

/-- Canonical $K$-independent BHM coupling threshold
    `J_0 = bhmSandwichDeviation / (bhmShellUniformMomentBound D C m_0 g_tail + 1)`. -/
def bhmUniformCouplingThreshold (D : ℕ) (C m_0 : ℝ) (g_tail : ℕ → ℝ) : ℝ :=
  bhmSandwichDeviation / (bhmShellUniformMomentBound D C m_0 g_tail + 1)

lemma bhmUniformCouplingThreshold_pos (D : ℕ) {C m_0 : ℝ} (hC : 1 ≤ C) (hm0 : 0 ≤ m_0)
    {g_tail : ℕ → ℝ} (hg_tail : IsSuperpolynomialDecay g_tail) :
    0 < bhmUniformCouplingThreshold D C m_0 g_tail := by
  unfold bhmUniformCouplingThreshold
  have h_nn := (bhmShellNormalizedMomentSum_le_uniform D hC hm0 hg_tail (le_refl 1)).1
  have h_dev : (0 : ℝ) < bhmSandwichDeviation := by dsimp [bhmSandwichDeviation]; norm_num
  exact div_pos h_dev (by linarith)

private lemma one_le_collar_const_rca_bdl_threshold : (1 : ℝ) ≤ (collarConstRCABDL : ℝ) := by
  dsimp [collarConstRCABDL, bBDL, bdlLambda]; norm_num

end
