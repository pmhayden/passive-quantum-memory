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

import Defs.FlowAndFilter
import Defs.BHMStability
import Proofs.KatoHastingsFlow.KatoHastingsODEFlow
import Proofs.LiebRobinson.SuperpolyDecayClosure
import Proofs.SupportAndCondExpLemmas
import Proofs.CubeTelescoping.CoarseCubeFunctor
import Proofs.KatoHastingsFlow.ConstructiveQuasiLocalQAC

noncomputable section

open scoped Classical InnerProduct ComplexConjugate BigOperators
open Filter Topology Asymptotics ContinuousLinearMap

/-!
# Scalar Tower and Commutativity Instances for QAC Operator Flows

Re-exports the constructive quasi-local QAC generator module and registers continuous-linear-map scalar tower and commutativity typeclass instances (`instIsScalarTowerCLMQAC`, `instSMulCommClassCLMQAC`) over real and complex scalars.

## References

* Part I, Section 6.3 (`subsec:qac-block-diag`), Equation (75) (`eq:qac-generator-def`), Proposition 6.4 (`prop:qac-block-diagonalization`)
-/

instance (priority := 10000) instIsScalarTowerCLMQAC {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] : IsScalarTower ℂ (E →L[ℂ] E) (E →L[ℂ] E) where
  smul_assoc _ _ _ := ContinuousLinearMap.ext fun _ => rfl

instance (priority := 10000) instSMulCommClassCLMQAC {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] : SMulCommClass ℂ (E →L[ℂ] E) (E →L[ℂ] E) where
  smul_comm c A B := ContinuousLinearMap.ext fun x => (A.map_smul c (B x)).symm

end
