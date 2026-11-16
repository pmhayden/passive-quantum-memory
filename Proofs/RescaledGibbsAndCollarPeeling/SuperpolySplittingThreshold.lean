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

import Proofs.RescaledGibbsAndCollarPeeling.AdditiveLeakageGibbsBridge

open scoped Classical InnerProduct ComplexConjugate BigOperators
open Filter Topology Asymptotics ContinuousLinearMap KMSPinchedGibbs PerturbedThermalBarrier
open WeldedHierarchy WeldedHierarchy.BDLDecoder InhomogeneousMemoryChallenge

noncomputable section

set_option maxRecDepth 200000
set_option maxHeartbeats 800000

/-!
# Asymptotic Eighth-Power Decay Threshold for Superpolynomial Profiles

Proves `exists_k_eight_of_isSuperpolynomialDecay`, extracting an explicit cutoff scale above which any profile satisfying `IsSuperpolynomialDecay` is bounded by any prescribed positive multiple of the inverse eighth power.

## References

* Part I, Section 6.1 (`subsec:dsuper-banach`), Definition 6.1 (`def:banach-quasilocal`), Lemma 6.2 (`lem:dsuper-closure`)
* Part II, Section 2 (`sec:setup`), Definition 2.3 (`def:perturbation-class`), Lemma 2.4 (`lem:D-super-closure`)
-/

lemma exists_k_eight_of_isSuperpolynomialDecay {δ_split : ℕ → ℝ}
    (hδ : IsSuperpolynomialDecay δ_split) :
    ∃ k_8 : ℕ, ∀ k : ℕ, k_8 ≤ k →
      δ_split (bdlBoxSide k) ≤ 1 / 8 ∧ δ_split (bdlBoxSide k) < 1 / 4 := by
  have h_tendsto : Tendsto δ_split atTop (𝓝 0) := by simpa using hδ.2 0
  rcases Filter.eventually_atTop.mp
      (h_tendsto.eventually (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1 / 8)))
    with ⟨N_8, hN_8⟩
  refine ⟨N_8, fun k hk => ?_⟩
  have hk2 : k + 2 ≤ bdlBoxSide k := (bdlBoxSide_scaling_and_strictMono k).2.1
  have hL : N_8 ≤ bdlBoxSide k := by omega
  have h_lt : δ_split (bdlBoxSide k) < 1 / 8 := hN_8 (bdlBoxSide k) hL
  exact ⟨le_of_lt h_lt, by linarith⟩

end
