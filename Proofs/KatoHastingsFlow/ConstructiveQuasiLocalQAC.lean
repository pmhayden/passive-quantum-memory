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
import Proofs.LiebRobinson.BochnerQuasiLocality
import Proofs.LiebRobinson.DuhamelAndGronwall
import Proofs.KatoHastingsFlow.KatoHastingsODEFlow
import Proofs.BandLimitedFilter.EigenprojEvolutionAndBlockDecomp
import Proofs.LiebRobinson.SuperpolyDecayClosure
import Proofs.SupportAndCondExpLemmas

/-!
# Constructive Quasi-Local Kato–Hastings Generator and Ground Annihilation

Proves ground-block annihilation of `katoHastingsGeneratorOp` via frustration-free local projector absorption (`localProj_absorbs_groundProj_qac`). Constructs the local commutator generator terms `localKatoGeneratorTerm` and the quasi-local perturbation package `indexedQuasiLocalQACGenerator` (`constructive_quasiLocal_qac_generator_and_flow`).

## References

* Part I, Section 6.1 (`subsec:dsuper-banach`), Definition 6.1 (`def:banach-quasilocal`)
* Part I, Section 6.3 (`subsec:qac-block-diag`), Equation (75) (`eq:qac-generator-def`), Proposition 6.4 (`prop:qac-block-diagonalization`)
-/

noncomputable section

open scoped Classical InnerProduct ComplexConjugate BigOperators
open Filter Topology Asymptotics ContinuousLinearMap MeasureTheory

/-!
## 1. Bochner Integral Ground-Block Annihilation for `katoHastingsGeneratorOp`
-/

/-- **Bochner Integral Ground-Block Identity (`proj_mul_katoHastingsGeneratorOp_mul_proj_eq_integral_smul`)**:
    When $H' P = E_0 P$ and $P H' = E_0 P$ for a star projection $P$, the ground-space block of the
    Bochner-integrated Kato–Hastings generator `katoHastingsGeneratorOp H' W dH` equals
    $\big(\int_{-\infty}^\infty W(t)\,dt\big) \bullet (P \, dH \, P)$. -/
theorem proj_mul_katoHastingsGeneratorOp_mul_proj_eq_integral_smul {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    {P H' dH : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site}
    {E0 : ℝ} {W : ℝ → ℂ}
    (hHP : H' * P = (E0 : ℂ) • P)
    (hPH : P * H' = (E0 : ℂ) • P)
    (h_int : Integrable (fun t : ℝ => W t • heisenbergFlow H' t dH)) :
    P * katoHastingsGeneratorOp H' W dH * P = (∫ t : ℝ, W t) • (P * dH * P) := by
  have hP_Upos : ∀ t : ℝ,
      P * timeEvolutionOp H' t =
      NormedSpace.exp ((Complex.I * (t : ℂ) * (E0 : ℂ)) •
        (1 : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site)) * P := by
    intro t
    change P * NormedSpace.exp ((Complex.I * (t : ℂ)) • H') = _
    rw [clm_proj_mul_exp_smul hPH (Complex.I * (t : ℂ)),
      (commute_exp_smul_one (Complex.I * (t : ℂ) * (E0 : ℂ)) P).eq]
  have hUneg_P : ∀ t : ℝ,
      timeEvolutionOp H' (-t) * P =
      P * NormedSpace.exp ((-(Complex.I * (t : ℂ) * (E0 : ℂ))) •
        (1 : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site)) := by
    intro t
    rw [timeEvolutionOp_neg_eq, clm_exp_smul_mul_proj hHP (-(Complex.I * (t : ℂ))), neg_mul,
      (commute_exp_smul_one (-(Complex.I * (t : ℂ) * (E0 : ℂ))) P).eq]
  unfold katoHastingsGeneratorOp
  rw [clm_sandwich_integral_smul P P W _ h_int]
  have h_pt : (fun t : ℝ => W t • (P * heisenbergFlow H' t dH * P)) =
      (fun t : ℝ => W t • (P * dH * P)) := by
    funext t
    dsimp [heisenbergFlow]
    rw [monoid_diag_flow_id (hP_Upos t) (hUneg_P t)
      (commute_exp_smul_one (-(Complex.I * (t : ℂ) * (E0 : ℂ))) (P * dH * P))
      (exp_smul_one_mul_neg (Complex.I * (t : ℂ) * (E0 : ℂ)))]
  rw [h_pt, integral_smul_const]

/-- **Bochner Integral Ground-Block Annihilation (`proj_mul_katoHastingsGeneratorOp_mul_proj_eq_zero`)**:
    When $H' P = E_0 P$ and $P H' = E_0 P$, if either the odd Kato–Hastings filter kernel has zero
    mean ($\int_{-\infty}^\infty W(t)\,dt = 0$) or $P \, dH \, P = 0$, then
    $P \cdot \mathrm{katoHastingsGeneratorOp}\ H'\ W\ dH \cdot P = 0$. -/
theorem proj_mul_katoHastingsGeneratorOp_mul_proj_eq_zero {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    {P H' dH : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site}
    {E0 : ℝ} {W : ℝ → ℂ}
    (hHP : H' * P = (E0 : ℂ) • P)
    (hPH : P * H' = (E0 : ℂ) • P)
    (h_int : Integrable (fun t : ℝ => W t • heisenbergFlow H' t dH))
    (h_vanish : (∫ t : ℝ, W t) = 0 ∨ P * dH * P = 0) :
    P * katoHastingsGeneratorOp H' W dH * P = 0 := by
  rw [proj_mul_katoHastingsGeneratorOp_mul_proj_eq_integral_smul hHP hPH h_int]
  rcases h_vanish with hW | hdH
  · rw [hW]; ext ψ; simp
  · rw [hdH]; ext ψ; simp

/-!
## 2. Exact Local Kato QAC Generator Term $D_{P}(X) = i [P, X]$
-/

/-- **Local Kato QAC Generator Term (`localKatoGeneratorTerm`)**: $D_P(X) := i (P X - X P)$. -/
def localKatoGeneratorTerm {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (P X : E →L[ℂ] E) : E →L[ℂ] E :=
  (Complex.I : ℂ) • (P * X - X * P)

/-- Self-adjointness of `localKatoGeneratorTerm P X` for self-adjoint $P$ and $X$. -/
lemma isSelfAdjoint_localKatoGeneratorTerm {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] [CompleteSpace E] {P X : E →L[ℂ] E}
    (hP : IsSelfAdjoint P) (hX : IsSelfAdjoint X) :
    IsSelfAdjoint (localKatoGeneratorTerm P X) := by
  rw [isSelfAdjoint_iff, localKatoGeneratorTerm, star_smul, star_sub, star_mul, star_mul,
    hP.star_eq, hX.star_eq, RCLike.star_def, Complex.conj_I, neg_smul, ← smul_neg, neg_sub]

/-- Support preservation of `localKatoGeneratorTerm P X` on any region $A$. -/
lemma isSupportedOn_localKatoGeneratorTerm {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    {A : Finset (BoxD D L)}
    {P X : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site}
    (hP : IsSupportedOn Site A P) (hX : IsSupportedOn Site A X) :
    IsSupportedOn Site A (localKatoGeneratorTerm P X) :=
  isSupportedOn_smul A (Complex.I : ℂ)
    (isSupportedOn_sub A (isSupportedOn_mul A hP hX) (isSupportedOn_mul A hX hP))

/-- Norm bound `‖localKatoGeneratorTerm P X‖ ≤ 2 * ‖X‖` whenever `‖P‖ ≤ 1`. -/
lemma norm_localKatoGeneratorTerm_le {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] {P X : E →L[ℂ] E} (hP : ‖P‖ ≤ 1) :
    ‖localKatoGeneratorTerm P X‖ ≤ 2 * ‖X‖ := by
  dsimp [localKatoGeneratorTerm]
  rw [norm_smul, Complex.norm_I, one_mul]
  have h1 : ‖P * X‖ ≤ ‖X‖ :=
    le_trans (norm_mul_le P X) (mul_le_of_le_one_left (norm_nonneg X) hP)
  have h2 : ‖X * P‖ ≤ ‖X‖ :=
    le_trans (norm_mul_le X P) (mul_le_of_le_one_right (norm_nonneg X) hP)
  linarith [norm_sub_le (P * X) (X * P)]

/-- Any projection $Q$ absorbed by $P$ ($P Q = Q$ and $Q P = Q$) satisfies $Q \, D_P(X) \, Q = 0$. -/
lemma subproj_mul_localKatoGeneratorTerm_mul_subproj_eq_zero {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] {P Q X : E →L[ℂ] E}
    (hPQ : P * Q = Q) (hQP : Q * P = Q) :
    Q * localKatoGeneratorTerm P X * Q = 0 := by
  dsimp [localKatoGeneratorTerm]
  have h1 : Q * (P * X - X * P) * Q = 0 := by
    calc Q * (P * X - X * P) * Q
      _ = (Q * P) * X * Q - Q * X * (P * Q) := by
        rw [mul_sub, sub_mul]; simp only [mul_assoc]
      _ = Q * X * Q - Q * X * Q := by rw [hQP, hPQ]
      _ = 0 := sub_self _
  rw [mul_smul_comm, smul_mul_assoc, h1]; ext ψ; simp

/-- For an idempotent $P$ ($P^2 = P$), the ground-block $P \, D_P(X) \, P = 0$. -/
lemma proj_mul_localKatoGeneratorTerm_mul_proj_eq_zero {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] {P X : E →L[ℂ] E} (hP_idem : P * P = P) :
    P * localKatoGeneratorTerm P X * P = 0 :=
  subproj_mul_localKatoGeneratorTerm_mul_subproj_eq_zero hP_idem hP_idem

/-- Any projection $Q$ orthogonal to $P$ ($Q P = 0$ and $P Q = 0$) satisfies $Q \, D_P(X) \, Q = 0$. -/
lemma orth_mul_localKatoGeneratorTerm_mul_orth_eq_zero {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] {P Q X : E →L[ℂ] E}
    (hQP : Q * P = 0) (hPQ : P * Q = 0) :
    Q * localKatoGeneratorTerm P X * Q = 0 := by
  dsimp [localKatoGeneratorTerm]
  have h1 : Q * (P * X - X * P) * Q = 0 := by
    calc Q * (P * X - X * P) * Q
      _ = (Q * P) * X * Q - Q * X * (P * Q) := by
        rw [mul_sub, sub_mul]; simp only [mul_assoc]
      _ = 0 := by rw [hQP, hPQ, zero_mul, zero_mul, mul_zero, sub_self]
  rw [mul_smul_comm, smul_mul_assoc, h1]; ext ψ; simp

/-- For an idempotent $P$ ($P^2 = P$), the excited-block $(1 - P) \, D_P(X) \, (1 - P) = 0$. -/
lemma one_sub_proj_mul_localKatoGeneratorTerm_mul_one_sub_proj_eq_zero {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] {P X : E →L[ℂ] E} (hP_idem : P * P = P) :
    (1 - P) * localKatoGeneratorTerm P X * (1 - P) = 0 :=
  orth_mul_localKatoGeneratorTerm_mul_orth_eq_zero
    (by rw [sub_mul, one_mul, hP_idem, sub_self])
    (by rw [mul_sub, mul_one, hP_idem, sub_self])

/-- For an idempotent $P$ ($P^2 = P$), $(1 - P) D_P(X) P + P D_P(X) (1 - P) = D_P(X)$. -/
lemma offDiag_localKatoGeneratorTerm_eq_self {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] {P X : E →L[ℂ] E} (hP_idem : P * P = P) :
    (1 - P) * localKatoGeneratorTerm P X * P + P * localKatoGeneratorTerm P X * (1 - P) =
      localKatoGeneratorTerm P X := by
  set D := localKatoGeneratorTerm P X
  have hPP : P * D * P = 0 := proj_mul_localKatoGeneratorTerm_mul_proj_eq_zero hP_idem
  have hQQ : (1 - P) * D * (1 - P) = 0 :=
    one_sub_proj_mul_localKatoGeneratorTerm_mul_one_sub_proj_eq_zero hP_idem
  calc (1 - P) * D * P + P * D * (1 - P)
    _ = (P * D * P + P * D * (1 - P)) + ((1 - P) * D * P + (1 - P) * D * (1 - P)) := by
      rw [hPP, hQQ, zero_add, add_zero, add_comm]
    _ = P * D * (P + (1 - P)) + (1 - P) * D * (P + (1 - P)) := by rw [← mul_add, ← mul_add]
    _ = P * D * 1 + (1 - P) * D * 1 := by rw [add_sub_cancel]
    _ = (P + (1 - P)) * D := by rw [mul_one, mul_one, ← add_mul]
    _ = 1 * D := by rw [add_sub_cancel]
    _ = D := one_mul D

/-- **Exact Local Kato Commutator Identity (`commutator_localKatoGeneratorTerm_eq_offDiag`)**:
    $i (D_P(X) P - P D_P(X)) = (1 - P) X P + P X (1 - P)$ for $P^2 = P$. -/
theorem commutator_localKatoGeneratorTerm_eq_offDiag {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] {P X : E →L[ℂ] E} (hP_idem : P * P = P) :
    (Complex.I : ℂ) • (localKatoGeneratorTerm P X * P - P * localKatoGeneratorTerm P X) =
      (1 - P) * X * P + P * X * (1 - P) := by
  dsimp [localKatoGeneratorTerm]
  rw [smul_mul_assoc, mul_smul_comm, ← smul_sub, smul_smul, Complex.I_mul_I, neg_one_smul]
  calc -((P * X - X * P) * P - P * (P * X - X * P))
    _ = -((P * X * P - X * (P * P)) - ((P * P) * X - P * X * P)) := by
      rw [sub_mul, mul_sub]; simp only [mul_assoc]
    _ = -((P * X * P - X * P) - (P * X - P * X * P)) := by rw [hP_idem]
    _ = (X * P - P * X * P) + (P * X - P * X * P) := by abel
    _ = (1 - P) * X * P + P * X * (1 - P) := by
      rw [sub_mul, one_mul, sub_mul, mul_sub, mul_one]

/-- **Exact Local Kato `opCommutator` Identity (`opCommutator_proj_localKatoGeneratorTerm_eq_smul_offDiag`)**. -/
theorem opCommutator_proj_localKatoGeneratorTerm_eq_smul_offDiag {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    {P X : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site} (hP_idem : P * P = P) :
    opCommutator P (localKatoGeneratorTerm P X) =
      (Complex.I : ℂ) • ((1 - P) * X * P + P * X * (1 - P)) := by
  rw [← commutator_localKatoGeneratorTerm_eq_offDiag hP_idem, smul_smul, Complex.I_mul_I,
    neg_one_smul]
  dsimp [opCommutator]
  abel

/-- **Exact Local Block Decomposition (`eq_diag_add_commutator_localKatoGeneratorTerm`)**:
    $X = (P X P + (1 - P) X (1 - P)) + i (D_P(X) P - P D_P(X))$ for $P^2 = P$. -/
theorem eq_diag_add_commutator_localKatoGeneratorTerm {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] {P X : E →L[ℂ] E} (hP_idem : P * P = P) :
    X = (P * X * P + (1 - P) * X * (1 - P)) +
      (Complex.I : ℂ) • (localKatoGeneratorTerm P X * P - P * localKatoGeneratorTerm P X) := by
  rw [commutator_localKatoGeneratorTerm_eq_offDiag hP_idem]
  calc X
    _ = 1 * X * 1 := by rw [one_mul, mul_one]
    _ = (P + (1 - P)) * X * (P + (1 - P)) := by rw [add_sub_cancel]
    _ = (P * X * P + (1 - P) * X * (1 - P)) + ((1 - P) * X * P + P * X * (1 - P)) := by
      rw [add_mul, add_mul, mul_add, mul_add]; abel

/-!
## 3. Global Quasi-Local QAC Generator `indexedQuasiLocalQACGenerator` & Autonomous Off-Diagonal Flow
-/

/-- Norm bound `‖P‖ ≤ 1` for any star projection $P$. -/
private lemma isStarProjection_norm_le_one_qac {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] [CompleteSpace E] {P : E →L[ℂ] E} (hP : IsStarProjection P) :
    ‖P‖ ≤ 1 := by
  by_cases h0 : ‖P‖ = 0
  · linarith
  · have h_pos : 0 < ‖P‖ := lt_of_le_of_ne (norm_nonneg P) (Ne.symm h0)
    have h_sq : ‖P‖ * ‖P‖ ≤ 1 * ‖P‖ := by
      rw [one_mul, ← CStarRing.norm_star_mul_self, hP.isSelfAdjoint.star_eq, hP.isIdempotentElem.eq]
    exact le_of_mul_le_mul_right h_sq h_pos

/-- The product of a list of pairwise-commuting star projections is a star projection. -/
private lemma isStarProjection_list_prod_qac {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [CompleteSpace E] (l : List (E →L[ℂ] E))
    (hl_proj : ∀ p ∈ l, IsStarProjection p)
    (hl_comm : l.Pairwise Commute) :
    IsStarProjection l.prod := by
  induction l with
  | nil =>
    rw [List.prod_nil]
    exact ⟨IsIdempotentElem.one, IsSelfAdjoint.one (E →L[ℂ] E)⟩
  | cons p tail ih =>
    rw [List.prod_cons]
    rcases List.pairwise_cons.mp hl_comm with ⟨h_p_comm, h_tail_comm⟩
    have hp : IsStarProjection p := hl_proj p List.mem_cons_self
    have htail : IsStarProjection tail.prod :=
      ih (fun q hq => hl_proj q (List.mem_cons_of_mem p hq)) h_tail_comm
    have h_comm_prod : Commute p tail.prod := Commute.list_prod_right tail p h_p_comm
    exact hp.mul htail h_comm_prod

/-- If $p \in l$ is idempotent and commutes with every element of $l$, then $(1 - p) \cdot \prod l = 0$. -/
private lemma one_sub_mul_list_prod_eq_zero_qac {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] [CompleteSpace E] (l : List (E →L[ℂ] E)) (p : E →L[ℂ] E)
    (hp_mem : p ∈ l) (hp_idem : IsIdempotentElem p)
    (hp_comm : ∀ q ∈ l, Commute p q) :
    (1 - p) * l.prod = 0 := by
  induction l with
  | nil => cases hp_mem
  | cons q tail ih =>
    rw [List.prod_cons, ← mul_assoc]
    rcases List.mem_cons.mp hp_mem with rfl | hp_tail
    · have h_zero : (1 - p) * p = 0 := by rw [sub_mul, one_mul, hp_idem.eq, sub_self]
      rw [h_zero, zero_mul]
    · have h_comm : Commute (1 - p) q :=
        (Commute.one_left q).sub_left (hp_comm q List.mem_cons_self)
      rw [h_comm.eq, mul_assoc, ih hp_tail (fun r hr => hp_comm r (List.mem_cons_of_mem q hr)),
        mul_zero]

/-- If every element $a \in l$ acts as a left identity on $x$, so does $\prod l$. -/
private lemma list_prod_mul_eq_right_qac {R : Type*} [Monoid R] (l : List R) (x : R)
    (h : ∀ a ∈ l, a * x = x) : l.prod * x = x := by
  induction l with
  | nil => simp
  | cons a tail ih =>
    rw [List.prod_cons, mul_assoc, ih (fun b hb => h b (List.mem_cons_of_mem a hb)),
      h a List.mem_cons_self]

/-- `sys.P_loc A` is a star projection for any `IndexedCommutingProjectorHamiltonian`. -/
private lemma IndexedCommutingProjectorHamiltonian.isStarProjection_P_loc_qac {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (sys : IndexedCommutingProjectorHamiltonian D L Site ι) (A : Finset (BoxD D L)) :
    IsStarProjection (sys.localGroundProj A) := by
  dsimp [IndexedCommutingProjectorHamiltonian.localGroundProj,
    IndexedCommutingProjectorHamiltonian.localGroundProj]
  set S := (Finset.univ : Finset ι).filter (fun i : ι => sys.support i ⊆ A)
  apply isStarProjection_list_prod_qac
  · intro p hp
    rcases List.mem_map.mp hp with ⟨i, _, rfl⟩
    exact (sys.is_projector i).one_sub
  · rw [List.pairwise_map]
    refine List.Pairwise.imp_of_mem ?_ S.nodup_toList
    intro i j _ _ _
    exact (Commute.one_left _).sub_left ((Commute.one_right _).sub_right (sys.pairwise_commute i j))

/-- Every check $Q_i$ ($i \in \iota$) annihilates `sys.P0`, so `sys.P_loc A` absorbs `sys.P0` on both sides. -/
private lemma IndexedCommutingProjectorHamiltonian.localProj_absorbs_groundProj_qac {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (sys : IndexedCommutingProjectorHamiltonian D L Site ι) (A : Finset (BoxD D L)) :
    sys.localGroundProj A * sys.P0 = sys.P0 ∧ sys.P0 * sys.localGroundProj A = sys.P0 := by
  have h_comm : Commute (sys.localGroundProj A) sys.P0 := by
    dsimp [IndexedCommutingProjectorHamiltonian.localGroundProj, IndexedCommutingProjectorHamiltonian.P0,
      IndexedCommutingProjectorHamiltonian.groundProj,
      IndexedCommutingProjectorHamiltonian.localGroundProj]
    apply Commute.list_prod_left; intro p hp
    rcases List.mem_map.mp hp with ⟨i, _, rfl⟩
    apply Commute.list_prod_right; intro q hq
    rcases List.mem_map.mp hq with ⟨j, _, rfl⟩
    exact (Commute.one_left _).sub_left ((Commute.one_right _).sub_right (sys.pairwise_commute i j))
  have h_check_P0 : ∀ i : ι, sys.checkProj i * sys.P0 = 0 := by
    intro i
    dsimp [IndexedCommutingProjectorHamiltonian.P0, IndexedCommutingProjectorHamiltonian.groundProj]
    have h_mem : 1 - sys.checkProj i ∈
        (Finset.univ : Finset ι).toList.map (fun j : ι => 1 - sys.checkProj j) :=
      List.mem_map_of_mem (Finset.mem_toList.mpr (Finset.mem_univ i))
    have h_sub : sys.checkProj i = 1 - (1 - sys.checkProj i) :=
      (sub_sub_cancel 1 (sys.checkProj i)).symm
    rw [h_sub]
    apply one_sub_mul_list_prod_eq_zero_qac _ (1 - sys.checkProj i) h_mem
      (sys.is_projector i).one_sub.isIdempotentElem
    intro q hq
    rcases List.mem_map.mp hq with ⟨j, _, rfl⟩
    exact (Commute.one_left _).sub_left ((Commute.one_right _).sub_right (sys.pairwise_commute i j))
  have h_abs : sys.localGroundProj A * sys.P0 = sys.P0 := by
    dsimp [IndexedCommutingProjectorHamiltonian.localGroundProj,
      IndexedCommutingProjectorHamiltonian.localGroundProj]
    apply list_prod_mul_eq_right_qac
    intro p hp
    rcases List.mem_map.mp hp with ⟨i, _, rfl⟩
    change (1 - sys.checkProj i) * sys.P0 = sys.P0
    rw [sub_mul, one_mul, h_check_P0 i, sub_zero]
  exact ⟨h_abs, h_comm.symm.eq.trans h_abs⟩

/-- **Constructive Quasi-Local Kato–Hastings QAC Generator (`indexedQuasiLocalQACGenerator`)**:
    $D_{\mathrm{loc}}.\mathrm{term}\ r\ A := i [\mathrm{sys.P\_loc}\ A, V.\mathrm{term}\ r\ A]$. -/
def indexedQuasiLocalQACGenerator {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (sys : IndexedCommutingProjectorHamiltonian D L Site ι)
    (V : QuasiLocalPerturbation D L Site) :
    QuasiLocalPerturbation D L Site where
  term r A := localKatoGeneratorTerm (sys.localGroundProj A) (V.term r A)
  is_selfAdjoint r A :=
    isSelfAdjoint_localKatoGeneratorTerm
      (sys.isStarProjection_P_loc_qac A).isSelfAdjoint (V.is_selfAdjoint r A)
  is_supported r hr A hA :=
    isSupportedOn_localKatoGeneratorTerm (sys.isSupportedOn_P_loc A) (V.is_supported r hr A hA)

/-- **Master Constructive Quasi-Local QAC Generator & Off-Diagonal Flow Theorem
    (`constructive_quasiLocal_qac_generator_and_flow`)**. -/
theorem constructive_quasiLocal_qac_generator_and_flow {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (sys : IndexedCommutingProjectorHamiltonian D L Site ι)
    (V : QuasiLocalPerturbation D L Site)
    {J : ℝ} {f : ℕ → ℝ} (hf : IsSuperpolynomialDecay f)
    (hV_decay : V.SatisfiesDecayBound J f) :
    let D_loc := indexedQuasiLocalQACGenerator sys V
    let D_gen : ℝ → (ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site) := fun _ => D_loc.totalPerturbation
    let U_flow : ℝ → (ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site) :=
      fun s => timeEvolutionOp D_loc.totalPerturbation s
    let P_flow : ℝ → (ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site) :=
      fun s => heisenbergFlow D_loc.totalPerturbation s sys.P0
    IsSuperpolynomialDecay (fun r => 2 * f r) ∧
    D_loc.SatisfiesDecayBound J (fun r => 2 * f r) ∧
    (∀ r : ℕ, ∀ A : Finset (BoxD D L),
      sys.localGroundProj A * D_loc.term r A * sys.localGroundProj A = 0 ∧
      (1 - sys.localGroundProj A) * D_loc.term r A * (1 - sys.localGroundProj A) = 0 ∧
      sys.P0 * D_loc.term r A * sys.P0 = 0 ∧
      opCommutator (sys.localGroundProj A) (D_loc.term r A) =
        (Complex.I : ℂ) • ((1 - sys.localGroundProj A) * V.term r A * sys.localGroundProj A +
          sys.localGroundProj A * V.term r A * (1 - sys.localGroundProj A)) ∧
      (Complex.I : ℂ) • (D_loc.term r A * sys.localGroundProj A - sys.localGroundProj A * D_loc.term r A) =
        (1 - sys.localGroundProj A) * V.term r A * sys.localGroundProj A +
          sys.localGroundProj A * V.term r A * (1 - sys.localGroundProj A)) ∧
    sys.P0 * D_loc.totalPerturbation * sys.P0 = 0 ∧
    IsKatoHastingsFlowSystem sys.P0 D_gen U_flow P_flow ∧
    (∀ s : ℝ, P_flow s * D_gen s * P_flow s = 0) := by
  intro D_loc D_gen U_flow P_flow
  have h2f : IsSuperpolynomialDecay (fun r => 2 * f r) :=
    isSuperpolynomialDecay_const_mul hf (by norm_num)
  have hD_decay : D_loc.SatisfiesDecayBound J (fun r => 2 * f r) := by
    intro r hr A hA; dsimp [D_loc, indexedQuasiLocalQACGenerator]
    have hP_norm : ‖sys.localGroundProj A‖ ≤ 1 :=
      isStarProjection_norm_le_one_qac (sys.isStarProjection_P_loc_qac A)
    calc ‖localKatoGeneratorTerm (sys.localGroundProj A) (V.term r A)‖
      _ ≤ 2 * ‖V.term r A‖ := norm_localKatoGeneratorTerm_le hP_norm
      _ ≤ 2 * (J * f r) := mul_le_mul_of_nonneg_left (hV_decay r hr A hA) (by norm_num)
      _ = J * (2 * f r) := by ring
  have h_terms : ∀ r : ℕ, ∀ A : Finset (BoxD D L),
      sys.localGroundProj A * D_loc.term r A * sys.localGroundProj A = 0 ∧
      (1 - sys.localGroundProj A) * D_loc.term r A * (1 - sys.localGroundProj A) = 0 ∧
      sys.P0 * D_loc.term r A * sys.P0 = 0 ∧
      opCommutator (sys.localGroundProj A) (D_loc.term r A) =
        (Complex.I : ℂ) • ((1 - sys.localGroundProj A) * V.term r A * sys.localGroundProj A +
          sys.localGroundProj A * V.term r A * (1 - sys.localGroundProj A)) ∧
      (Complex.I : ℂ) • (D_loc.term r A * sys.localGroundProj A - sys.localGroundProj A * D_loc.term r A) =
        (1 - sys.localGroundProj A) * V.term r A * sys.localGroundProj A +
          sys.localGroundProj A * V.term r A * (1 - sys.localGroundProj A) := by
    intro r A
    have hPA_idem : sys.localGroundProj A * sys.localGroundProj A = sys.localGroundProj A :=
      (sys.isStarProjection_P_loc_qac A).isIdempotentElem.eq
    rcases sys.localProj_absorbs_groundProj_qac A with ⟨hPA_P0, hP0_PA⟩
    refine ⟨proj_mul_localKatoGeneratorTerm_mul_proj_eq_zero hPA_idem,
      one_sub_proj_mul_localKatoGeneratorTerm_mul_one_sub_proj_eq_zero hPA_idem,
      subproj_mul_localKatoGeneratorTerm_mul_subproj_eq_zero hPA_P0 hP0_PA,
      opCommutator_proj_localKatoGeneratorTerm_eq_smul_offDiag hPA_idem,
      commutator_localKatoGeneratorTerm_eq_offDiag hPA_idem⟩
  have hP0_D_P0 : sys.P0 * D_loc.totalPerturbation * sys.P0 = 0 := by
    dsimp [QuasiLocalPerturbation.totalPerturbation]; rw [Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_eq_zero (fun r _ => ?_)
    rw [Finset.mul_sum, Finset.sum_mul]
    exact Finset.sum_eq_zero (fun A _ => (h_terms r A).2.2.1)
  have h_flow : IsKatoHastingsFlowSystem sys.P0 D_gen U_flow P_flow :=
    { isSelfAdjoint_D := fun _ => D_loc.isSelfAdjoint_totalPerturbation
      U_zero := timeEvolutionOp_zero D_loc.totalPerturbation
      P_zero := by dsimp [P_flow, heisenbergFlow]; rw [neg_zero, timeEvolutionOp_zero, one_mul, mul_one]
      hasDerivAt_U := fun s => hasDerivAt_timeEvolutionOp D_loc.totalPerturbation s
      hasDerivAt_P := fun s => hasDerivAt_heisenbergFlow D_loc.totalPerturbation sys.P0 s }
  have h_flow_zero : ∀ s : ℝ, P_flow s * D_gen s * P_flow s = 0 := by
    intro s; dsimp [P_flow, D_gen, heisenbergFlow]
    have h_comm_neg : Commute (timeEvolutionOp D_loc.totalPerturbation (-s)) D_loc.totalPerturbation :=
      (commute_smul_left_clm (Commute.refl D_loc.totalPerturbation) (Complex.I * ((-s : ℝ) : ℂ))).exp_left
    have h_mid : timeEvolutionOp D_loc.totalPerturbation (-s) * D_loc.totalPerturbation * timeEvolutionOp D_loc.totalPerturbation s =
        D_loc.totalPerturbation := by
      rw [h_comm_neg.eq, mul_assoc, (timeEvolutionOp_mul_neg_self D_loc.totalPerturbation s).2, mul_one]
    calc (timeEvolutionOp D_loc.totalPerturbation s * sys.P0 * timeEvolutionOp D_loc.totalPerturbation (-s)) *
          D_loc.totalPerturbation *
          (timeEvolutionOp D_loc.totalPerturbation s * sys.P0 * timeEvolutionOp D_loc.totalPerturbation (-s))
      _ = timeEvolutionOp D_loc.totalPerturbation s * sys.P0 *
          (timeEvolutionOp D_loc.totalPerturbation (-s) * D_loc.totalPerturbation * timeEvolutionOp D_loc.totalPerturbation s) *
          sys.P0 * timeEvolutionOp D_loc.totalPerturbation (-s) := by simp only [mul_assoc]
      _ = timeEvolutionOp D_loc.totalPerturbation s * (sys.P0 * D_loc.totalPerturbation * sys.P0) *
          timeEvolutionOp D_loc.totalPerturbation (-s) := by rw [h_mid]; simp only [mul_assoc]
      _ = 0 := by rw [hP0_D_P0, mul_zero, zero_mul]
  exact ⟨h2f, hD_decay, h_terms, hP0_D_P0, h_flow, h_flow_zero⟩

end
