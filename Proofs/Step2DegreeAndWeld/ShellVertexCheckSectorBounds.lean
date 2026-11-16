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

import Proofs.Step2DegreeAndWeld.CylinderQubitZDegreeBound

/-!
# Shell-Vertex X-Check Support Bounds Across Vertical, Star, and Azimuthal Sectors

Establishes injectivity of radial-parent and boundary-projection maps (`radialParentV_eq_imp_eq_of_ne_inr_inr`, `projXq0ToBoundaryX0_inj_of_ne_inr_inr`) and bounds the qubit support of each shell-vertex `X`-check sector-by-sector. Bounds incident vertical boundary 1-cells (`card_filter_bdlDeltaX0_vert_le_two`), star-interface 1-cells under `bdlGXQ0`, and azimuthal shell segments across all boundary-link types (`card_filter_bdlDeltaX0_azim_inl_le_four`, `card_filter_bdlDeltaX0_azim_inr_inl_le_two`, `card_filter_bdlDeltaX0_azim_inr_inr_le_two`).

## References

* Part I, Section 2.3 (`subsec:step2-mapping-cone`), Definition 2.5 (`def:three-layer-mapping-cone`), Equation (4) (`eq:dx-coboundary`), Equation (8) (`eq:Psi-XQ-def`), Proposition 2.6 (`prop:mapping-cone-invariants`)
-/

noncomputable section
open scoped Classical BigOperators
namespace WeldedHierarchy

/-! ## 1. Radial Parent & Boundary Projection Injectivity Lemmas -/

lemma radialParentV_eq_imp_eq_of_ne_inr_inr {Q M_Z M_X : Type}
    [Fintype Q] [DecidableEq Q] [Fintype M_Z] [DecidableEq M_Z] [Fintype M_X] [DecidableEq M_X]
    (pcode : CSSCode3D Q M_Z M_X) (M : ℕ)
    (v v0 : BoundaryX0 pcode M) (r : Fin (M + 1))
    (h_not_z : ∀ z : M_Z, v0 ≠ Sum.inr (Sum.inr z))
    (h_eq : radialParentV pcode M v r = v0) :
    v = v0 := by
  rcases v with q | ⟨⟨eZ, j⟩ | z⟩
  · exact h_eq
  · dsimp [radialParentV] at h_eq
    split_ifs at h_eq with hj
    · exact h_eq
    · exfalso; exact h_not_z eZ.val.2 h_eq.symm
  · exfalso; exact h_not_z z h_eq.symm

/-- Shows that `projXq0ToBoundaryX0` is injective over any fiber whose target $v_0$ is not
    a coarse $Z$-check vertex. -/
lemma projXq0ToBoundaryX0_inj_of_ne_inr_inr {Q M_Z M_X : Type}
    [Fintype Q] [DecidableEq Q] [Fintype M_Z] [DecidableEq M_Z] [Fintype M_X] [DecidableEq M_X]
    (pcode : CSSCode3D Q M_Z M_X) (M : ℕ)
    (v1 v2 : Xq0 pcode M) (v0 : BoundaryX0 pcode M)
    (h_not_z : ∀ z : M_Z, v0 ≠ Sum.inr (Sum.inr z))
    (h1 : projXq0ToBoundaryX0 pcode M v1 = v0)
    (h2 : projXq0ToBoundaryX0 pcode M v2 = v0) :
    v1 = v2 := by
  rcases v1 with q1 | ⟨p1 | eZ1⟩ <;> rcases v2 with q2 | ⟨p2 | eZ2⟩
  · dsimp [projXq0ToBoundaryX0] at h1 h2
    injection (h1.trans h2.symm) with hq_eq
    exact congr_arg Sum.inl hq_eq
  · dsimp [projXq0ToBoundaryX0] at h1 h2; exfalso; injection (h1.trans h2.symm)
  · dsimp [projXq0ToBoundaryX0] at h2; exfalso; exact h_not_z eZ2.val.2 h2.symm
  · dsimp [projXq0ToBoundaryX0] at h1 h2; exfalso; injection (h1.trans h2.symm)
  · dsimp [projXq0ToBoundaryX0] at h1 h2
    injection (h1.trans h2.symm) with h_inr
    injection h_inr with hp_eq
    exact congr_arg (fun p => Sum.inr (Sum.inl p)) hp_eq
  · dsimp [projXq0ToBoundaryX0] at h2; exfalso; exact h_not_z eZ2.val.2 h2.symm
  · dsimp [projXq0ToBoundaryX0] at h1; exfalso; exact h_not_z eZ1.val.2 h1.symm
  · dsimp [projXq0ToBoundaryX0] at h1; exfalso; exact h_not_z eZ1.val.2 h1.symm
  · dsimp [projXq0ToBoundaryX0] at h1; exfalso; exact h_not_z eZ1.val.2 h1.symm

/-- Shows that `radialParentVertex` can never lie on the outermost shell $r = M$. -/
lemma radialParentVertex_ne_of_last {Q M_Z M_X : Type}
    [Fintype Q] [DecidableEq Q] [Fintype M_Z] [DecidableEq M_Z] [Fintype M_X] [DecidableEq M_X]
    (pcode : CSSCode3D Q M_Z M_X) (M : ℕ)
    (sv sv0 : ShellVertex pcode M) (hr_nz : sv.val.2.val ≠ 0)
    (h_last : sv0.val.2 = Fin.last M) :
    radialParentVertex pcode M sv ≠ sv0 := by
  intro h_eq
  have hr : finPred sv.val.2 = sv0.val.2 := congr_arg (fun s : ShellVertex pcode M => s.val.2) h_eq
  rw [h_last] at hr
  have hr_val : sv.val.2.val - 1 = M := congr_arg Fin.val hr
  have h_lt := sv.val.2.isLt
  omega

/-! ## 2. Vertical Boundary & Coupling Map bdlGXQ0 Support Bounds -/

lemma card_filter_bdlDeltaX0_vert_le_two {Q M_Z M_X : Type}
    [Fintype Q] [DecidableEq Q] [Fintype M_Z] [DecidableEq M_Z] [Fintype M_X] [DecidableEq M_X]
    (pcode : CSSCode3D Q M_Z M_X) (M : ℕ) (sv0 : ShellVertex pcode M) (b0 : Fin 3) :
    (Finset.univ.filter (fun p : BoundaryX0Link pcode M × Fin 2 =>
      bdlDeltaX0 pcode M (Sum.inr (sv0, b0)) (Sum.inr (Sum.inr p)) ≠ 0)).card ≤ 2 := by
  have h_sub : Finset.univ.filter (fun p : BoundaryX0Link pcode M × Fin 2 =>
      bdlDeltaX0 pcode M (Sum.inr (sv0, b0)) (Sum.inr (Sum.inr p)) ≠ 0) ⊆
      {(sv0.val.1, 0), (sv0.val.1, 1)} := by
    intro ⟨xv, v⟩ hp
    rw [Finset.mem_filter] at hp
    have h1 := hp.2
    unfold bdlDeltaX0 at h1; dsimp only at h1
    have h_eq : xv = sv0.val.1 := by
      rcases add_ite_one_ne_zero_imp h1 with hc | hc <;>
        (injection hc with hc; injection hc with hsv _;
         exact (congr_arg (fun s : ShellVertex pcode M => s.val.1) hsv).symm)
    subst h_eq
    rw [Finset.mem_insert, Finset.mem_singleton]
    fin_cases v
    · exact Or.inl rfl
    · exact Or.inr rfl
  exact (Finset.card_le_card h_sub).trans Finset.card_le_two

/-- Shows that an interior shell vertex check ($r_0 \ne M$) acts on $0$ outer vertical
    boundary qubits under `bdlDeltaX0`. -/
lemma card_filter_bdlDeltaX0_vert_eq_zero_of_ne_last {Q M_Z M_X : Type}
    [Fintype Q] [DecidableEq Q] [Fintype M_Z] [DecidableEq M_Z] [Fintype M_X] [DecidableEq M_X]
    (pcode : CSSCode3D Q M_Z M_X) (M : ℕ) (sv0 : ShellVertex pcode M) (b0 : Fin 3)
    (h_ne : sv0.val.2 ≠ Fin.last M) :
    (Finset.univ.filter (fun p : BoundaryX0Link pcode M × Fin 2 =>
      bdlDeltaX0 pcode M (Sum.inr (sv0, b0)) (Sum.inr (Sum.inr p)) ≠ 0)).card = 0 := by
  apply card_filter_eq_zero_of_imp_false
  intro ⟨xv, v⟩ h1
  unfold bdlDeltaX0 at h1; dsimp only at h1
  rcases add_ite_one_ne_zero_imp h1 with hc | hc <;>
    (injection hc with hc; injection hc with hsv _;
     exact h_ne (congr_arg (fun s : ShellVertex pcode M => s.val.2) hsv))

/-- Shows that an interior shell vertex check ($r_0 \ne M$) acts on $0$ qubits in `BDLCQ1`
    under the outer coupling map `bdlGXQ0`. -/
lemma card_filter_bdlGXQ0_eq_zero_of_ne_last {Q M_Z M_X : Type}
    [Fintype Q] [DecidableEq Q] [Fintype M_Z] [DecidableEq M_Z] [Fintype M_X] [DecidableEq M_X]
    (pcode : CSSCode3D Q M_Z M_X) (M : ℕ) (sv0 : ShellVertex pcode M) (b0 : Fin 3)
    (h_ne : sv0.val.2 ≠ Fin.last M) :
    (Finset.univ.filter (fun qQ : BDLCQ1 pcode M =>
      bdlGXQ0 pcode M (Sum.inr (sv0, b0)) qQ ≠ 0)).card = 0 := by
  apply card_filter_eq_zero_of_imp_false
  intro qQ h1
  dsimp [bdlGXQ0] at h1
  split_ifs at h1 with hc
  · exact h_ne hc.1
  · exact h1 rfl

/-- Shows that a shell vertex check `(sv0, b0)` whose link vertex is not a coarse $Z$-check
    acts on at most $1$ qubit in `BDLCQ1` under `bdlGXQ0`. -/
lemma card_filter_bdlGXQ0_le_one_of_ne_inr_inr {Q M_Z M_X : Type}
    [Fintype Q] [DecidableEq Q] [Fintype M_Z] [DecidableEq M_Z] [Fintype M_X] [DecidableEq M_X]
    (pcode : CSSCode3D Q M_Z M_X) (M : ℕ) (sv0 : ShellVertex pcode M) (b0 : Fin 3)
    (h_not_z : ∀ z : M_Z, sv0.val.1.val.2 ≠ Sum.inr (Sum.inr z)) :
    (Finset.univ.filter (fun qQ : BDLCQ1 pcode M =>
      bdlGXQ0 pcode M (Sum.inr (sv0, b0)) qQ ≠ 0)).card ≤ 1 := by
  apply card_filter_le_one_of_unique
  intro qQ1 h1 qQ2 h2
  dsimp [bdlGXQ0] at h1 h2
  split_ifs at h1 with hc1 <;> [skip; exact False.elim (h1 rfl)]
  split_ifs at h2 with hc2 <;> [skip; exact False.elim (h2 rfl)]
  have hv : qQ1.1 = qQ2.1 :=
    projXq0ToBoundaryX0_inj_of_ne_inr_inr pcode M qQ1.1 qQ2.1 sv0.val.1.val.2 h_not_z hc1.2.1.symm hc2.2.1.symm
  exact Prod.ext hv (hc1.2.2.symm.trans hc2.2.2)

/-- Shows that a shell vertex check `(sv0, b0)` over a coarse $Z$-check $z_0$ acts on at
    most $2$ qubits in `BDLCQ1` under `bdlGXQ0` when coarse check overlap is at most $2$. -/
lemma card_filter_bdlGXQ0_le_two_of_inr_inr {Q M_Z M_X : Type}
    [Fintype Q] [DecidableEq Q] [Fintype M_Z] [DecidableEq M_Z] [Fintype M_X] [DecidableEq M_X]
    (pcode : CSSCode3D Q M_Z M_X) (M : ℕ) (sv0 : ShellVertex pcode M) (b0 : Fin 3) (z0 : M_Z)
    (hov : ∀ (x : M_X) (z : M_Z),
      (Finset.univ.filter (fun q : Q => pcode.checkX x q ≠ 0 ∧ pcode.checkZ z q ≠ 0)).card ≤ 2)
    (hz0 : sv0.val.1.val.2 = Sum.inr (Sum.inr z0)) :
    (Finset.univ.filter (fun qQ : BDLCQ1 pcode M =>
      bdlGXQ0 pcode M (Sum.inr (sv0, b0)) qQ ≠ 0)).card ≤ 2 := by
  refine (card_filter_le_of_injOn_filter _
    (fun q : Q => pcode.checkX sv0.val.1.val.1 q ≠ 0 ∧ pcode.checkZ z0 q ≠ 0)
    (fun qQ => xq0OwnerQ pcode M qQ.1) ?_ ?_).trans (hov sv0.val.1.val.1 z0)
  -- Step 1: Map active BDLCQ1 qubits injectively to coarse qubits in the shared (x0, z0) check support.
  · intro qQ h1
    rcases qQ with ⟨q | ⟨p | eZ⟩, bQ⟩
    · dsimp [bdlGXQ0] at h1
      split_ifs at h1 with hc <;> [skip; exact False.elim (h1 rfl)]
      have h_proj : projXq0ToBoundaryX0 pcode M (Sum.inl q) = Sum.inr (Sum.inr z0) := hc.2.1.symm.trans hz0
      dsimp [projXq0ToBoundaryX0] at h_proj; injection h_proj
    · dsimp [bdlGXQ0] at h1
      split_ifs at h1 with hc <;> [skip; exact False.elim (h1 rfl)]
      have h_proj : projXq0ToBoundaryX0 pcode M (Sum.inr (Sum.inl p)) = Sum.inr (Sum.inr z0) := hc.2.1.symm.trans hz0
      dsimp [projXq0ToBoundaryX0] at h_proj; injection h_proj with h_proj; injection h_proj
    · dsimp [bdlGXQ0] at h1
      split_ifs at h1 with hc <;> [skip; exact False.elim (h1 rfl)]
      have h_proj : projXq0ToBoundaryX0 pcode M (Sum.inr (Sum.inr eZ)) = Sum.inr (Sum.inr z0) := hc.2.1.symm.trans hz0
      dsimp [projXq0ToBoundaryX0] at h_proj
      injection h_proj with h_proj; injection h_proj with heZ_z
      dsimp [xq0OwnerQ] at h1 ⊢
      exact ⟨h1, heZ_z ▸ eZ.property⟩
  -- Step 2: Verify injectivity of xq0OwnerQ on the active BDLCQ1 support fiber.
  · intro qQ1 h1 qQ2 h2 h_eq
    rcases qQ1 with ⟨_ | ⟨_ | eZ1⟩, bQ1⟩
    · dsimp [bdlGXQ0] at h1
      split_ifs at h1 with hc1 <;> [skip; exact False.elim (h1 rfl)]
      have h_proj1 : projXq0ToBoundaryX0 pcode M (Sum.inl _) = Sum.inr (Sum.inr z0) := hc1.2.1.symm.trans hz0
      injection h_proj1
    · dsimp [bdlGXQ0] at h1
      split_ifs at h1 with hc1 <;> [skip; exact False.elim (h1 rfl)]
      have h_proj1 : projXq0ToBoundaryX0 pcode M (Sum.inr (Sum.inl _)) = Sum.inr (Sum.inr z0) := hc1.2.1.symm.trans hz0
      injection h_proj1 with h_proj1; injection h_proj1
    · rcases qQ2 with ⟨_ | ⟨_ | eZ2⟩, bQ2⟩
      · dsimp [bdlGXQ0] at h2
        split_ifs at h2 with hc2 <;> [skip; exact False.elim (h2 rfl)]
        have h_proj2 : projXq0ToBoundaryX0 pcode M (Sum.inl _) = Sum.inr (Sum.inr z0) := hc2.2.1.symm.trans hz0
        injection h_proj2
      · dsimp [bdlGXQ0] at h2
        split_ifs at h2 with hc2 <;> [skip; exact False.elim (h2 rfl)]
        have h_proj2 : projXq0ToBoundaryX0 pcode M (Sum.inr (Sum.inl _)) = Sum.inr (Sum.inr z0) := hc2.2.1.symm.trans hz0
        injection h_proj2 with h_proj2; injection h_proj2
      · dsimp [bdlGXQ0] at h1 h2
        split_ifs at h1 with hc1 <;> [skip; exact False.elim (h1 rfl)]
        split_ifs at h2 with hc2 <;> [skip; exact False.elim (h2 rfl)]
        have h_proj1 : projXq0ToBoundaryX0 pcode M (Sum.inr (Sum.inr eZ1)) = Sum.inr (Sum.inr z0) := hc1.2.1.symm.trans hz0
        have h_proj2 : projXq0ToBoundaryX0 pcode M (Sum.inr (Sum.inr eZ2)) = Sum.inr (Sum.inr z0) := hc2.2.1.symm.trans hz0
        injection h_proj1 with h_proj1; injection h_proj1 with hz1
        injection h_proj2 with h_proj2; injection h_proj2 with hz2
        dsimp [xq0OwnerQ] at h_eq
        have heZ : eZ1 = eZ2 := Subtype.ext (Prod.ext h_eq (hz1.trans hz2.symm))
        exact Prod.ext (congr_arg (fun e => Sum.inr (Sum.inr e)) heZ) (hc1.2.2.symm.trans hc2.2.2)

/-! ## 3. Azimuthal Segment Support Bounds for bdlDeltaX0 -/

lemma bdlDeltaX0_radial_inr_ne_zero_imp {Q M_Z M_X : Type}
    [Fintype Q] [DecidableEq Q] [Fintype M_Z] [DecidableEq M_Z] [Fintype M_X] [DecidableEq M_X]
    (pcode : CSSCode3D Q M_Z M_X) (M : ℕ) (sv0 : ShellVertex pcode M) (b0 : Fin 3)
    (p : RadialVertex pcode M × Fin 3)
    (hne : bdlDeltaX0 pcode M (Sum.inr (sv0, b0)) (Sum.inl p) ≠ 0) :
    (p.1.val, p.2) = (sv0, b0) ∨ (p.1.val.val.2.val ≠ 0 ∧ radialParentVertex pcode M p.1.val = sv0 ∧ p.2 = b0) := by
  rcases p with ⟨⟨sv, h_nd⟩, b⟩
  unfold bdlDeltaX0 at hne; dsimp only at hne ⊢
  by_cases hr0 : sv.val.2.val = 0
  · rw [if_pos hr0] at hne
    rcases add_ite_one_ne_zero_imp hne with hc | hc
    · injection hc
    · injection hc with hc; exact Or.inl hc.symm
  · rw [if_neg hr0] at hne
    rcases add_ite_one_ne_zero_imp hne with hc | hc
    · injection hc with hc; injection hc with hsv hb
      exact Or.inr ⟨hr0, hsv.symm, hb.symm⟩
    · injection hc with hc; exact Or.inl hc.symm

/-- Bounds the azimuthal segment support of `bdlDeltaX0` at a shell vertex over a coarse
    qubit $q_0$ by $d_{QZ} \le 4$. -/
lemma card_filter_bdlDeltaX0_azim_inl_le_four {Q M_Z M_X : Type}
    [Fintype Q] [DecidableEq Q] [Fintype M_Z] [DecidableEq M_Z] [Fintype M_X] [DecidableEq M_X]
    (pcode : CSSCode3D Q M_Z M_X) (M : ℕ)
    (hdQZ : ∀ q : Q, (Finset.univ.filter (fun z : M_Z => pcode.checkZ z q ≠ 0)).card ≤ 4)
    (sv0 : ShellVertex pcode M) (b0 : Fin 3) (q0 : Q)
    (hq0 : sv0.val.1.val.2 = Sum.inl q0) :
    (Finset.univ.filter (fun p : ShellSegment pcode M × Fin 3 =>
      bdlDeltaX0 pcode M (Sum.inr (sv0, b0)) (Sum.inr (Sum.inl p)) ≠ 0)).card ≤ 4 := by
  refine (card_filter_le_of_injOn_filter _
    (fun z : M_Z => pcode.checkZ z q0 ≠ 0)
    (fun p => p.1.val.1.val.2.val.2) ?_ ?_).trans (hdQZ q0)
  -- Step 1: Map active azimuthal segments over coarse qubit q0 to coarse Z-checks incident to q0.
  · intro ⟨seg, b⟩ hp
    unfold bdlDeltaX0 at hp; dsimp only at hp
    rcases add_ite_one_ne_zero_imp hp with h | h
    · injection h with h; injection h with hsv _
      have hv : bxStart pcode M seg.val.1.val.2 seg.val.2.2 = Sum.inl q0 :=
        (congr_arg (fun s : ShellVertex pcode M => s.val.1.val.2) hsv).symm.trans hq0
      dsimp [bxStart, armStart, projXq0ToBoundaryX0] at hv
      split_ifs at hv with hk0
      injection hv with hq_eq
      exact hq_eq ▸ seg.val.1.val.2.property
    · injection h with h; injection h with hsv _
      have hv : shellSegEndV pcode M seg = Sum.inl q0 :=
        (congr_arg (fun s : ShellVertex pcode M => s.val.1.val.2) hsv).symm.trans hq0
      exact False.elim (shellSegEndV_ne_inl pcode M seg q0 hv)
  -- Step 2: Prove injectivity of the projection to M_Z and apply hdQZ q0 ≤ 4.
  · intro ⟨seg1, b1⟩ hp1 ⟨seg2, b2⟩ hp2 h_eq
    unfold bdlDeltaX0 at hp1 hp2; dsimp only at hp1 hp2
    rcases add_ite_one_ne_zero_imp hp1 with h1 | h1 <;>
      [skip; (injection h1 with h1; injection h1 with hsv1 _;
              exact False.elim (shellSegEndV_ne_inl pcode M seg1 q0
                ((congr_arg (fun s : ShellVertex pcode M => s.val.1.val.2) hsv1).symm.trans hq0)))]
    rcases add_ite_one_ne_zero_imp hp2 with h2 | h2 <;>
      [skip; (injection h2 with h2; injection h2 with hsv2 _;
              exact False.elim (shellSegEndV_ne_inl pcode M seg2 q0
                ((congr_arg (fun s : ShellVertex pcode M => s.val.1.val.2) hsv2).symm.trans hq0)))]
    injection h1 with h1; injection h1 with hsv1 hb1
    injection h2 with h2; injection h2 with hsv2 hb2
    have hv1 : bxStart pcode M seg1.val.1.val.2 seg1.val.2.2 = Sum.inl q0 :=
      (congr_arg (fun s : ShellVertex pcode M => s.val.1.val.2) hsv1).symm.trans hq0
    have hv2 : bxStart pcode M seg2.val.1.val.2 seg2.val.2.2 = Sum.inl q0 :=
      (congr_arg (fun s : ShellVertex pcode M => s.val.1.val.2) hsv2).symm.trans hq0
    dsimp [bxStart, armStart, projXq0ToBoundaryX0] at hv1 hv2
    split_ifs at hv1 with hk1
    split_ifs at hv2 with hk2
    injection hv1 with hq1; injection hv2 with hq2
    have hx1 : seg1.val.1.val.1 = sv0.val.1.val.1 :=
      (congr_arg (fun s : ShellVertex pcode M => s.val.1.val.1) hsv1).symm
    have hx2 : seg2.val.1.val.1 = sv0.val.1.val.1 :=
      (congr_arg (fun s : ShellVertex pcode M => s.val.1.val.1) hsv2).symm
    have hr1 : seg1.val.2.1 = sv0.val.2 :=
      (congr_arg (fun s : ShellVertex pcode M => s.val.2) hsv1).symm
    have hr2 : seg2.val.2.1 = sv0.val.2 :=
      (congr_arg (fun s : ShellVertex pcode M => s.val.2) hsv2).symm
    have heZ : seg1.val.1.val.2 = seg2.val.1.val.2 :=
      Subtype.ext (Prod.ext (hq1.trans hq2.symm) h_eq)
    have hs : seg1.val.1 = seg2.val.1 :=
      Subtype.ext (Prod.ext (hx1.trans hx2.symm) heZ)
    exact Prod.ext (Subtype.ext (Prod.ext hs (Prod.ext (hr1.trans hr2.symm) (Fin.ext (by dsimp only; omega)))))
      (hb1.symm.trans hb2)

/-- Bounds the azimuthal segment support of `bdlDeltaX0` at a shell vertex over a subdivided
    $Z$-arm vertex `(eZ0, j0)` by $2$. -/
lemma card_filter_bdlDeltaX0_azim_inr_inl_le_two {Q M_Z M_X : Type}
    [Fintype Q] [DecidableEq Q] [Fintype M_Z] [DecidableEq M_Z] [Fintype M_X] [DecidableEq M_X]
    (pcode : CSSCode3D Q M_Z M_X) (M : ℕ)
    (sv0 : ShellVertex pcode M) (b0 : Fin 3) (eZ0 : ActiveZ pcode) (j0 : Fin M)
    (hej0 : sv0.val.1.val.2 = Sum.inr (Sum.inl (eZ0, j0))) :
    (Finset.univ.filter (fun p : ShellSegment pcode M × Fin 3 =>
      bdlDeltaX0 pcode M (Sum.inr (sv0, b0)) (Sum.inr (Sum.inl p)) ≠ 0)).card ≤ 2 := by
  -- Step 1: Split azimuthal segments over (eZ0, j0) into start-vertex and end-vertex families.
  have h_split := card_filter_le_add_of_or
    (fun p : ShellSegment pcode M × Fin 3 =>
      bdlDeltaX0 pcode M (Sum.inr (sv0, b0)) (Sum.inr (Sum.inl p)) ≠ 0)
    (fun p => shellSegStartVertex pcode M p.1 = sv0 ∧ p.2 = b0)
    (fun p => shellSegEndVertex pcode M p.1 = sv0 ∧ p.2 = b0)
    (fun ⟨seg, b⟩ hp => by
      unfold bdlDeltaX0 at hp; dsimp only at hp
      rcases add_ite_one_ne_zero_imp hp with h | h
      · injection h with h; injection h with hsv hb
        exact Or.inl ⟨hsv.symm, hb.symm⟩
      · injection h with h; injection h with hsv hb
        exact Or.inr ⟨hsv.symm, hb.symm⟩)
  -- Step 2: Show both the start-vertex and end-vertex families have cardinality at most 1.
  have h_start : (Finset.univ.filter (fun p : ShellSegment pcode M × Fin 3 =>
      shellSegStartVertex pcode M p.1 = sv0 ∧ p.2 = b0)).card ≤ 1 := by
    apply card_filter_le_one_of_unique
    intro ⟨seg1, b1⟩ ⟨hsv1, hb1⟩ ⟨seg2, b2⟩ ⟨hsv2, hb2⟩
    dsimp only at hsv1 hb1 hsv2 hb2
    have hv1 : bxStart pcode M seg1.val.1.val.2 seg1.val.2.2 = Sum.inr (Sum.inl (eZ0, j0)) :=
      (congr_arg (fun s : ShellVertex pcode M => s.val.1.val.2) hsv1).trans hej0
    have hv2 : bxStart pcode M seg2.val.1.val.2 seg2.val.2.2 = Sum.inr (Sum.inl (eZ0, j0)) :=
      (congr_arg (fun s : ShellVertex pcode M => s.val.1.val.2) hsv2).trans hej0
    dsimp [bxStart, armStart, projXq0ToBoundaryX0] at hv1 hv2
    split_ifs at hv1 with hk1
    split_ifs at hv2 with hk2
    injection hv1 with hv1; injection hv1 with hej1
    injection hv2 with hv2; injection hv2 with hej2
    injection hej1 with heZ1 hj1; injection hej2 with heZ2 hj2
    have hj1_val : seg1.val.2.2.val - 1 = j0.val := congr_arg Fin.val hj1
    have hj2_val : seg2.val.2.2.val - 1 = j0.val := congr_arg Fin.val hj2
    have hx1 := congr_arg (fun s : ShellVertex pcode M => s.val.1.val.1) hsv1
    have hx2 := congr_arg (fun s : ShellVertex pcode M => s.val.1.val.1) hsv2
    have hr1 := congr_arg (fun s : ShellVertex pcode M => s.val.2) hsv1
    have hr2 := congr_arg (fun s : ShellVertex pcode M => s.val.2) hsv2
    have hs : seg1.val.1 = seg2.val.1 :=
      Subtype.ext (Prod.ext (hx1.trans hx2.symm) (heZ1.trans heZ2.symm))
    exact Prod.ext (Subtype.ext (Prod.ext hs (Prod.ext (hr1.trans hr2.symm) (Fin.ext (by dsimp only; omega)))))
      (hb1.trans hb2.symm)
  have h_end : (Finset.univ.filter (fun p : ShellSegment pcode M × Fin 3 =>
      shellSegEndVertex pcode M p.1 = sv0 ∧ p.2 = b0)).card ≤ 1 := by
    apply card_filter_le_one_of_unique
    intro ⟨seg1, b1⟩ ⟨hsv1, hb1⟩ ⟨seg2, b2⟩ ⟨hsv2, hb2⟩
    dsimp only at hsv1 hb1 hsv2 hb2
    have hv1 : shellSegEndV pcode M seg1 = Sum.inr (Sum.inl (eZ0, j0)) :=
      (congr_arg (fun s : ShellVertex pcode M => s.val.1.val.2) hsv1).trans hej0
    have hv2 : shellSegEndV pcode M seg2 = Sum.inr (Sum.inl (eZ0, j0)) :=
      (congr_arg (fun s : ShellVertex pcode M => s.val.1.val.2) hsv2).trans hej0
    dsimp [shellSegEndV] at hv1 hv2
    split_ifs at hv1 with hk1 <;> [skip; (injection hv1 with hv1; injection hv1)]
    split_ifs at hv2 with hk2 <;> [skip; (injection hv2 with hv2; injection hv2)]
    injection hv1 with hv1; injection hv1 with hej1
    injection hv2 with hv2; injection hv2 with hej2
    injection hej1 with heZ1 hj1; injection hej2 with heZ2 hj2
    have hj1_val : seg1.val.2.2.val = j0.val := congr_arg Fin.val hj1
    have hj2_val : seg2.val.2.2.val = j0.val := congr_arg Fin.val hj2
    have hx1 := congr_arg (fun s : ShellVertex pcode M => s.val.1.val.1) hsv1
    have hx2 := congr_arg (fun s : ShellVertex pcode M => s.val.1.val.1) hsv2
    have hr1 := congr_arg (fun s : ShellVertex pcode M => s.val.2) hsv1
    have hr2 := congr_arg (fun s : ShellVertex pcode M => s.val.2) hsv2
    have hs : seg1.val.1 = seg2.val.1 :=
      Subtype.ext (Prod.ext (hx1.trans hx2.symm) (heZ1.trans heZ2.symm))
    exact Prod.ext (Subtype.ext (Prod.ext hs (Prod.ext (hr1.trans hr2.symm) (Fin.ext (by dsimp only; omega)))))
      (hb1.trans hb2.symm)
  omega

/-- Bounds the azimuthal segment support of `bdlDeltaX0` at a shell vertex over a coarse
    $Z$-check $z_0$ by $2$ using the coarse check overlap bound. -/
lemma card_filter_bdlDeltaX0_azim_inr_inr_le_two {Q M_Z M_X : Type}
    [Fintype Q] [DecidableEq Q] [Fintype M_Z] [DecidableEq M_Z] [Fintype M_X] [DecidableEq M_X]
    (pcode : CSSCode3D Q M_Z M_X) (M : ℕ)
    (hov : ∀ (x : M_X) (z : M_Z),
      (Finset.univ.filter (fun q : Q => pcode.checkX x q ≠ 0 ∧ pcode.checkZ z q ≠ 0)).card ≤ 2)
    (sv0 : ShellVertex pcode M) (b0 : Fin 3) (z0 : M_Z)
    (hz0 : sv0.val.1.val.2 = Sum.inr (Sum.inr z0)) :
  -- Step 1: Map azimuthal segments over coarse Z-check z0 to coarse qubits in checkX ∩ checkZ.
    (Finset.univ.filter (fun p : ShellSegment pcode M × Fin 3 =>
      bdlDeltaX0 pcode M (Sum.inr (sv0, b0)) (Sum.inr (Sum.inl p)) ≠ 0)).card ≤ 2 := by
  refine (card_filter_le_of_injOn_filter _
    (fun q : Q => pcode.checkX sv0.val.1.val.1 q ≠ 0 ∧ pcode.checkZ z0 q ≠ 0)
    (fun p => p.1.val.1.val.2.val.1) ?_ ?_).trans (hov sv0.val.1.val.1 z0)
  · intro ⟨seg, b⟩ hp
    unfold bdlDeltaX0 at hp; dsimp only at hp
    rcases add_ite_one_ne_zero_imp hp with h | h
    · injection h with h; injection h with hsv _
      have hv : bxStart pcode M seg.val.1.val.2 seg.val.2.2 = Sum.inr (Sum.inr z0) :=
        (congr_arg (fun s : ShellVertex pcode M => s.val.1.val.2) hsv).symm.trans hz0
      exact False.elim (bxStart_ne_inr_inr pcode M seg.val.1.val.2 seg.val.2.2 z0 hv)
    · injection h with h; injection h with hsv _
      have hx : seg.val.1.val.1 = sv0.val.1.val.1 :=
  -- Step 2: Prove injectivity of the coarse qubit projection and apply hov ≤ 2.
        (congr_arg (fun s : ShellVertex pcode M => s.val.1.val.1) hsv).symm
      have hv : shellSegEndV pcode M seg = Sum.inr (Sum.inr z0) :=
        (congr_arg (fun s : ShellVertex pcode M => s.val.1.val.2) hsv).symm.trans hz0
      dsimp [shellSegEndV] at hv
      split_ifs at hv with hk <;> [(injection hv with hv; injection hv); skip]
      injection hv with hv; injection hv with hz_eq
      exact ⟨hx ▸ seg.val.1.property, hz_eq ▸ seg.val.1.val.2.property⟩
  · intro ⟨seg1, b1⟩ hp1 ⟨seg2, b2⟩ hp2 h_eq
    dsimp only at hp1 hp2 h_eq
    unfold bdlDeltaX0 at hp1 hp2; dsimp only at hp1 hp2
    rcases add_ite_one_ne_zero_imp hp1 with h1 | h1
    · injection h1 with h1; injection h1 with hsv1 _
      exact False.elim (bxStart_ne_inr_inr pcode M seg1.val.1.val.2 seg1.val.2.2 z0
        ((congr_arg (fun s : ShellVertex pcode M => s.val.1.val.2) hsv1).symm.trans hz0))
    · rcases add_ite_one_ne_zero_imp hp2 with h2 | h2
      · injection h2 with h2; injection h2 with hsv2 _
        exact False.elim (bxStart_ne_inr_inr pcode M seg2.val.1.val.2 seg2.val.2.2 z0
          ((congr_arg (fun s : ShellVertex pcode M => s.val.1.val.2) hsv2).symm.trans hz0))
      · injection h1 with h1; injection h1 with hsv1 hb1
        injection h2 with h2; injection h2 with hsv2 hb2
        have hv1 : shellSegEndV pcode M seg1 = Sum.inr (Sum.inr z0) :=
          (congr_arg (fun s : ShellVertex pcode M => s.val.1.val.2) hsv1).symm.trans hz0
        have hv2 : shellSegEndV pcode M seg2 = Sum.inr (Sum.inr z0) :=
          (congr_arg (fun s : ShellVertex pcode M => s.val.1.val.2) hsv2).symm.trans hz0
        dsimp [shellSegEndV] at hv1 hv2
        split_ifs at hv1 with hk1 <;> [(injection hv1 with hv1; injection hv1); skip]
        split_ifs at hv2 with hk2 <;> [(injection hv2 with hv2; injection hv2); skip]
        injection hv1 with hv1; injection hv1 with hz1
        injection hv2 with hv2; injection hv2 with hz2
        have hle1 := seg1.property; have hle2 := seg2.property
        have hx1 := (congr_arg (fun s : ShellVertex pcode M => s.val.1.val.1) hsv1).symm
        have hx2 := (congr_arg (fun s : ShellVertex pcode M => s.val.1.val.1) hsv2).symm
        have hr1 := (congr_arg (fun s : ShellVertex pcode M => s.val.2) hsv1).symm
        have hr2 := (congr_arg (fun s : ShellVertex pcode M => s.val.2) hsv2).symm
        have hr1_val := congr_arg Fin.val hr1
        have hr2_val := congr_arg Fin.val hr2
        dsimp [shellSegEndVertex] at hr1_val hr2_val
        have heZ : seg1.val.1.val.2 = seg2.val.1.val.2 :=
          Subtype.ext (Prod.ext h_eq (hz1.trans hz2.symm))
        have hs : seg1.val.1 = seg2.val.1 :=
          Subtype.ext (Prod.ext (hx1.trans hx2.symm) heZ)
        exact Prod.ext (Subtype.ext (Prod.ext hs (Prod.ext (hr1.trans hr2.symm) (Fin.ext (by dsimp only; omega)))))
          (hb1.symm.trans hb2)

end WeldedHierarchy
