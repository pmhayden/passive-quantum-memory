# Passive Quantum Memory in Three Dimensions

Lean 4 (`v4.35.0`) formalization of a three-dimensional passive quantum memory on open 3D cubic lattices $\mathrm{Box3D}(L_k)$, structured according to the [Mathlib Initiative `formalization.yaml`](https://github.com/mathlib-initiative/formalization.yaml) and [Palomar Registry](https://palomar-registry.org/) conventions for trust-minimized kernel verification with `lake comparator`.

## Companion Papers

- **Part I**: Patrick Hayden, *Passive Quantum Memory in Three Dimensions, Part I: Thermal and Zero-Temperature Perturbative Stability*
- **Part II**: Patrick Hayden, *Passive Quantum Memory in Three Dimensions, Part II: Robust Thermal Stability*

## Certified Challenge Theorems (`Challenge.lean` / `Solution.lean`)

The repository is organized around certifying two standalone existential spin-lattice theorems in `Challenge.lean` (stated purely over six generic spin-system modules in `Defs/`, with zero welded-code, homological-perturbation, cluster-decoder, or worldline-polymer imports):

1. **`PassiveQuantumMemory.part1_thermally_and_perturbatively_stable_memory`** (Part I, Section 7.4 (`subsec:main-theorem-synthesis`), Theorem 7.5 (`thm:main`)):
   Existence of a 3D geometrically local commuting-projector quantum memory family on open boxes $\mathrm{Box3D}(L_k)$ with ground degeneracy $\ge 2$ and safe decoded logical observables obeying $37\Lambda^k$-cube immunity that simultaneously satisfies:
   - unperturbed positive-temperature Gibbs concentration and stretched-exponential memory lifetimes ($\forall \beta > \beta_c$) under bounded-range KMS-symmetric double-commutator generators and completely positive trace-preserving (CPTP) Markovian Davies thermal baths; and
   - zero-temperature superpolynomial perturbative stability under arbitrary superpolynomially decaying Hermitian perturbations (full-spectrum relative form sandwich, approximate ground-space invariance $\lVert [H_k, P_{0,\mathrm{dress}}] \rVert \le \delta_{\mathrm{split}}(L_k)$, cube-range dressed safe-subspace immunity, and closed-system Heisenberg unitary memory lifetime).
2. **`PassiveQuantumMemory.part2_fixed_temp_perturbative_thermal_and_kms_stability`** (Part II, Section 6.3 (`subsec:main-theorems`), Theorems 6.3, 6.4, and 6.5 (`thm:main-A`, `thm:main-B`, `thm:main-D`)):
   Simultaneous unperturbed thermal stability and perturbed positive-temperature stability under general finite-range Hermitian perturbations of constant $O(1)$ coupling strength $0 \le J \le J_0$, establishing both:
   - fixed-temperature ($\beta \in (\beta_c, \beta_{\max}]$ for any ceiling $\beta_{\max} > \beta_c$) bare Gibbs failure probability and KMS-symmetric dissipative dynamical memory lifetime bounds; and
   - logarithmic-cooling ($\beta \ge C_{\mathrm{scale}} \log L_k$ down to $T = 0$) QAC-dressed Gibbs failure probability and KMS-symmetric dissipative memory lifetime bounds (the general superpolynomial-decay cryogenic theorem for all $f \in \mathcal{D}_{\mathrm{super}}$ is proved internally as `log_cooling_perturbative_thermal_stability_main` in `Proofs/PerturbativeThermalSynthesis/LogCoolingPerturbativeSynthesis.lean`).

Rather than formalizing the companion manuscripts statement-by-statement, supporting modules in `Defs/` and `Proofs/` establish the directions, parameter specializations, and operator bounds needed along the proof path to `Challenge.lean` (see Appendix A of Part I and Part II for the full scope and cross-reference).

## Repository Structure

- `Challenge.lean` — Minimal, self-contained challenge specifications for `part1_thermally_and_perturbatively_stable_memory` and `part2_fixed_temp_perturbative_thermal_and_kms_stability` (with `sorry` placeholders), stated over six generic spin-lattice definition modules in `Defs/`.
- `Solution.lean` — Complete, machine-checked proofs of both challenge theorems with zero `sorry` declarations and only Lean's three standard foundational axioms (`propext`, `Quot.sound`, `Classical.choice`).
- `Defs/` — Spin-lattice, Hilbert-space, Gibbs/KMS/Davies-bath, superpolynomial-decay, unitary-flow, abstract polymer-gas, and three-layer welded CSS code definitions.
- `Proofs/` — Formal proof modules across spherical-cap de-crowding, scale-matched relative cone acyclicity, two-stage syndrome cleaning, multiscale cluster decoding, coset Peierls bounds, CPTP Davies generator bridges, Lieb–Robinson and band-limited QAC flows, centered-ball gap bootstrap, and continuous-time Duhamel–Ursell spacetime worldline cluster expansions.
- `comparator.json` — Configuration for `lake comparator` (bundled natively with Lean `v4.35.0`).
- `formalization.yaml` — Mathlib Initiative / Palomar Registry (`v0.4`) metadata, provenance, and result inventory.

## Verification

With [`elan`](https://github.com/leanprover/elan) installed (which automatically fetches the pinned `leanprover/lean4:v4.35.0` toolchain and bundled `lake comparator` verifier from `lean-toolchain`):

```bash
lake exe cache get
lake build Defs Proofs Challenge Solution
lake comparator --config comparator.json
```

## License

Licensed under the Apache License, Version 2.0 (see [`LICENSE`](LICENSE)).
