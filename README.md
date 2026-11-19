# Critical two-dimensional subtori of the torus: root systems, repeat lines, and torsion points

Repository: https://github.com/ElVec1o/lonely-runner-root-torus
DOI: https://doi.org/10.5281/zenodo.24357912 (version 1.0.0); all versions: https://doi.org/10.5281/zenodo.24357911
Version 1.0.0 (November 2026). Author: Vico Bonfioli. License: CC-BY-4.0 (`LICENSE.md`).
Note: `paper/main.pdf` (19 pages; source `paper/main.tex`). Not peer reviewed.

## Abstract

For integer linear forms `l_1,...,l_n` in two variables, let `M` be the supremum over the plane of `min_r dist(l_r(s,t))`, where `dist` is the distance to the nearest integer: the largest distance from the coordinate walls reached by the corresponding two-dimensional subtorus of `T^n`. We prove four statements and verify each in Lean 4 with Mathlib; the formal statements are slightly weaker in places, which Section 9 of the paper lists.
(1) The coefficient lists of the positive roots of `A_2, B_2, G_2` have `M = 1/3, 1/4, 1/6`, that is `1/h` for the Coxeter number `h` and the number `n = h` of forms; the tori `U^2` of Jain and Kravitz and `U_C` of Cordella are the tori of `B_2` and `G_2`. The upper bound is a finite case check (2, 6 and 120 cases) closed by the Lean kernel.
(2) If `n` forms are pairwise distinct up to sign and fall into `d >= 2` proportionality classes, then at least `2n - d` lines of the plane carry two coordinates that agree up to sign while no coordinate vanishes.
(3) A condition on the absolute values of the coordinates of an integer vector in the plane forces `phi(N) = 2` for Euler's function.
(4) If every form has content coprime to `N` and `n` is smaller than the number of points of the projective line over `Z/N`, then `M >= 1/N`; consequently, for every `n >= 5` with `n != 6`, a list of `n` forms with coprime entries has `M > 1/n`, and `M = 1/n` for a list with coprime entries forces `n` in `{2,3,4,6}`.
One conjecture, supported by exact computation in bounded boxes and not proved, is stated at the end of the paper.
**Novelty is partial and no field-level claim is made**: the values for `B_2` and `A_2` are in Yi, Gill and Bu (arXiv:2610.40694, Lemma 8.3 and Lemma 9.4), the value for `G_2` is Theorem 3.7 of Cordella (arXiv:2609.03444), `B_2` is the torus `U^2` of Jain and Kravitz; what is added is the Lean verification, the root-system dictionary, the sharp count `2n - d` for every `n`, and the torsion and totient bounds. The note has no bearing on the lonely runner conjecture itself.

## Main results

All statements below are in Lean (label VERIFIED, see "Trust"); the paper says exactly which clause is formal and which is only remarked. Namespaces are `LRSpectrumFull.<module>`.

| paper | Lean module | main declarations |
|---|---|---|
| Theorem 1 (root tori) | `ObsRootTorus` | `torusML_A2`, `torusML_B2`, `torusML_G2`, `torusGap_diag`, `torusML_JK_U2`, `torusML_Cordella_UC`, `JK_U2_forms_eq_B2`, `Cordella_UC_forms_eq_G2`, controls `control_A2'`, `control_B2'`, `control_G2'` |
| Theorem 2 (repeat lines) | `ObsConeLemma` | `cone_lemma`, `cone_lemma_normalised`, `A2_free_card`, `A2_slope_card` |
| Theorem 3 (totient condition) | `ObsCrystallographic` | `crystallographic_pair`, `crystallographic_lemma`, `totient_eq_two_iff` |
| Theorem 4, Corollary 5 (torsion points) | `ObsPsiBound`, `ObsPsiTable` | `torusML_ge_inv_of_two_mul_sub_totient`, `torusML_ge_inv_of_projReps`, `torusML_gt_inv_of_primitive`, `primitive_critical_card`, `primitive_totient_two`, `torusML_ge_one_sixth_of_primitive`, `torusML_ge_primitive_table`, `psiDed_table` |

`torusML g1 g2` is the supremum of `torusGap` (the minimum over the forms of `nearestIntDist`) over the plane; for `g2 = 0` it equals the one-variable `ML` of `MaxLoneliness.lean` (`torusML_zero_snd`).
The map from every statement of the paper to Lean declarations, with one sentence each, is in Section 9 of the paper.

## Idea in words

A two-dimensional torus is a plane wound around a cube, and `M` is how far the plane gets from all faces. Two devices bound `M` from below. Adding or subtracting two forms gives a line in the plane on which two coordinates agree up to sign, so the problem on that line has fewer speeds; counting such lines is Theorem 2. Alternatively, sample the plane at the points of order `N`: a form with content coprime to `N` vanishes at exactly one cyclic subgroup of order `N`, and when there are more cyclic subgroups than forms some point survives, at distance at least `1/N` from every face (Theorem 4). The lists for which `1/n` is reached are those with no level `N < n` that has room; for `n = 3, 4, 6` they are the root tori (Theorem 1), whose value `1/h` is checked exactly by cutting the plane into finitely many cells and refuting each one.

## What is not claimed

No identification of the three lists with positive roots, no statement about general root systems or the Coxeter number, no statement about rank at least 3 in Lean (the paper states these only as remarks or cites the literature, and says so). The conjecture at the end of the paper is not proved: it rests on exact computation in bounded boxes, exhaustive within the boxes and unresolved outside them.
The computations behind the conjecture (paper, Section 8) are exact-integer programs that are not part of this archive and are not Lean-verified.
No proof of the lonely runner conjecture. No human referee has checked the proofs. No withdrawal or retraction notice applies to this release.

## Trust

* Lean 4.30.0 (`leanprover/lean4:v4.30.0`) and Mathlib at revision `c5ea00351c28e24afc9f0f84379aa41082b1188f` (pinned in `lean/lake-manifest.json`).
* Axioms: `repro/check_axioms.sh` prints `#print axioms` for the declarations above and a planted-`sorry` control and judges the printout; the expected result is exactly `[propext, Classical.choice, Quot.sound]` for every listed declaration and `sorryAx` for the two controls.
  Axiom prints made on the author's machine on 15 and 16 November 2026, while the modules were being written, gave the same result. The script in this archive and its declaration list were written afterwards and have not yet been run in this form: run it once after the build.
* Source scan (17 November 2026, comments stripped): the code of the seven modules contains no `sorry`, `native_decide`, `axiom`, `unsafe`, `implemented_by`, `extern`, `opaque`, `Classical.choose`, `ofReduceBool`, `skipKernelTC` or `autoImplicit`; `decide +kernel` is used 18 times; `set_option` is used only for linter switches.
* Not guaranteed: that each Lean statement is the mathematical statement of the paper (the paper's Section 9 says in words what each declaration states; a fresh reading of the signatures found no mismatch, and that reading is not a human expert's review).

## Reproduction

Requirements: `elan` with the toolchain above, the Mathlib cache for the pinned revision (`lake exe cache get`, needs network, not done by the scripts), about 3 GB free disk, and enough memory for one `lean` process (the author's logs for these modules show a largest sampled peak of 7.3 GB; keep 10 GB free). The seven modules build one at a time.

```
cd repro
bash build.sh --plan        # validate sources, hashes, build order, pins; builds nothing
bash build.sh --run         # build the 7 modules in order, one at a time, resumable
bash check_axioms.sh        # after the build: print and judge the axioms; expect VERDICT: PASS
```

Do not run a bare `lake build` in `lean/` (the lakefile has no default target, so it would do nothing). The five note modules are leaf modules: nothing imports them, so no top-level build target builds them; each is built by name, with its imports already built.

## File map

| path | content |
|---|---|
| `paper/main.tex`, `paper/main.pdf` | the note |
| `lean/` | Lake project: `lean-toolchain`, `lakefile.toml`, `lake-manifest.json`, `LRSpectrumFull/` with the 5 note modules (`ObsRootTorus` 395 lines, `ObsConeLemma` 902, `ObsCrystallographic` 442, `ObsPsiBound` 459, `ObsPsiTable` 55) and the 2 support modules they import (`MaxLoneliness`, `NearestInteger`) |
| `repro/` | `build.sh`, `check_axioms.sh`, `check_axioms.lean`, `MANIFEST.tsv` (module order and sha256), `EXPECTED.tsv`, `README.md` |
| `CHECKSUMS.sha256` | sha256 of every file of this repository (except itself) |
| `CITATION.cff`, `.zenodo.json`, `LICENSE.md` | citation and archive metadata, license |

**Docstrings and comments.** In 4 of the 7 Lean modules (`ObsRootTorus`, `ObsConeLemma`, `ObsCrystallographic`, `ObsPsiBound`) docstrings and comments were rewritten for publication (references to internal working notes were removed) after the modules were built on the author's machine. The code, declarations and proofs are identical (checked by comparing the sources with comments stripped), so the kernel content is the same; but the sha256 of those 4 files differ from the files that were built.

## Provenance

The Lean modules, the proofs and the first draft of the note were produced by an AI system (Claude, Anthropic); the questions, the research directions and the decision to formalize these statements came from Vico Bonfioli. Here "checked" means accepted by the Lean kernel; no human referee has checked the proofs.

## Prior art and credit

* Jain and Kravitz, *Relative Lonely Runner spectra*, Combinatorial Theory 6 (2026), Paper 1; arXiv:2411.12684 (classification of two-dimensional tori with `D = 1/4`, the torus `U^2`).
* Cordella, *Odd denominators in the Lonely Runner spectrum for six speeds*, arXiv:2609.03444 (v2): the torus `U_C`, Theorem 3.7, Lemma 3.4, Theorem 3.8.
* Yi, Gill and Bu, *Four runners that are barely lonely*, arXiv:2610.40694 (v1): Lemma 8.3 (the `B_2` value), Lemma 9.4, Lemma 11.2, Theorem 11.5.
* Giri and Kravitz, Fan and Sun, Kravitz, Wills, Cusick: see the reference list of the paper.
