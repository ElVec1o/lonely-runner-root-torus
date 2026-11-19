# Reproduction directory: Lean verification of the root-torus note

All paths below are relative to this directory (`repro/`); the Lean project is `../lean`.

## 1. What is built

Seven modules, in the order of `MANIFEST.tsv` (sha256 of each source is recorded there):

| # | module | lines | imports (project) | role |
|---|---|---|---|---|
| 1 | `NearestInteger` | 123 | none | support: distance to the nearest integer |
| 2 | `MaxLoneliness` | 95 | `NearestInteger` | support: the one-variable `ML` |
| 3 | `ObsRootTorus` | 395 | `MaxLoneliness` | Theorem 1 (root tori), `torusML` |
| 4 | `ObsConeLemma` | 902 | none | Theorem 2 (repeat lines) |
| 5 | `ObsCrystallographic` | 442 | `ObsRootTorus` | Theorem 3 (totient condition) |
| 6 | `ObsPsiBound` | 459 | `ObsRootTorus` | Theorem 4, Corollary 5 |
| 7 | `ObsPsiTable` | 55 | `ObsPsiBound` | Corollary 5(iv): cardinalities for N = 18, 24, 30 |

No module imports modules 3 to 7, and there is no aggregator: each is built by name, with its project imports already built.

## 2. Requirements

`elan` with `leanprover/lean4:v4.30.0` (`../lean/lean-toolchain`), Lake 5.0.0, the Mathlib cache for revision `c5ea00351c28e24afc9f0f84379aa41082b1188f` (`lake exe cache get` in `../lean`; needs network; not done by the scripts), about 3 GB free disk.
Memory: the author's logs of the builds of these modules show a largest sampled peak of 7.3 GB for one `lean` process; build one module at a time and keep 10 GB free. Build times were not recorded in this archive (`EXPECTED.tsv` is empty).

## 3. Commands

```
bash build.sh --plan                 # validate: sources present, sha256 = MANIFEST, order topological, pins, disk; no lake
bash build.sh --status               # plan, then `lake build --no-build` per module: UP-TO-DATE / NEEDS-BUILD
bash build.sh --run                  # build the 7 modules one at a time, resumable (results in logs/build_results.tsv)
bash check_axioms.sh                 # after the build: print axioms of the listed declarations and a planted-sorry control; expect VERDICT: PASS
```

`build.sh` options and environment variables (`WRAPPER`, `GATE_LIMIT_MB`, `GATE_RESERVE_MB`, `LOCK`, `DISK_FLOOR_GB`) are documented at the top of the script. It builds exactly one module per `lake build LRSpectrumFull.<Module>` call, after all of that module's project imports have been built, with a memory gate on the `lean` processes of the machine.
`check_axioms.sh` builds nothing: it reads the compiled modules, counts the printed axiom lines against the number of `#print axioms` commands, requires every listed declaration to print exactly `[propext, Classical.choice, Quot.sound]`, and requires the two planted-`sorry` controls to print `sorryAx`.

## 4. Status of the checks

* `build.sh --plan` was run on this directory's copy of the sources on 19 November 2026 (sources present, sha256 as in `MANIFEST.tsv`).
* Docstrings and comments of four modules were rewritten for publication after they were built (code unchanged; see the main README); `MANIFEST.tsv` records the hashes of the files in this archive.
* The axiom prints of the five note modules were made on 15 and 16 November 2026 on the author's machine, before this archive was assembled; `check_axioms.sh` itself and its declaration list were prepared on 17 November 2026 and not run in this form before release. Run it once; a `VERDICT: FAIL` here would mean a mistyped declaration name or a real difference, and the printout says which.
