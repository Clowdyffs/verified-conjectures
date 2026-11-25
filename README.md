# Verified conjectures

[![check](https://github.com/Clowdyffs/verified-conjectures/actions/workflows/check.yml/badge.svg)](https://github.com/Clowdyffs/verified-conjectures/actions/workflows/check.yml)
[![Lean](https://img.shields.io/badge/Lean-v4.35.0-blue)](lean/lean-toolchain)
[![axioms](https://img.shields.io/badge/axioms-propext%20%C2%B7%20Classical.choice%20%C2%B7%20Quot.sound-brightgreen)](docs/VERIFYING.md#2-replay-the-proof)
[![license](https://img.shields.io/badge/license-Apache--2.0%20%2F%20CC%20BY%204.0-lightgrey)](NOTICE)

Published open problems that we have settled, each with a Lean proof that the kernel checks against a verbatim transcription of the original statement, and a one-command replay.

**[Results](#results)** · **[Check a result yourself](#check-a-result-yourself)** · **[Standards](docs/STANDARDS.md)** · **[Auditing a statement](docs/VERIFYING.md)** · **[Report an error](CONTRIBUTING.md)** · **[History](HISTORY.md)**

Only finished work appears here. A result is listed after it meets every [solve condition](docs/STANDARDS.md#solve-conditions): the exact statement pinned to its source, a full resolution, a kernel-checked Lean theorem using only the standard axioms, an independent exact replay in a second implementation, a fresh-context internal review, and a dated literature search. In-progress work and claims whose checks are incomplete are never published here.

**These results are unrefereed and have had internal review only.** Please [report any error](CONTRIBUTING.md). Corrections are recorded publicly in [HISTORY.md](HISTORY.md) and never removed silently.

## Results

<!-- results:start -->
### Solved

| Problem | Result | Answer | Checked by | Solved (UTC) | Details |
| :--- | :--- | :---: | :--- | :---: | :--- |
| **[Problem 7.1 of Momihara, Suda and Xiang (2022), four-fifths question](results/momihara-suda-xiang-determinant/)**<br><sub>Restated as Problem 15 of Egan, Kotsireas, London and Ó Catháin (2026)</sub> | The four-fifths bound holds for three near-Hadamard families | **True** | Lean, complete | 2026-11-25 | [Proof](results/momihara-suda-xiang-determinant/PROOF.md) · [Lean statement](lean/Conjectures/NearHadamard/Statement.lean) · [Audit](results/momihara-suda-xiang-determinant/AUDIT.md) · [Replay](results/momihara-suda-xiang-determinant/verify.sh) |
<!-- results:end -->

The same index is available as [results.json](results.json).

## Check a result yourself

Every entry is self-contained and replays from a clean clone.

```sh
git clone https://github.com/Clowdyffs/verified-conjectures
cd verified-conjectures
./verify.sh                       # every result, one at a time
./verify.sh <slug>                # one result, named by its folder in results/
```

You need Python 3.10 or newer and [elan](https://github.com/leanprover/elan), which installs the pinned Lean toolchain (`leanprover/lean4:v4.35.0`) automatically. Lake fetches the pinned mathlib and its prebuilt cache on the first run. Each entry's README gives its expected output, running time and peak memory. Some kernel checks need more than 16 GB of RAM.

For each result, the replay

1. runs a second, independent implementation in exact arithmetic and compares every number the proof depends on,
2. confirms every dependency is at the commit pinned in `lean/lake-manifest.json`,
3. builds the Lean theorem from source,
4. prints `#print axioms` for the final theorem and fails unless it is exactly `propext`, `Classical.choice` and `Quot.sound`,
5. replays the compiled modules through the kernel again with `leanchecker`,
6. prints the headline statement.

[docs/VERIFYING.md](docs/VERIFYING.md) explains what each check establishes, what it does not, and how to audit a statement against its source in about ten minutes.

## How an entry is organized

```text
results/<slug>/
  README.md     the result, the verbatim original statement, how to verify, trust base, credits
  metadata.json kind, status, verification level, Lean declaration, solve date and provenance hashes
  PROOF.md      the complete argument, readable without Lean
  AUDIT.md      source hypothesis → line of Statement.lean, conventions, dated literature searches, review findings
  verify.sh     the replay, plus any helper scripts and certificate data it reads
lean/Conjectures/<Module>/
  Statement.lean   only the definitions and the conjecture, beside the source text; audit this file
  ...              the proof
```

The final theorem always has the conjecture's own `Prop` as its type, or its negation, with no extra hypotheses. A partial result is named for what it proves and states how it relates to the original question.

## Provenance

Each entry's `metadata.json` records the UTC date on which every solve condition first held, the commit in our development repository at that moment, and the git tree hash of its Lean sources at that commit. `python3 scripts/collection.py check` recomputes the hash from the files in this repository, so the published Lean code is provably the code that was verified on the solve date. Run `git rev-parse HEAD:lean/Conjectures/<Module>` to compare it yourself.

## Standards and vocabulary

Kinds are `proof`, `disproof` and `partial`. Verification levels are `lean-complete`, `lean-partial`, `computed` and `written`. We say "internal review", never "peer review", and "we found no earlier resolution (search dated …)", never "first". The full definitions are in [docs/STANDARDS.md](docs/STANDARDS.md).

## Credits and AI assistance

The original posers of each problem are credited in its entry, along with the sources of every method and construction used. Proofs, formalizations and replays were developed with AI assistance. Each entry names the tool and model it used. Curated by Clowdyffs.

## Citing

See [CITATION.cff](CITATION.cff). Please cite the original source of each problem as well.

## License

Lean code and scripts are licensed under the [Apache License 2.0](LICENSE). Proofs, audits and other prose are licensed under [CC BY 4.0](NOTICE). The original problem statements are quoted from their sources for identification and commentary.
