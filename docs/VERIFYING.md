# Verifying a result

A Lean proof is only as good as the statement it proves. This page explains how to check both.

## 1. Audit the statement (about ten minutes)

Open the entry's `README.md` and its `lean/Conjectures/<Module>/Statement.lean` side by side.

- Each definition in `Statement.lean` sits beside the source text it formalizes. Compare them.
- The entry's `AUDIT.md` maps every hypothesis in the source to a line of `Statement.lean` and lists each convention we chose, with the reason.
- Check the quantifiers, the domain (for example, whether ℕ includes 0), and the edge cases against the original paper. The citation includes the version used.
- Look for the sanity lemmas that reproduce values printed in the source. They confirm that the definitions mean what the source means.
- The final theorem's type is the `Prop` defined in `Statement.lean`, or its negation, with no additional hypotheses. `verify.sh` prints its axioms.

If you find a mismatch, please [report it](../CONTRIBUTING.md).

## 2. Replay the proof

```sh
./verify.sh <slug>
```

Requirements: Python 3.10 or newer, Git, and [elan](https://github.com/leanprover/elan). The entry's README lists running time and peak memory measured on a clean clone. The script exits nonzero if any step fails.

Each `verify.sh` does the following.

| Step | What it establishes |
| --- | --- |
| Independent replay | A second implementation, usually Python's standard library with exact integers and fractions, recomputes every number the claim uses and compares it with the certificate data. It shares no code with the Lean proof. |
| Pin check | Every Lake dependency is at the commit recorded in `lean/lake-manifest.json`. |
| `lake build` | Lean elaborates and type-checks the statement and proof from source. Mathlib's prebuilt cache is used for mathlib itself, but every module of the result is rebuilt. |
| Axiom audit | `#print axioms` on the final theorem, and on the sanity lemmas, lists exactly `propext`, `Classical.choice` and `Quot.sound`. This excludes `sorry`, custom axioms and `native_decide`. |
| `leanchecker` | The kernel re-checks every declaration in the compiled modules, independently of the elaborator. |

Offline or repeat runs can reuse an existing Lake packages directory. Each entry's README names the environment variable for this.

## 3. Structural checks

```sh
python3 scripts/collection.py check
```

This needs only Python and runs in seconds. It checks that every entry has its required files and metadata, that the index is current, that every link resolves, that no published Lean file contains a forbidden construct, that every entry uses the pinned toolchain, and that each entry's Lean sources have the git tree hash recorded at its solve commit.

## What this does not establish

- That the formal statement matches the author's intent. This is what step 1 is for, and it is a human judgement.
- That the result is new. Our literature searches are dated and listed in each `AUDIT.md`, and they can miss work.
- Correctness of Lean, mathlib or your hardware. The trust base is the Lean kernel, the three standard axioms and the pinned mathlib definitions used in `Statement.lean`.
- Peer review. Every entry has had internal review only.
