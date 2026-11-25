# Standards

What it takes for a result to appear in this collection, and what the words in each entry mean.

## Solve conditions

A target is **solved** only when all six conditions hold.

1. **Pinned target.** We have the verbatim source text with its version, our restatement, and the resolved conventions, such as whether ℕ includes 0 or what "distinct" means. If the source is ambiguous, the result holds under every reasonable reading or names the reading it settles.
2. **Full resolution.** The result fully proves or fully disproves that exact statement. A special case, bounded range, weaker form or conditional theorem is `partial`, however strong.
3. **Kernel check.** The Lean kernel accepts the final theorem using only `propext`, `Classical.choice` and `Quot.sound`, and the statement audit confirms that `Statement.lean` matches the source. A lower verification level is stated wherever the result appears.
4. **Independent replay.** A second implementation in another language or library, using exact arithmetic, reproduces every number the claim depends on. `verify.sh` runs every check from a clean checkout and prints the headline values verbatim.
5. **Fresh-context review.** A new reviewer receives only the source and the entry and looks for a statement mismatch, a gap in the proof, and a prior resolution. Each finding and its resolution is logged in the entry's `AUDIT.md`.
6. **Recent novelty check.** A literature search dated no more than seven days before the solve date found no earlier resolution. The search terms and sources are listed in `AUDIT.md`. Searches can miss work, so we write "we found no earlier resolution (search dated YYYY-MM-DD)", never "first".

The **solve date** is the UTC date on which all six conditions first held.

A result that rests on an unrefereed or unverified claim is conditional. The dependency is named, kept as an explicit hypothesis in Lean, and the result is not counted as solved.

## Kinds

| Kind | Meaning |
| --- | --- |
| `proof` | The conjecture, exactly as stated, is true. |
| `disproof` | The conjecture, exactly as stated, is false. The entry gives a witness or certificate. |
| `partial` | A precisely stated part, range or weaker form is settled. Never described as "true" or "false". |

## Verification levels

| Level | Meaning |
| --- | --- |
| `lean-complete` | The Lean kernel checks the exact target statement. |
| `lean-partial` | Lean checks part of the argument. The entry names every unformalized step. |
| `computed` | Two independent implementations replay an exact computation, without Lean. |
| `written` | A written proof alone. |

## Status

| Status | Meaning |
| --- | --- |
| `verified` | Meets all solve conditions, or for a partial result the equivalent checks on its stated scope. |
| `ready` | Verified, freshly rechecked against the literature, and cleared for announcement. |
| `announced` | Announced publicly. The entry records where and when. |
| `in-paper` | Included in a paper. The entry records the arXiv identifier. |
| `withdrawn` | An error or an earlier resolution surfaced after verification. The entry stays, with the reason. |

## Lean rules

- `Statement.lean` contains only the definitions and the conjecture as a `Prop`, each beside the verbatim source text. A reviewer can audit it without reading the proof.
- Definitions are anchored by sanity lemmas that reproduce values printed in the source. For a proof, the hypotheses are shown to be satisfiable, so the statement is not vacuous.
- Mathlib definitions are reused wherever they exist.
- No `sorry`, `admit`, custom axioms, `native_decide`, `implemented_by`, `extern`, `unsafe` or options that skip kernel checking. `scripts/collection.py check` scans every published Lean file for these, and `verify.sh` checks the axioms of the final theorem.
- Every result is checked by the single toolchain and mathlib revision pinned in `lean/`.

## Corrections

If an error or earlier resolution surfaces, the entry's status becomes `withdrawn`, or its kind becomes `partial` if a smaller claim survives. The problem is recorded in the entry's `AUDIT.md` and in [HISTORY.md](../HISTORY.md), with credit to whoever found it. Nothing is deleted silently.
