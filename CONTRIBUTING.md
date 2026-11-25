# Reporting an error

We want to hear about any problem with a result: a statement that does not match its source, a gap in a proof, a replay that fails, or an earlier paper that already settles the question.

Please open an issue with

- the entry, by its folder name in `results/`,
- what is wrong, with a page or line reference to the source, the proof or the Lean file,
- for a failed replay, your operating system, the output of `./verify.sh <slug>`, and the commit you ran.

What happens next is set out in [docs/STANDARDS.md](docs/STANDARDS.md#corrections). Confirmed problems are recorded in the entry's `AUDIT.md` and in [HISTORY.md](HISTORY.md), with credit to the reporter unless you ask otherwise. A result is withdrawn or narrowed in place, never deleted.

This repository publishes finished results only, so we do not accept pull requests that add new results. Fixes to typos, links and scripts are welcome.
