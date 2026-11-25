# Result history

## 2026-11-25

Verified the positive-ratio transition problem of Keating and Keleş. The proof gives the sharp maximum and all maximizing matrices over the closed real box, including ties, for every order and every positive ratio. The order-five matrices refute the equality of upper-entry counts, and the permutation terms of every positive-ratio maximizer have a common sign. Kind `proof`, verification `lean-complete`. [Result](results/keating-keles-transitions/README.md)

Cleared the positive-ratio transition classification for announcement. Solve commit `1fa1359902b8ade6c5f3b1d333a05fe9e85323e8`. The local release-format export passed its structural checks and the full exact and Lean replay from a fresh clone. All internal review findings are closed. [Result](results/keating-keles-transitions/README.md)

Verified Question 2 of Keating and Keleş. Their fixed-subdiagonal Hessenberg matrix maximizes the absolute determinant in every order $n\ge4$. Kind `proof`, verification `lean-complete`. The clean replay of proof snapshot `9e7183fe36eab1b393cf449e3049bbbd0e52b93b` passed. [Result](results/keating-keles-hessenberg/README.md)

Question 2 of Keating and Keleş became `ready` after the release structure check and the complete result replay passed from a clean export of solve commit `b537f77f8f0f2ee6e136df771abf3ecaf5341f7b`. The draft posts and paper section are prepared; the user chooses the publication date.

Verified the four-fifths determinant question of Momihara, Suda and Xiang, restated as Problem 15 of Egan et al. Kind `proof`, verification `lean-complete`. Solve commit `df7104831195e4d404090392b0dc596c41e17c10`. The pinned theorem, exact replay, source audit and fresh-context internal review passed. [Result](results/momihara-suda-xiang-determinant/README.md)

Published the entry in the public repository https://github.com/Clowdyffs/verified-conjectures, initial commit `1551e01ad504720350ceaa0533ec83264feff2e8`, exported from development commit `175c3c7ea16b`. A fresh clone of that commit replayed in 386 seconds and the GitHub structural check passed. Not yet announced on X; status remains `verified`.

Published the [Keating–Keleş proof](results/keating-keles-hessenberg/README.md) on the public repository’s main branch at [commit 788ff29](https://github.com/Clowdyffs/verified-conjectures/commit/788ff29e4461e70a9a53a6f889a3f696d19b41b6), exported from development commit `81ff1ef298c9b91f660bb305a662af510a46b799`. A clean clone of the release commit passed the exact numerical checks and replayed all seven Lean modules in 30 seconds. The [GitHub structural check](https://github.com/Clowdyffs/verified-conjectures/actions/runs/45544283112) passed. Status is `ready` for the separate X announcement.
