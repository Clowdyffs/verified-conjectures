# Result history

## 2026-11-25

Reviewed priority and release preparation for the [sharp near-Hadamard bounds](results/momihara-suda-xiang-sharp-bounds/README.md). Added credit for Lin–Phoa and the Turyn–Whiteman antecedents of Class (4), distinguished the previous four-fifths result, and supplied the required FLINT dependency in the release instructions and manual workflow. The exact certificate, numerical replay and axiom checks passed again.

Cleared the [sharp near-Hadamard bounds](results/momihara-suda-xiang-sharp-bounds/README.md) for announcement. The clean proof replay passed, and the source and publication drafts incorporate both fresh-context internal reviews. Solve commit `7496df6f445f526e0d62309bcc0c96d65ad5bd65`. Publication timing is the user’s decision.

Verified the sharp uniform lower bounds in Problem 7.1 of Momihara, Suda and Xiang. The six attained minima cover all primitive generators on the full domain and at orders at least 30. Kind `proof`, verification `lean-complete`. [Result](results/momihara-suda-xiang-sharp-bounds/README.md)

Published the [Keating–Keleş transition classification](results/keating-keles-transitions/README.md) on the public main branch at [commit 40e4e75](https://github.com/Clowdyffs/verified-conjectures/commit/40e4e75fc0ac0c6da4c68143cd5a13335cac830b), exported from development commit 7f5f82ec30e7. A clean clone of the public commit passed the exact replay and Lean kernel verification in 42 seconds, including the order-100 headline maximum and all nine axiom audits. The [GitHub structural check](https://github.com/Clowdyffs/verified-conjectures/actions/runs/45552113339) passed. Status remains `ready` for the separate X announcement.

Verified the positive-ratio transition problem of Keating and Keleş. The proof gives the sharp maximum and all maximizing matrices over the closed real box, including ties, for every order and every positive ratio. The order-five matrices refute the equality of upper-entry counts, and the permutation terms of every positive-ratio maximizer have a common sign. Kind `proof`, verification `lean-complete`. [Result](results/keating-keles-transitions/README.md)

Cleared the positive-ratio transition classification for announcement. Solve commit `1fa1359902b8ade6c5f3b1d333a05fe9e85323e8`. The local release-format export passed its structural checks and the full exact and Lean replay from a fresh clone. All internal review findings are closed. [Result](results/keating-keles-transitions/README.md)

Verified Question 2 of Keating and Keleş. Their fixed-subdiagonal Hessenberg matrix maximizes the absolute determinant in every order $n\ge4$. Kind `proof`, verification `lean-complete`. The clean replay of proof snapshot `9e7183fe36eab1b393cf449e3049bbbd0e52b93b` passed. [Result](results/keating-keles-hessenberg/README.md)

Question 2 of Keating and Keleş became `ready` after the release structure check and the complete result replay passed from a clean export of solve commit `b537f77f8f0f2ee6e136df771abf3ecaf5341f7b`. The draft posts and paper section are prepared; the user chooses the publication date.

Verified the four-fifths determinant question of Momihara, Suda and Xiang, restated as Problem 15 of Egan et al. Kind `proof`, verification `lean-complete`. Solve commit `df7104831195e4d404090392b0dc596c41e17c10`. The pinned theorem, exact replay, source audit and fresh-context internal review passed. [Result](results/momihara-suda-xiang-determinant/README.md)

Published the entry in the public repository https://github.com/Clowdyffs/verified-conjectures, initial commit `1551e01ad504720350ceaa0533ec83264feff2e8`, exported from development commit `175c3c7ea16b`. A fresh clone of that commit replayed in 386 seconds and the GitHub structural check passed. Not yet announced on X; status remains `verified`.

Published the [Keating–Keleş proof](results/keating-keles-hessenberg/README.md) on the public repository’s main branch at [commit 788ff29](https://github.com/Clowdyffs/verified-conjectures/commit/788ff29e4461e70a9a53a6f889a3f696d19b41b6), exported from development commit `81ff1ef298c9b91f660bb305a662af510a46b799`. A clean clone of the release commit passed the exact numerical checks and replayed all seven Lean modules in 30 seconds. The [GitHub structural check](https://github.com/Clowdyffs/verified-conjectures/actions/runs/45544283112) passed. Status is `ready` for the separate X announcement.
