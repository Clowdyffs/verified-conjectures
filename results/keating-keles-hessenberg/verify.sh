#!/usr/bin/env bash
set -euo pipefail
here=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd)
cd "$here/../../lean"
export LEAN_NUM_THREADS=${LEAN_NUM_THREADS:-1}
python3 -I "$here/replay.py"
# Offline checkouts can reuse the package clones named by the pinned manifest.
if [[ -n ${KEATING_KELES_DEPS:-} && ! -e .lake/packages ]]; then
    mkdir -p .lake
    ln -s -- "$(realpath -- "$KEATING_KELES_DEPS")" .lake/packages
fi
if [[ ! -f .lake/packages/mathlib/.lake/build/lib/lean/Mathlib/Tactic.olean ]]; then
    lake exe cache get
fi
python3 - <<'PY'
import json
import subprocess
from pathlib import Path
manifest = json.loads(Path('lake-manifest.json').read_text())
for package in manifest['packages']:
    path = Path(manifest['packagesDir']) / package['name']
    actual = subprocess.check_output(['git', '-C', path, 'rev-parse', 'HEAD'], text=True).strip()
    if actual != package['rev']:
        raise SystemExit(f"Dependency revision differs for {package['name']}")
PY
lake build Conjectures.KeatingKeles
audit=$(mktemp -d)
trap 'rm -rf -- "$audit"' EXIT
cat > "$audit/Audit.lean" <<'LEAN'
import Conjectures.KeatingKeles
#print axioms KeatingKeles.question_two
#print axioms KeatingKeles.control_four
#print axioms KeatingKeles.control_five
#print axioms KeatingKeles.maximum_recurrence
#print axioms KeatingKeles.order_four_tie
LEAN
lake env lean "$audit/Audit.lean" | tee "$audit/axioms"
python3 - "$audit/axioms" <<'PY'
import re
import sys
from pathlib import Path
audit = Path(sys.argv[1]).read_text()
names = {'question_two', 'control_four', 'control_five', 'maximum_recurrence', 'order_four_tie'}
rows = re.findall(r"'KeatingKeles\.([^']+)' depends on axioms:\s*\[([^\]]*)\]", audit)
if {name for name, _ in rows} != names or any(
        set(axioms.split(', ')) - {'propext', 'Classical.choice', 'Quot.sound'} for _, axioms in rows):
    raise SystemExit("Axiom audit failed")
PY
if lake env sh -c 'command -v lean4checker >/dev/null'; then
    lake env lean4checker Conjectures.KeatingKeles
fi
lake env leanchecker -v Conjectures.KeatingKeles
echo 'Question 2 of Keating and Keleş (2020) is true.'
echo 'U_n^(rc) attains the maximum absolute determinant at s=2, t=1 for every n >= 4.'
