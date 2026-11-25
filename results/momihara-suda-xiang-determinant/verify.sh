#!/usr/bin/env bash
set -euo pipefail
here=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd)
root=$(cd -- "$here/../.." && pwd)
audit_dir=$(mktemp -d)
trap 'rm -rf -- "$audit_dir"' EXIT
export LEAN_NUM_THREADS=${LEAN_NUM_THREADS:-2}

python3 -I "$here/replay.py" --lean-check "$audit_dir/Audit.lean"
cd "$root/lean"
if [[ -n ${NEAR_HADAMARD_DEPS:-} && ! -e .lake/packages ]]; then
    mkdir -p .lake
    ln -s -- "$(realpath -- "$NEAR_HADAMARD_DEPS")" .lake/packages
fi
if [[ ! -f .lake/packages/mathlib/.lake/build/lib/lean/Mathlib/Tactic.olean ]]; then
    lake exe cache get
fi
python3 - <<'CHECK_PINS'
import json
import subprocess
from pathlib import Path
manifest = json.loads(Path('lake-manifest.json').read_text())
for dep in manifest['packages']:
    checkout = Path(manifest['packagesDir']) / dep['name']
    revision = subprocess.check_output(['git','-C',str(checkout),'rev-parse','HEAD'], text=True).strip()
    if revision != dep['rev']:
        raise SystemExit(f"Pin mismatch for {dep['name']}: {revision}")
CHECK_PINS
lake build Conjectures.NearHadamard
lake env lean "$audit_dir/Audit.lean" | tee "$audit_dir/axioms"
python3 - "$audit_dir/axioms" <<'PY'
import re
import sys
from pathlib import Path
expected = {'NearHadamard.problem15'}
expected.update('NearHadamard.Controls.' + name for name in
                ('admissible_order30','source_decimals','class4_order30',
                 'class4_inverse_order30','class5_order30','class6_order30'))
rows = re.findall(r"'([^']+)' depends on axioms:\s*\[([^\]]*)\]", Path(sys.argv[1]).read_text())
if {name for name, _ in rows} != expected or any(
        set(axioms.split(', ')) - {'propext','Classical.choice','Quot.sound'} for _, axioms in rows):
    raise SystemExit('Missing or unexpected axiom audit')
PY
if lake env sh -c 'command -v lean4checker >/dev/null'; then
    lake env lean4checker Conjectures.NearHadamard
fi
# Lean 4.35 ships leanchecker. A module prefix covers its entire subtree.
lake env leanchecker -v Conjectures.NearHadamard
echo 'The four-fifths inequality in Problem 7.1 of Momihara, Suda and Xiang is true.'
echo '5|det M| >= 4 W_n for Classes (4), (5), and (6) at every eligible n >= 30.'
