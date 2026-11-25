#!/usr/bin/env bash
set -euo pipefail
here=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd)
root=$(cd -- "$here/../.." && pwd)
work=$(mktemp -d)
trap 'rm -rf -- "$work"' EXIT
export LEAN_NUM_THREADS=1
flint_python=${SHARP_FLINT_PYTHON:-python3}
"$flint_python" -Ic 'import flint; assert flint.__version__ == "0.9.0", flint.__version__'

# Serialize heavy phases individually, allowing other research jobs between modules.
heavy() (
    exec 9>/tmp/proofs-conjectures-heavy.lock
    flock -x 9
    free -g
    ps -eo pid,rss,comm --sort=-rss | head -n 8 || true
    "$@"
)
reference() {
    "$flint_python" -IB "$here/reference.py" > "$work/certificates.tsv"
}
heavy reference
cmp "$here/certificates.tsv" "$work/certificates.tsv"
heavy python3 -IB "$here/replay.py"

cd "$root/lean"
if [[ -n ${NEAR_HADAMARD_DEPS:-} && ! -e .lake/packages ]]; then
    mkdir -p .lake
    ln -s -- "$(realpath -- "$NEAR_HADAMARD_DEPS")" .lake/packages
fi
if [[ ! -f .lake/packages/mathlib/.lake/build/lib/lean/Mathlib/Tactic.olean ]]; then
    heavy lake exe cache get
fi
python3 - <<'PY'
import json, subprocess
from pathlib import Path
manifest = json.loads(Path('lake-manifest.json').read_text())
for package in manifest['packages']:
    path = Path(manifest['packagesDir']) / package['name']
    rev = subprocess.check_output(['git','-C',str(path),'rev-parse','HEAD'], text=True).strip()
    if rev != package['rev']:
        raise ValueError(f'Pinned revision mismatch for {package["name"]}')
PY

# Order all local imports before their consumers. This also serializes a cold
# build of the conference-matrix and finite-field dependencies.
python3 - > "$work/modules" <<'PY_ORDER'
import re
from pathlib import Path

seen = set()
def visit(module):
    if module in seen:
        return
    seen.add(module)
    path = Path(*module.split('.')).with_suffix('.lean')
    for child in re.findall(r'^(?:public )?import (Conjectures[.][^\s]+)', path.read_text(), re.M):
        visit(child)
    print(module)

visit('Conjectures.NearHadamardSharp')
PY_ORDER
while IFS= read -r mod; do
    echo "Building $mod"
    heavy lake -q build "$mod"
done < "$work/modules"
cat > "$work/Axioms.lean" <<'LEAN'
import Conjectures.NearHadamardSharp
example : NearHadamard.Optimal.SharpLowerBounds := NearHadamard.Optimal.sharpLowerBounds
#print axioms NearHadamard.Optimal.sharpLowerBounds
#print axioms NearHadamard.Optimal.nonordinaryFive
LEAN
heavy lake env lean "$work/Axioms.lean" | tee "$work/axioms.txt"
python3 - "$work/axioms.txt" <<'PY'
import re, sys
from pathlib import Path
rows = re.findall(r"'([^']+)' depends on axioms:\s*\[([^\]]*)\]", Path(sys.argv[1]).read_text())
expected = {'NearHadamard.Optimal.'+s for s in ('sharpLowerBounds','nonordinaryFive')}
if {name for name, _ in rows} != expected or any(
        set(a.split(', ')) - {'propext','Classical.choice','Quot.sound'} for _, a in rows):
    raise ValueError('Axiom audit failed')
PY
if lake env sh -c 'command -v lean4checker >/dev/null'; then
    heavy lake env lean4checker Conjectures.NearHadamardSharp
fi
# A prefix runs its entire subtree. Separate leaf invocations cap live environments.
for file in Conjectures/NearHadamardSharp/Orders/*.lean Conjectures/NearHadamardSharp/*.lean; do
    mod=${file%.lean}
    heavy lake env leanchecker -v "${mod//\//.}"
done
echo 'The six sharp uniform normalized determinant bounds passed the kernel and exact arithmetic replays.'
