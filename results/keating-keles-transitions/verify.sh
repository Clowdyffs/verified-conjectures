#!/usr/bin/env bash
set -euo pipefail
here=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd)
cd "$here/../../lean"
export LEAN_NUM_THREADS=1
# Estimated peak child RSS is 4 GiB with this toolchain and the dependency cache.
free -g
ps -eo comm,rss --sort=-rss | head -8
exec 9>/tmp/proofs-conjectures-heavy.lock
flock -x 9
python3 -I "$here/replay.py"
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
for pkg in manifest['packages']:
    directory = Path(manifest['packagesDir']) / pkg['name']
    rev = subprocess.check_output(['git','-C',directory,'rev-parse','HEAD'], text=True).strip()
    if rev != pkg['rev']:
        raise SystemExit(f"Dependency revision differs for {pkg['name']}")
PY
lake build Conjectures.KeatingKelesTransitions
scratch=$(mktemp -d)
trap 'rm -rf -- "$scratch"' EXIT
cat > "$scratch/Audit.lean" <<'LEAN'
import Conjectures.KeatingKelesTransitions
#print axioms HessenbergTransitions.resolution
#print axioms HessenbergTransitions.sharp_maximum
#print axioms HessenbergTransitions.all_forms
#print axioms HessenbergTransitions.no_cancellation
#print axioms HessenbergTransitions.unequal_counts
#print axioms HessenbergTransitions.even_steps_tail
#print axioms HessenbergTransitions.odd_steps_tail
#print axioms HessenbergTransitions.strip
#print axioms HessenbergTransitions.observation_five_one
LEAN
lake env lean "$scratch/Audit.lean" | tee "$scratch/axioms"
python3 - "$scratch/axioms" <<'PY'
import re
import sys
from pathlib import Path
rows = re.findall(r"'HessenbergTransitions\.([^']+)' depends on axioms:\s*\[([^\]]*)\]", Path(sys.argv[1]).read_text())
names = {'resolution','sharp_maximum','all_forms','no_cancellation','unequal_counts','even_steps_tail','odd_steps_tail','strip','observation_five_one'}
if {name for name, _ in rows} != names or any(
        set(ax.split(', ')) - {'propext','Classical.choice','Quot.sound'} for _,ax in rows):
    raise SystemExit("Axiom check failed")
PY
if lake env sh -c 'command -v lean4checker >/dev/null'; then
    lake env lean4checker Conjectures.KeatingKelesTransitions
fi
lake env leanchecker -v Conjectures.KeatingKelesTransitions
