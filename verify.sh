#!/usr/bin/env bash
# Replay every result, or only the named ones, strictly one at a time.
# Usage: ./verify.sh [slug ...]      Logs go to verify-logs/<slug>.log.
set -uo pipefail
root=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd)
cd "$root"

python3 scripts/collection.py check || { echo "Structural check failed; not replaying."; exit 1; }

if (($#)); then slugs=("$@"); else mapfile -t slugs < <(python3 scripts/collection.py slugs); fi
mkdir -p verify-logs
timer=()
if /usr/bin/time -v true >/dev/null 2>&1; then timer=(/usr/bin/time -v); fi

failed=0
summary=()
for slug in "${slugs[@]}"; do
    script="results/$slug/verify.sh"
    [[ -x $script ]] || { echo "No such result: $slug"; failed=1; continue; }
    log="verify-logs/$slug.log"
    echo "==> $slug"
    start=$SECONDS
    if "${timer[@]}" "$script" >"$log" 2>&1; then verdict=PASS; else verdict=FAIL; failed=1; fi
    elapsed=$((SECONDS - start))
    rss=$(grep -m1 'Maximum resident set size' "$log" 2>/dev/null | awk '{printf "%.1f GiB", $NF/1048576}')
    # The headline lines are the last lines the entry's script prints before the timer report.
    grep -v -e '^\s*\(Command being timed\|User time\|System time\|Percent of CPU\|Elapsed\|Average\|Maximum resident\|Major\|Minor\|Voluntary\|Involuntary\|Swaps\|File system\|Socket\|Signals\|Page size\|Exit status\)' "$log" | tail -n 2 | sed 's/^/    /'
    summary+=("$(printf '%-4s  %-48s %5ss  %s' "$verdict" "$slug" "$elapsed" "${rss:-}")")
done

echo
printf '%s\n' "${summary[@]}"
((failed)) && echo "At least one replay failed. See verify-logs/." || echo "All replays passed."
exit "$failed"
