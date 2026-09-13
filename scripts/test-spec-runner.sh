#!/usr/bin/env bash
# Hermetic classifier controls: no JVM, network, or repository mutation.
set -euo pipefail
root="$(cd "$(dirname "$0")/.." && pwd)"
work="$(mktemp -d)"; trap 'rm -rf "$work"' EXIT
check="$root/scripts/check-tlc-result.sh"
footer() {
  printf '%s\n' '21 states generated, 12 distinct states found, 0 states left on queue.' \
    'Finished in 00s at (2026-01-01 00:00:00)'
}
{ echo 'Model checking completed. No error has been found.'; footer; } > "$work/pass"
{
  echo 'Error: Invariant Expected is violated.'
  echo 'Error: The behavior up to this point is:'
  echo 'State 1: <Initial predicate>'
  footer
} > "$work/negative"
{
  echo 'Error: Temporal property Terminates was violated.'
  echo 'Error: The following behavior constitutes a counter-example:'
  echo 'State 1: <Initial predicate>'
  footer
} > "$work/temporal"
"$check" 0 pass "$work/pass"
"$check" 12 Expected "$work/negative"
"$check" 13 temporal:Terminates "$work/temporal"
reject() {
  if "$check" "$@"; then echo "classifier wrongly accepted: $*" >&2; exit 1; fi
}
reject 12 Different "$work/negative"
reject 0 Expected "$work/negative"
reject 255 Expected "$work/negative"
reject 12 pass "$work/negative"
reject 124 pass "$work/pass"
reject 0 temporal:Terminates "$work/temporal"
reject 13 temporal:OtherProperty "$work/temporal"
reject 13 Expected "$work/temporal"
reject 12 Expected "$work/pass"
for error in 'Error: Deadlock reached.' 'Error: Invariant Different is violated.' \
  'Error: Parsing failed.' 'Error: Temporal property Different was violated.'; do
  { cat "$work/negative"; echo "$error"; } > "$work/extra"
  reject 12 Expected "$work/extra"
  { cat "$work/pass"; echo "$error"; } > "$work/extra"
  reject 0 pass "$work/extra"
done
cat "$work/negative" "$work/negative" > "$work/concatenated"
reject 12 Expected "$work/concatenated"
# Neither an expected first line nor a success banner proves a complete run.
sed '/^Finished in /d' "$work/negative" > "$work/truncated"
reject 12 Expected "$work/truncated"
sed '/states generated/d' "$work/pass" > "$work/truncated"
reject 0 pass "$work/truncated"
sed 's/0 states left/1 states left/' "$work/pass" > "$work/queued"
reject 0 pass "$work/queued"
sed '/^State 1:/d' "$work/negative" > "$work/no-trace"
reject 12 Expected "$work/no-trace"
echo 'spec runner: result-classifier regressions passed'
