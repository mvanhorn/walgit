#!/usr/bin/env bash
# Classify only this invocation. An expected error alongside another error fails.
set -euo pipefail
[[ $# -eq 3 ]] || exit 2
status="$1" expected="$2" log="$3"
[[ -f "$log" ]] || exit 1
# Both successful enumeration and counterexamples must have a complete footer.
rg -q '^Finished in .+ at \(.+\)$' "$log" || exit 1
rg -q '^[0-9,]+ states generated, [0-9,]+ distinct states found, [0-9,]+ states left on queue\.$' "$log" || exit 1
case "$expected" in
  pass)
    [[ "$status" == 0 ]] &&
      rg -Fqx 'Model checking completed. No error has been found.' "$log" &&
      rg -q '^[0-9,]+ states generated, [0-9,]+ distinct states found, 0 states left on queue\.$' "$log" &&
      ! rg -q '^Error:' "$log"
    ;;
  *)
    if [[ "$expected" == temporal:* ]]; then
      [[ "$status" == 13 ]] || exit 1
      verdict="Error: Temporal property ${expected#temporal:} was violated."
      trace='Error: The following behavior constitutes a counter-example:'
    else
      [[ "$status" == 12 ]] || exit 1
      verdict="Error: Invariant $expected is violated."
      trace='Error: The behavior up to this point is:'
    fi
    # TLC prefixes the trace heading with Error too; it is the only permitted
    # companion. Duplicate verdicts also reject concatenated or stale logs.
    awk -v verdict="$verdict" -v trace="$trace" '
      /^Error:/ {
        if ($0 == verdict) verdicts++
        else if ($0 == trace) traces++
        else bad = 1
      }
      END { exit !(verdicts == 1 && traces == 1 && !bad) }
    ' "$log" && rg -q '^State 1: ' "$log"
    ;;
esac
