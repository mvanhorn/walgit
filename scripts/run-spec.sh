#!/usr/bin/env bash
# Exhaustive bounded TLC, not simulation. Each invocation has its own log and
# metadir; a different arm's expected error must never satisfy a negative control.
#
# Each case owns its config, log and state directory. Bound the JVM pool
# explicitly: the default is two jobs, two workers and 2 GiB heap per job.
set -euo pipefail
root="$(cd "$(dirname "$0")/.." && pwd)"
cd "$root"

# --case: one pooled TLC arm, self-exec'd by the pool below.
# Env from the parent: SPEC_JAR SPEC_LOGS SPEC_WORK SPEC_WORKERS SPEC_HEAP.
# Writes $SPEC_LOGS/<name>.result (the arm's summary-file fragment) and exits
# nonzero on an unexpected verdict so xargs propagates failure.
if [[ "${1:-}" == "--case" ]]; then
  name="$2" module="$3" config="$4" expected="$5"
  log="$SPEC_LOGS/$name.log" meta="$SPEC_WORK/$name" result="$SPEC_LOGS/$name.result"
  mkdir -p "$meta"
  effective="$SPEC_LOGS/$name.cfg"
  [[ "$config" == "$effective" ]] || cp "$config" "$effective"
  config="$effective"
  status=0
  timeout "${WALGIT_TLC_TIMEOUT:-600}" java -Xmx"$SPEC_HEAP" -XX:+UseParallelGC -XX:ActiveProcessorCount="$SPEC_WORKERS" \
    -DTLA-Library="$root/docs/spec" -cp "$SPEC_JAR" tlc2.TLC \
    -noGenerateSpecTE -metadir "$meta" -workers "$SPEC_WORKERS" -fp 0 \
    -config "$config" "$module" > "$log" 2>&1 || status=$?
  if scripts/check-tlc-result.sh "$status" "$expected" "$log"; then
    {
      printf '== %s (expect %s)\n' "$name" "$expected"
      printf 'PASS %s (exit %s)\n' "$name" "$status"
      rg 'states generated,|depth of the complete|Finished in' "$log" || true
    } > "$result"
    echo "PASS $name"
    rm -rf "$meta"
    exit 0
  fi
  {
    printf '== %s (expect %s)\n' "$name" "$expected"
    printf 'FAIL %s: exit %s, expected %s; %s\n' "$name" "$status" "$expected" "$log"
  } > "$result"
  echo "FAIL $name ($log)"
  exit 1
fi

mode="${1:-fast}"
case "$mode" in
  fast|fragments) default_workers=2; default_heap=2g ;;
  full) default_workers=8; default_heap=8g ;;
  *) echo "usage: $0 [fast|full|fragments]" >&2; exit 2 ;;
esac
workers="${WALGIT_TLC_WORKERS:-$default_workers}"
heap="${WALGIT_TLC_HEAP:-$default_heap}"
[[ "$heap" =~ ^[1-9][0-9]*[mMgG]$ ]] || { echo "WALGIT_TLC_HEAP must use m or g units" >&2; exit 2; }
[[ "$workers" =~ ^[1-9][0-9]*$ ]] || { echo 'WALGIT_TLC_WORKERS must be positive' >&2; exit 2; }
jobs="${WALGIT_TLC_JOBS:-2}"
[[ "$jobs" =~ ^[1-9][0-9]*$ ]] || { echo 'WALGIT_TLC_JOBS must be positive' >&2; exit 2; }
mkdir -p target/test-logs
logs="$(mktemp -d "$root/target/test-logs/spec-$mode-$(date +%Y%m%d-%H%M%S).XXXXXX")"
echo "log: $logs/summary.log"
: > "$logs/summary.log"
if ! scripts/test-spec-runner.sh > "$logs/runner.log" 2>&1; then
  echo "FAIL result-classifier regressions ($logs/runner.log)" | tee -a "$logs/summary.log"
  tail -60 "$logs/runner.log"
  exit 1
fi
# A malformed/empty matrix or duplicate label must not silently skip cases or
# overwrite another invocation's evidence.
awk '
  /^#/ || NF == 0 { next }
  NF != 7 || seen[$1]++ { print "invalid/duplicate TLC case at line " NR > "/dev/stderr"; exit 1 }
  { count++ }
  END { if (count == 0) exit 1 }
' docs/spec/tlc/cases.tsv
scripts/ensure-tla-tools.sh
jar="$root/target/tla2tools.jar"
work="$(mktemp -d "$root/target/tlc.XXXXXX")"
trap 'rm -rf "$work"' EXIT

export SPEC_JAR="$jar" SPEC_LOGS="$logs" SPEC_WORK="$work" SPEC_WORKERS="$workers" SPEC_HEAP="$heap"

# NUL-delimited arguments also preserve checkout paths containing whitespace.
queue="$logs/queue.txt"
: > "$queue"
order=()
enqueue() {
  printf '%s\0%s\0%s\0%s\0' "$1" "$2" "$3" "$4" >> "$queue"
  order+=("$1")
}

# TLC semantically checks every loaded module too. Keep an explicit SANY log
# for the frozen reference, even in the fragment-only developer loop.
java -cp "$jar" tla2sany.SANY docs/spec/WALContract.tla > "$logs/sany.log" 2>&1
if rg -q "\*\*\* (Errors|Parse Error)|Fatal errors|Semantic errors" "$logs/sany.log"; then
  echo "FAIL reference SANY ($logs/sany.log)" >&2
  exit 1
fi
if [[ "$mode" != fragments ]]; then
  enqueue reference-fast "$root/docs/spec/tlc/MC.tla" "$root/docs/spec/tlc/MC_fast.cfg" pass
  enqueue reference-bug "$root/docs/spec/tlc/MC_bug.tla" "$root/docs/spec/tlc/MC_bug.cfg" HistPreconds
fi

while read -r name module config scenario fault spec expected; do
  [[ -z "$name" || "$name" == \#* ]] && continue
  cfg="$logs/$name.cfg"
  dir="$root/docs/spec/scratch"
  [[ -f "$dir/$module.tla" ]] || dir="$root/docs/spec/tlc"
  awk -v scenario="$scenario" -v fault="$fault" -v spec="$spec" -v expected="$expected" '
    /^SPECIFICATION / && spec != "-" { print "SPECIFICATION " spec; next }
    /^  Scenario = / && scenario != "-" { print "  Scenario = \"" scenario "\""; next }
    /^  Broken = / && scenario != "-" { print "  Broken = " (scenario ~ /^broken/ ? "TRUE" : "FALSE"); next }
    /^  Mode = / && scenario != "-" { print "  Mode = \"" (scenario ~ /prune$/ ? "prune" : "conserve") "\""; next }
    /^  Fault = / && fault != "-" { print "  Fault = \"" fault "\""; next }
    /^(INVARIANTS?|PROPERTIES|PROPERTY)( |$)/ && expected != "pass" {
      if (expected ~ /^temporal:/) print "PROPERTY " substr(expected, 10)
      else print "INVARIANT " expected
      exit
    }
    { print }
    END {
      if ((spec == "LiveSpec" || spec == "HealthySpec") && expected == "pass")
        print "PROPERTIES Terminates TransportSettles"
      if (spec == "HealthySpec" && expected == "pass") print "PROPERTY EventuallyCommitted"
    }
  ' "$dir/$config.cfg" > "$cfg"
  enqueue "$name" "$dir/$module.tla" "$cfg" "$expected"
done < docs/spec/tlc/cases.tsv

# Fan the arms out. Unlike the serial loop this does not stop at the first
# failure: every arm runs, every verdict is recorded, and the exit is the sum —
# partial evidence beats a truncated matrix.
pool_status=0
xargs -0 -P "$jobs" -n 4 "$0" --case < "$queue" || pool_status=$?

failures=0
for name in "${order[@]}"; do
  if [[ ! -f "$logs/$name.result" ]]; then
    printf 'FAIL %s: no result written (crashed arm?); %s\n' "$name" "$logs/$name.log" | tee -a "$logs/summary.log"
    failures=$((failures + 1))
    continue
  fi
  cat "$logs/$name.result" >> "$logs/summary.log"
  if rg -q '^FAIL ' "$logs/$name.result"; then
    failures=$((failures + 1))
    tail -60 "$logs/$name.log"
  fi
done

# spec-full's reference arms enumerate big state spaces with -workers=8 each;
# running them concurrently would only divide the same cores. Keep them serial.
if [[ "$mode" == full && "$failures" -eq 0 && "$pool_status" -eq 0 ]]; then
  for config in MC MC_notrim MC_live; do
    arm_status=0
    "$0" --case "$config" "$root/docs/spec/tlc/MC.tla" "$root/docs/spec/tlc/$config.cfg" pass || arm_status=$?
    cat "$logs/$config.result" >> "$logs/summary.log" 2>/dev/null || true
    if [[ "$arm_status" -ne 0 ]]; then
      failures=$((failures + 1))
      tail -60 "$logs/$config.log"
      break
    fi
  done
fi

if [[ "$failures" -ne 0 || "$pool_status" -ne 0 ]]; then
  printf 'spec-%s: %s failed arm(s); evidence in %s\n' "$mode" "$failures" "$logs" | tee -a "$logs/summary.log"
  exit 1
fi
printf 'spec-%s: all required passes, mutations and witnesses verified (%s)\n' "$mode" "$logs" | tee -a "$logs/summary.log"
