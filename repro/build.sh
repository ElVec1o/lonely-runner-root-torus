#!/bin/bash
# build.sh : build (or validate the plan for) the 7 project modules of the root-torus note, ONE AT A TIME, in the order of MANIFEST.tsv.
#
#   NEVER run a bare `lake build` for this project: it starts one lean worker per core, each worker on a heavy module reaches
#   9 GB, and the machine runs out of memory.  This script builds exactly one module per `lake build LRSpectrumFull.<Module>`
#   call, after all of that module's project imports have been built (so lake has nothing else to build), with one lean process
#   at a time.
#
# MODES (exactly one)
#   --plan     list the build order and VALIDATE it, no lake, no lean: manifest readable, every source present, sha256 equal to
#              MANIFEST.tsv, order topological, lean-toolchain and Mathlib revision equal to the pins, free disk, expected cost.
#   --status   --plan, then for every selected module `lake build --no-build LRSpectrumFull.<M>` (a lake process, no lean worker
#              unless lake itself decides something is stale, which --no-build forbids): reports UP-TO-DATE or NEEDS-BUILD.
#   --run      build the selected modules (resumable; see below).
# OPTIONS
#   --from N --to N      select manifest indices N..M (default 1..all)
#   --only A,B,...       select modules by name; a name may omit the leading `LRSpectrumFull.` (e.g. ObsPsiBound)
#   --force              --run: build even if results.tsv already has an OK row with the same source hash
#   --results FILE       results table (default logs/build_results.tsv); rows: module sha256 status try wall_s peak_MB
#   --retries N          how often a guard-killed build (exit 137, no error line) is retried (default 6)
#   --retry-wait S       seconds to wait before a retry (default 600)
# ENVIRONMENT (defaults in brackets)
#   LEAN_DIR     the Lean project root (the lean/ directory of this repository)                     [$HERE/../lean]
#   CEILING_MB   memory ceiling handed to the wrapper               [12000]  (watchdog kills the process tree at 90 %)
#   WRAPPER      memory/disk watchdog launcher: `WRAPPER CEILING LOGDIR NAME cmd...`; must append `rss=NNNMB` samples to
#                LOGDIR/NAME.watch.  [none: plain run, no watchdog (not recommended)]
#   GATE_RESERVE_MB / GATE_LIMIT_MB   memory gate: wait while (RSS of all lean processes on the machine + RESERVE) > LIMIT
#                [6500 / 14500].  RESERVE is what the next module needs beyond baseline; the heavy line modules peak at 9 GB.
#   LOCK         atomic lock directory (mkdir)                       [./logs/build.lock]
#   DISK_FLOOR_GB  abort below this many free GB                     [3]
#
# RESUMABLE: after each module one row goes to the results table.  A second --run skips every module whose row says OK with
# the same sha256 (unless --force).  Kill the script (Ctrl-C), start it again: it continues.
# GUARD-AWARE: an external memory guard or the OS out-of-memory killer may kill a build; that shows as
# `exit 137` / "code 137" and no other error line.  The module is then retried after RETRY_WAIT seconds, up to RETRIES times.
# ABORTS on a real error (an `error:` line that is not an exit-137 line, or a kill by our own watchdog): later modules would
# import an unbuilt module, and lake would then rebuild the unbuilt imports in parallel (a process tree of 29.6 GB was observed once).
# EXIT: 0 = all selected modules done (or plan valid); 1 = real error / abort; 2 = plan validation failed; 3 = disk / lock problem.

HERE=$(cd "$(dirname "$0")" && pwd)
LEAN_DIR=${LEAN_DIR:-$HERE/../lean}
CEILING_MB=${CEILING_MB:-12000}
GATE_RESERVE_MB=${GATE_RESERVE_MB:-6500}
GATE_LIMIT_MB=${GATE_LIMIT_MB:-14500}
DISK_FLOOR_GB=${DISK_FLOOR_GB:-3}
if [ -z "${WRAPPER+x}" ]; then WRAPPER=""; fi
if [ -z "${LOCK+x}" ]; then LOCK=$HERE/logs/build.lock; fi
PIN_TOOLCHAIN="leanprover/lean4:v4.30.0"
PIN_MATHLIB_REV="c5ea00351c28e24afc9f0f84379aa41082b1188f"
MANIFEST=${MANIFEST:-$HERE/MANIFEST.tsv}
EXPECTED=${EXPECTED:-$HERE/EXPECTED.tsv}
LOGDIR=$HERE/logs/build
RESULTS=$HERE/logs/build_results.tsv
MODE=""; FROM=1; TO=100000; ONLY=""; FORCE=0; RETRIES=6; RETRY_WAIT=600

while [ $# -gt 0 ]; do
  case "$1" in
    --plan|--status|--run) MODE=${1#--} ;;
    --from) FROM=$2; shift ;;
    --to) TO=$2; shift ;;
    --only) ONLY=$2; shift ;;
    --force) FORCE=1 ;;
    --results) RESULTS=$2; shift ;;
    --retries) RETRIES=$2; shift ;;
    --retry-wait) RETRY_WAIT=$2; shift ;;
    -h|--help) sed -n '2,45p' "$0"; exit 0 ;;
    *) echo "unknown option $1 (see --help)" >&2; exit 2 ;;
  esac
  shift
done
[ -n "$MODE" ] || { echo "give one of --plan --status --run (see --help)" >&2; exit 2; }
mkdir -p "$LOGDIR" "$(dirname "$RESULTS")"

# ---- read the manifest into parallel arrays (index = manifest idx) -------------------------------------------------------
[ -f "$MANIFEST" ] || { echo "MANIFEST.tsv not found: $MANIFEST" >&2; exit 2; }
N=0
while IFS=$'\t' read -r idx mod path sha bytes lines kind imps; do
  [ "$idx" = "idx" ] && continue
  N=$((N+1))
  MOD[$idx]=$mod; PATH_[$idx]=$path; SHA[$idx]=$sha; KIND[$idx]=$kind; IMPS[$idx]=$imps
done < "$MANIFEST"
echo "manifest: $N modules ($MANIFEST)"

# selected indices
SEL=""
want() {   # does name $1 match the --only list?
  local m=$1 s w
  for w in $(echo "$ONLY" | tr ',' ' '); do
    case "$w" in LRSpectrumFull.*) s=$w ;; *) s=LRSpectrumFull.$w ;; esac
    [ "$s" = "$m" ] && return 0
  done
  return 1
}
i=1
while [ $i -le $N ]; do
  if [ $i -ge $FROM ] && [ $i -le $TO ]; then
    if [ -z "$ONLY" ] || want "${MOD[$i]}"; then SEL="$SEL $i"; fi
  fi
  i=$((i+1))
done
NSEL=$(echo $SEL | wc -w | tr -d ' ')
[ "$NSEL" -gt 0 ] || { echo "no module selected" >&2; exit 2; }
if [ -n "$ONLY" ]; then
  for w in $(echo "$ONLY" | tr ',' ' '); do
    f=0; for i in $SEL; do case "$w" in LRSpectrumFull.*) s=$w ;; *) s=LRSpectrumFull.$w ;; esac; [ "${MOD[$i]}" = "$s" ] && f=1; done
    [ $f = 1 ] || { echo "--only: $w is not in the manifest (or outside --from/--to)" >&2; exit 2; }
  done
fi

free_gb() { df -Pk "$LEAN_DIR" | awk 'NR==2{print int($4/1048576)}'; }
leanrss() { ps -axo rss=,command= | grep -E 'bin/lean ' | grep -v grep | awk '{s+=$1} END{print int(s/1024)}'; }

# ---- PLAN: validate everything that needs no lake ------------------------------------------------------------------------
BAD=0
echo "---- plan validation ----"
if [ "$(cat "$LEAN_DIR/lean-toolchain" 2>/dev/null)" = "$PIN_TOOLCHAIN" ]; then echo "ok   lean-toolchain = $PIN_TOOLCHAIN"; else echo "FAIL lean-toolchain is '$(cat "$LEAN_DIR/lean-toolchain" 2>/dev/null)', expected $PIN_TOOLCHAIN"; BAD=1; fi
if grep -q "\"rev\": \"$PIN_MATHLIB_REV\"" "$LEAN_DIR/lake-manifest.json" 2>/dev/null; then echo "ok   lake-manifest.json pins mathlib $PIN_MATHLIB_REV"; else echo "FAIL lake-manifest.json does not pin mathlib $PIN_MATHLIB_REV"; BAD=1; fi
SUMW=0; MAXP=0; NMIS=0; NHASH=0; NORD=0
printf '%-4s %-44s %-9s %7s %8s\n' idx module kind wall_s peak_MB
for i in $SEL; do
  f="$LEAN_DIR/${PATH_[$i]}"
  [ -f "$f" ] || { echo "FAIL missing source ${PATH_[$i]}"; NMIS=$((NMIS+1)); BAD=1; continue; }
  h=$(shasum -a 256 "$f" | cut -d' ' -f1)
  [ "$h" = "${SHA[$i]}" ] || { echo "FAIL sha256 differs: ${MOD[$i]}"; NHASH=$((NHASH+1)); BAD=1; }
  for d in $(echo "${IMPS[$i]}" | tr ',' ' '); do
    ok=0; j=1; while [ $j -lt $i ]; do [ "${MOD[$j]}" = "$d" ] && ok=1; j=$((j+1)); done
    [ $ok = 1 ] || { echo "FAIL order: ${MOD[$i]} imports $d which is not earlier in the manifest"; NORD=$((NORD+1)); BAD=1; }
  done
  e=$(grep -F "${MOD[$i]}	" "$EXPECTED" 2>/dev/null | head -1)
  w=$(echo "$e" | cut -f2); p=$(echo "$e" | cut -f3)
  case "$w" in ''|NA) w=NA ;; *) SUMW=$((SUMW+w)) ;; esac
  case "$p" in ''|NA) p=NA ;; *) [ "$p" -gt "$MAXP" ] && MAXP=$p ;; esac
  printf '%-4s %-44s %-9s %7s %8s\n' "$i" "${MOD[$i]#LRSpectrumFull.}" "${KIND[$i]}" "$w" "$p"
done
echo "selected $NSEL modules; missing sources $NMIS; sha256 mismatches $NHASH; order violations $NORD"
echo "expected (observed in earlier clean rebuilds): sum wall $SUMW s = $((SUMW/3600)) h $(((SUMW%3600)/60)) min; max peak $MAXP MB"
DG=$(free_gb); if [ "$DG" -ge "$DISK_FLOOR_GB" ]; then echo "ok   free disk ${DG} GB >= floor ${DISK_FLOOR_GB} GB"; else echo "FAIL free disk ${DG} GB < floor ${DISK_FLOOR_GB} GB"; BAD=1; fi
echo "machine: lean RSS now $(leanrss) MB (gate: wait while RSS + $GATE_RESERVE_MB > $GATE_LIMIT_MB); wrapper='${WRAPPER:-none}'; lock=$LOCK; ceiling=$CEILING_MB MB"
if [ $BAD != 0 ]; then echo "PLAN INVALID"; exit 2; fi
echo "PLAN VALID"
[ "$MODE" = plan ] && exit 0

# ---- STATUS: is each module up to date according to lake? ------------------------------------------------------------------
cd "$LEAN_DIR" || exit 2
if [ "$MODE" = status ]; then
  echo "---- lake status (one lake build --no-build per module, sequential) ----"
  NUP=0; NNB=0
  for i in $SEL; do
    if lake build --no-build "${MOD[$i]}" > "$LOGDIR/status_$(echo "${MOD[$i]}" | tr '.' '_').out" 2>&1; then echo "UP-TO-DATE  ${MOD[$i]}"; NUP=$((NUP+1)); else echo "NEEDS-BUILD ${MOD[$i]}"; NNB=$((NNB+1)); fi
  done
  echo "up-to-date $NUP, needs build $NNB"
  exit 0
fi

# ---- RUN ---------------------------------------------------------------------------------------------------------------------
[ -f "$RESULTS" ] || printf 'module\tsha256\tstatus\ttry\twall_s\tpeak_MB\n' > "$RESULTS"
HELD=0
release() { if [ $HELD = 1 ]; then rm -f "$LOCK/owner" 2>/dev/null; rmdir "$LOCK" 2>/dev/null; HELD=0; fi; }
kill_tree() {  # kill a process and all its descendants (only ours: started by this script)
  local root=$1
  local all=$(ps -axo pid=,ppid= | awk -v r=$root '{pp[$1]=$2} END{t[r]=1; do{c=0; for(p in pp) if(!(p in t) && (pp[p] in t)){t[p]=1;c=1}}while(c); for(p in t) printf "%s ", p}')
  [ -n "$all" ] && kill $all 2>/dev/null
}
WPID=""
on_signal() { echo "signal: stopping our own build tree and releasing the lock"; [ -n "$WPID" ] && kill_tree "$WPID"; release; exit 1; }
trap on_signal INT TERM
trap release EXIT
is_done() {   # OK row with the same hash for module $1 hash $2
  awk -F'\t' -v m="$1" -v h="$2" '$1==m && $2==h && $3=="OK"{f=1} END{exit f?0:1}' "$RESULTS"
}
DONE=" "
NOK=0; NSKIP=0
for i in $SEL; do
  m=${MOD[$i]}; h=${SHA[$i]}; nm=$(echo "$m" | tr '.' '_')
  if [ $FORCE = 0 ] && is_done "$m" "$h"; then echo "skip (OK row in results): $m"; DONE="$DONE$m "; NSKIP=$((NSKIP+1)); continue; fi
  # all project imports must be built already; lake would otherwise build them too, possibly in parallel
  for d in $(echo "${IMPS[$i]}" | tr ',' ' '); do
    case "$DONE" in *" $d "*) continue ;; esac
    if lake build --no-build "$d" > "$LOGDIR/imp_check.out" 2>&1; then DONE="$DONE$d "; else
      echo "ABORT: import $d of $m is not built (run the manifest in order, or build $d first)"; exit 1; fi
  done
  try=0
  while :; do
    try=$((try+1))
    DG=$(free_gb); [ "$DG" -ge "$DISK_FLOOR_GB" ] || { echo "ABORT: free disk ${DG} GB < floor ${DISK_FLOOR_GB} GB"; exit 3; }
    # memory gate (heavy module needs RESERVE beyond what other lean processes hold)
    while [ $(( $(leanrss) + GATE_RESERVE_MB )) -gt "$GATE_LIMIT_MB" ]; do echo "$(date +%T) gate: lean RSS $(leanrss) MB + $GATE_RESERVE_MB > $GATE_LIMIT_MB, waiting before $m"; sleep 30; done
    # build lock (atomic mkdir): one lean process at a time
    while ! mkdir "$LOCK" 2>/dev/null; do echo "$(date +%T) lock $LOCK held by '$(cat "$LOCK/owner" 2>/dev/null)', waiting"; sleep 20; done
    HELD=1; echo "root-torus repro build.sh pid $$ building $m" > "$LOCK/owner"
    rm -f "$LOGDIR/$nm.out" "$LOGDIR/$nm.err" "$LOGDIR/$nm.watch"
    S=$(date +%s)
    echo "$(date +%T) build $i/$N $m (try $try)"
    if [ -n "$WRAPPER" ]; then
      $WRAPPER "$CEILING_MB" "$LOGDIR" "$nm" bash -c "cd '$LEAN_DIR' && lake build $m" &
    else
      ( bash -c "cd '$LEAN_DIR' && lake build $m" > "$LOGDIR/$nm.out" 2> "$LOGDIR/$nm.err" ) &
    fi
    WPID=$!; wait $WPID; WPID=""
    release
    W=$(( $(date +%s) - S ))
    OK=$(grep -c "Build completed successfully" "$LOGDIR/$nm.out" 2>/dev/null)
    PEAK=$(grep -o 'rss=[0-9]*MB' "$LOGDIR/$nm.watch" 2>/dev/null | sed 's/rss=//;s/MB//' | sort -n | tail -1)
    [ -n "$PEAK" ] || PEAK=NA
    if [ "$OK" = "1" ] && ! grep -q "WATCHDOG KILL" "$LOGDIR/$nm.watch" 2>/dev/null; then
      printf '%s\t%s\tOK\ttry%s\t%s\t%s\n' "$m" "$h" "$try" "$W" "$PEAK" >> "$RESULTS"
      echo "     OK  ${W}s  peak ${PEAK} MB"; DONE="$DONE$m "; NOK=$((NOK+1)); break
    fi
    printf '%s\t%s\tFAIL\ttry%s\t%s\t%s\n' "$m" "$h" "$try" "$W" "$PEAK" >> "$RESULTS"
    if grep -q "WATCHDOG KILL" "$LOGDIR/$nm.watch" 2>/dev/null; then echo "ABORT: our own watchdog killed $m (peak ${PEAK} MB > 90% of $CEILING_MB MB); not retried blindly"; exit 1; fi
    if grep "error:" "$LOGDIR/$nm.out" "$LOGDIR/$nm.err" 2>/dev/null | grep -qv "code 137"; then
      echo "ABORT: real error in $m (log $LOGDIR/$nm.out):"; grep "error:" "$LOGDIR/$nm.out" "$LOGDIR/$nm.err" | grep -v "code 137" | head -20; exit 1; fi
    # no real error line: external kill (guard / OOM killer), exit 137
    if [ "$try" -ge "$RETRIES" ]; then echo "ABORT: $m failed $try times without a real error (external kills); see $LOGDIR/$nm.*"; exit 1; fi
    echo "     guard kill suspected (no error line, exit 137?) at try $try; retry in ${RETRY_WAIT}s"
    sleep "$RETRY_WAIT"
  done
done
echo "DONE: built $NOK, skipped $NSKIP (results: $RESULTS)"
exit 0
