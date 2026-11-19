#!/bin/bash
# check_axioms.sh : print the axioms of the headline theorems and judge the printout.  BUILDS NOTHING (no `lake build`).
# It elaborates check_axioms.lean with `lake env lean`, which only reads the existing .olean files of the 7 modules
# (so the modules must have been built: see build.sh), under the same lock / memory gate / watchdog wrapper as build.sh.
#
# Verdict rules (a script that prints PASS must be checked on what it counts):
#   * the number of `depends on axioms` lines must equal the number of `#print axioms` commands in the file (nothing silently lost),
#   * every real theorem's axiom set is exactly {propext, Classical.choice, Quot.sound} (or empty),
#   * the two planted controls print sorryAx (the instrument can see a sorry, directly and transitively),
#   * the Lean output contains no `error`.
# Output: logs/check_axioms.raw (raw Lean output; logs/check_axioms.out/.err are the wrapper files), logs/check_axioms.verdict (this script's judgement).
# Exit 0 = PASS, 1 = FAIL, 2 = could not run.
HERE=$(cd "$(dirname "$0")" && pwd)
LEAN_DIR=${LEAN_DIR:-$HERE/../lean}
CEILING_MB=${CEILING_MB:-12000}
if [ -z "${WRAPPER+x}" ]; then WRAPPER=""; fi
if [ -z "${LOCK+x}" ]; then LOCK=$HERE/logs/build.lock; fi
GATE_RESERVE_MB=${GATE_RESERVE_MB:-6500}; GATE_LIMIT_MB=${GATE_LIMIT_MB:-14500}
LOGDIR=$HERE/logs; mkdir -p "$LOGDIR"
RAW=$LOGDIR/check_axioms.raw; NORM=$LOGDIR/check_axioms.norm; VERD=$LOGDIR/check_axioms.verdict
NAME=check_axioms
leanrss() { ps -axo rss=,command= | grep -E 'bin/lean ' | grep -v grep | awk '{s+=$1} END{print int(s/1024)}'; }
NEXPECT=$(grep -c '^#print axioms' "$HERE/check_axioms.lean")
while [ $(( $(leanrss) + GATE_RESERVE_MB )) -gt "$GATE_LIMIT_MB" ]; do echo "gate: lean RSS $(leanrss) MB, waiting"; sleep 30; done
while ! mkdir "$LOCK" 2>/dev/null; do echo "lock held by '$(cat "$LOCK/owner" 2>/dev/null)', waiting"; sleep 20; done
echo "root-torus repro check_axioms.sh pid $$" > "$LOCK/owner"
trap 'rm -f "$LOCK/owner"; rmdir "$LOCK" 2>/dev/null' EXIT
rm -f "$LOGDIR/$NAME.out" "$LOGDIR/$NAME.err" "$LOGDIR/$NAME.watch"
if [ -n "$WRAPPER" ]; then
  $WRAPPER "$CEILING_MB" "$LOGDIR" "$NAME" bash -c "cd '$LEAN_DIR' && lake env lean '$HERE/check_axioms.lean'"
else
  ( bash -c "cd '$LEAN_DIR' && lake env lean '$HERE/check_axioms.lean'" > "$LOGDIR/$NAME.out" 2> "$LOGDIR/$NAME.err" )
fi
cat "$LOGDIR/$NAME.out" "$LOGDIR/$NAME.err" > "$RAW" 2>/dev/null
awk '/^ / { printf "%s", $0; next } NR > 1 { printf "\n" } { printf "%s", $0 } END { printf "\n" }' "$RAW" > "$NORM"   # join wrapped continuation lines (long names make Lean wrap the axiom list)
NGOT=$(grep -c -E "depends on axioms|does not depend on any axioms" "$NORM")
STD=$(grep -E "depends on axioms" "$NORM" | grep -v sorryAx | grep -c -E "\[propext, Classical.choice, Quot.sound\]")
NSORRY=$(grep -E "depends on axioms" "$NORM" | grep -c sorryAx)
NNONE=$(grep -c "does not depend on any axioms" "$NORM")
NOTHER=$(grep -E "depends on axioms" "$NORM" | grep -v sorryAx | grep -v -c -E "\[propext, Classical.choice, Quot.sound\]")
NERR=$(grep -c -i "error" "$NORM")
CTL1=$(grep -c "check_axioms_planted_sorry' depends on axioms.*sorryAx" "$NORM")
CTL2=$(grep -c "check_axioms_planted_sorry_user' depends on axioms.*sorryAx" "$NORM")
{
  echo "expected #print axioms lines : $NEXPECT"
  echo "printed axiom lines          : $NGOT"
  echo "exactly the 3 standard axioms: $STD   (no axioms at all: $NNONE)"
  echo "other axiom sets (not sorry) : $NOTHER"
  echo "lines with sorryAx           : $NSORRY (must be exactly the 2 planted controls)"
  echo "planted control direct / transitive : $CTL1 / $CTL2 (must be 1 / 1)"
  echo "lines containing 'error'     : $NERR"
} > "$VERD"
if [ "$NGOT" = "$NEXPECT" ] && [ "$NOTHER" = 0 ] && [ "$NSORRY" = 2 ] && [ "$CTL1" = 1 ] && [ "$CTL2" = 1 ] && [ "$NERR" = 0 ] && [ $((STD+NNONE+NSORRY)) = "$NEXPECT" ]; then
  echo "VERDICT: PASS" >> "$VERD"; cat "$VERD"; grep -E "depends on axioms|does not depend" "$NORM"; exit 0
else
  echo "VERDICT: FAIL (see $RAW)" >> "$VERD"; cat "$VERD"; exit 1
fi
